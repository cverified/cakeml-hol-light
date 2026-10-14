"""Translate a CakeML HOL4 script file to a HOL Light file.

  python3 -I tools/port.py <theory>

writes ml/<path>/<theory>.ml and reports what it could not do.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, overrides
hterm.NAME_MAP = overrides.NAME_MAP

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'
SRC = hol4.SRC

HEAD = '''(* ======================================================== *)
(*  %s: ported from HOL4's
    %s  *)%s
(* ======================================================== *)
'''

LIBNOTE = '''
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)'''


# HOL4 declarations that only configure its parser or its
# simplifier, and that the port does not need
IGNORE_ML = [
  r'numLib\.', r'ParseExtras\.', r'diminish_srw_ss', r'Parse\.',
  r'monadsyntax', r'temp_', r'hide ', r'export_theory',
  r'bring_to_front_overload', r'Globals\.', r'computeLib',
  r'set_grammar_ancestry', r'type_abbrev', r'overload_on',
  r'Datatype\.', r'val _ = TeX', r'remove_ovl_mapping',
]


class Porter:
  def __init__(self, db, thy):
    self.db = db
    self.thy = thy
    self.path = db.thy_of_file[thy]
    self.kind = db.kind_of_thy[thy]
    names = db.names_for(thy)
    fields, amb = db.fields_for(thy)
    self.amb = amb
    flds = {f: t for f, t in fields.items() if t}
    flds.update(overrides.FIELD_OF.get(thy, {}))
    self.ctx = hterm.Ctx(names=names, fields=flds,
                         recs=db.recs_for(thy), thy=thy,
                         accessors=overrides.ACCESSORS.get(thy, {}),
                         cons=db.cons_for(thy))
    self.abbrevs = db.abbrevs_for(thy)
    raw = db.overloads_for(thy)
    for _ in range(3):
      for nm, txt in raw.items():
        try: self.ctx.overloads[nm] = self.term(txt)
        except Exception: pass
    self.out = []
    self.warn = []

  # -- helpers ---------------------------------------------------

  def srcname(self):
    return re.sub(r'^.*/(cakeml-src|hol4-src)/', '', self.path)

  def nm(self, n):
    return self.ctx.name(n)

  def term(self, text):
    toks = hterm.tokenize(text)
    p = hterm.Parser(toks, self.ctx)
    e = p.parse()
    if p.peek().kind != 'eof':
      t = p.peek()
      raise SyntaxError(f'unparsed input at {t.pos}: {t.text!r}')
    return hterm.Printer(self.ctx).pr(e, 0)

  def typ(self, text):
    ty = hterm.parse_type_text(text)
    ty = hterm.expand_type(ty, self.abbrevs)
    return hterm.print_type(ty, self.ctx)

  # -- the blocks ------------------------------------------------

  def run(self):
    blocks = hol4.parse(self.path)
    first = True
    for b in blocks:
      try:
        self.block(b)
      except Exception as ex:
        self.warn.append(f'{b.kind} {b.name}: {ex}')
        self.out.append(f'(* PORT FAILED: {b.kind} {b.name}: {ex}\n'
                        f'{b.text}\n*)\n')
    return '\n'.join(self.out)

  def wanted(self, b):
    """of a HOL4 library theory only the needed definitions are ported"""
    if self.kind != 'lib': return True
    if b.kind == 'Datatype':
      names = []
      for ty, cons, flds in hol4.datatype_names(b.body):
        names += [ty] + cons + flds
    elif b.kind in ('Definition', 'Inductive', 'CoInductive'):
      names = dbmod.definition_names(b.body)
    elif b.kind in ('Type', 'Overload'):
      names = [b.name]
    else:
      return True
    return self.db.is_needed(self.thy, names)

  def block(self, b):
    k = b.kind
    if self.kind == 'lib' and k in ('Comment', 'ML'):
      return
    if not self.wanted(b):
      return
    if k == 'Comment':
      self.out.append(b.text)
    elif k == 'Theory':
      self.out.append(HEAD % (b.name, self.srcname(),
                              LIBNOTE if self.kind == 'lib' else ''))
    elif k == 'Ancestors':
      deps = [w for w in b.body.split()]
      needs = []
      for d in deps:
        if d in self.db.thy_of_file:
          needs.append('needs "%s";;' % self.db.mlpath_of(d))
      if needs:
        self.out.append('\n'.join(sorted(set(needs))))
      ext = [d for d in deps if d not in self.db.thy_of_file]
      if ext:
        self.out.append('(* HOL4 ancestors outside the port: %s *)'
                        % ' '.join(ext))
    elif k == 'Libs':
      pass
    elif k == 'Datatype':
      self.datatype(b)
    elif k == 'Definition':
      self.definition(b)
    elif k == 'Type':
      self.typeabbrev(b)
    elif k == 'Overload':
      self.overload(b)
    elif k in ('Inductive', 'CoInductive'):
      self.inductive(b)
    elif k in ('Theorem', 'Triviality'):
      pass
    elif k == 'ML':
      if any(re.search(pat, b.text) for pat in IGNORE_ML):
        return
      self.warn.append('ML code skipped: ' + b.text.strip()[:60])
      self.out.append('(* HOL4 ML code, not ported:\n' + b.text + '\n*)')
    else:
      self.warn.append('unknown block ' + k)

  # -- datatypes -------------------------------------------------

  def datatype(self, b):
    specs = hol4.split_top(hol4.strip_comments(b.body), ';')
    parts = []
    for part in specs:
      if not part.strip(): continue
      m = re.match(r"\s*([A-Za-z][A-Za-z0-9_']*)\s*=\s*(.*)$", part, re.S)
      if not m: raise SyntaxError('datatype: ' + part[:40])
      ty, rhs = m.group(1), m.group(2).strip()
      if rhs.startswith('<|'):
        self.record(ty, rhs)
        continue
      cons = []
      for alt in hol4.split_top(rhs, '|'):
        alt = alt.strip()
        if not alt: continue
        toks = hterm.tokenize(alt)
        cname = toks[0].text
        tp = hterm.TypeParser(toks[1:-1])
        argtys = []
        while tp.i < len(tp.toks):
          argtys.append(tp.parse_atom())
        cons.append((cname, argtys))
      parts.append((ty, cons))
    if not parts: return
    spec = ';\n   '.join(
      '%s = %s' % (self.nm(ty),
                   ' | '.join(
                     ' '.join([self.nm(c)] +
                              ['(%s)' % self.typ_ast(a) for a in args])
                     for c, args in cons))
      for ty, cons in parts)
    names = [self.nm(ty) for ty, _ in parts]
    lhs = ','.join('%s_INDUCT' % n for n in names[:1]) + ',' + \
          ','.join('%s_RECURSION' % n for n in names[:1])
    self.out.append('let %s = define_datatype\n  "%s";;'
                    % (lhs, spec))

  def typ_ast(self, ty):
    ty = hterm.expand_type(ty, self.abbrevs)
    return hterm.print_type(ty, self.ctx)

  def record(self, ty, rhs):
    inner = rhs[2:rhs.rindex('|>')]
    flds = []
    for f in hol4.split_top(inner, ';'):
      if not f.strip(): continue
      name, tytext = f.split(':', 1)
      flds.append((name.strip(), self.typ(tytext.strip())))
    self.out.append('let %s_FIELDS = define_record "%s"\n  [%s];;'
                    % (self.nm(ty), self.nm(ty),
                       ';\n   '.join('"%s","%s"' % (f, t)
                                     for f, t in flds)))

  # -- definitions -----------------------------------------------

  def definition(self, b):
    name = b.name
    key = (self.thy, name)
    if key in overrides.REPLACE:
      self.out.append(overrides.REPLACE[key].strip())
      return
    body = b.body
    if key in overrides.MATCH_FORM or self.overlapping(body):
      term = fmt(self.match_form(body))
    else:
      term = fmt(self.term(body))
    rel = overrides.MEASURE.get(key)
    if rel is not None:
      self.out.append('(* the termination relation is not in the HOL4 '
                      'source *)\nlet %s = cake_define_wf\n  `%s`\n'
                      '  `%s`;;' % (name, rel, term))
      return
    if b.extra is None:
      self.out.append('let %s = cake_define\n  `%s`;;' % (name, term))
    else:
      rel, rest = wf_relation(b.extra)
      if rel is None:
        self.warn.append(f'{name}: no WF_REL_TAC in the Termination')
        self.out.append('(* TERMINATION: %s *)\nlet %s = cake_define\n'
                        '  `%s`;;' % (b.extra.strip(), name, term))
      else:
        self.out.append('(* HOL4 termination: %s *)\n'
                        'let %s = cake_define_wf\n  `%s`\n  `%s`;;'
                        % (' '.join(rest.split()), name,
                           fmt(self.term(rel)), term))

  # -- a definition as one clause with a match -------------------

  def overlapping(self, body):
    """do the clauses of a definition overlap, so that they rely on
       HOL4's first match semantics?"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      cls = hterm.clauses_of(hterm.Parser(toks, self.ctx).parse())
    except Exception:
      return False
    global CONS
    CONS = self.ctx.cons
    if len(cls) < 2: return False
    pats = [args for _, args, _ in cls]
    if any(len(a) != len(pats[0]) for a in pats): return False
    for i in range(len(pats)):
      for j in range(i + 1, len(pats)):
        if all(overlap(p, q) for p, q in zip(pats[i], pats[j])):
          return True
    return False

  def match_form(self, body):
    """the clauses of a definition as one clause with a match, which
       is what HOL4's first match semantics means"""
    toks = hterm.tokenize(hol4.strip_comments(body))
    e = hterm.Parser(toks, self.ctx).parse()
    cls = hterm.clauses_of(e)
    hop = cls[0][0]
    n = max(len(args) for _, args, _ in cls)
    if any(len(args) != n for _, args, _ in cls):
      raise SyntaxError('match_form: different arities')
    # the names of the arguments, from the clauses that have a
    # variable there
    names = []
    for i in range(n):
      nm = None
      for _, args, _ in cls:
        if args[i].kind == 'id' and args[i].name not in self.ctx.cons \
           and args[i].name not in names:
          nm = args[i].name; break
      if nm is None:
        nm = 'x' + str(i + 1)
        while nm in names: nm += "'"
      names.append(nm)
    pats = [i for i in range(n)
            if any(args[i].kind != 'id' or args[i].name in self.ctx.cons
                   for _, args, _ in cls)]
    pr = hterm.Printer(self.ctx)
    arms = []
    for _, args, r in cls:
      sub = {args[i].name: names[i] for i in range(n)
             if i not in pats and args[i].kind == 'id'
             and args[i].name not in self.ctx.cons}
      pat = ','.join(pr.pr(args[i], 60) for i in pats)
      if len(pats) > 1: pat = '(' + pat + ')'
      arms.append((pat, pr.pr(hterm.rename_ast(r, sub), 0)))
    scrut = ','.join(names[i] for i in pats)
    if len(pats) > 1: scrut = '(' + scrut + ')'
    head = pr.pr(hop, 0) + ' ' + ' '.join(names)
    body = '\n     | '.join('%s -> %s' % (p, b) for p, b in arms)
    return '%s =\n     match %s with\n       %s' % (head, scrut, body)

  # -- type abbreviations, overloads, inductive relations --------

  def typeabbrev(self, b):
    txt = dbmod.strip_quote(b.body)
    ty = hterm.parse_type_text(txt)
    params = hterm.type_vars_of(ty)
    if params:
      self.out.append('(* HOL4 type abbreviation (expanded in the port):'
                      '\n     %s = %s *)' % (b.name, txt))
    else:
      self.out.append('new_type_abbrev("%s",`:%s`);;'
                      % (self.nm(b.name), self.typ(txt)))

  def overload(self, b):
    txt = dbmod.strip_quote(b.body)
    self.warn.append('Overload %s' % b.name)
    self.out.append('(* HOL4 overload (expanded in the port):\n'
                    '     %s = %s *)' % (b.name, txt))

  def inductive(self, b):
    term = fmt(self.term(b.body))
    self.out.append('let %s = cake_inductive\n  `%s`;;' % (b.name, term))


CONS = set()           # the constructors in scope, set by the porter


def overlap(p, q):
  """can two patterns match the same value?"""
  while p.kind == 'paren': p = p.e
  while q.kind == 'paren': q = q.e
  if p.kind == 'typed': return overlap(p.e, q)
  if q.kind == 'typed': return overlap(p, q.e)
  if p.kind == 'id' and p.name not in CONS: return True
  if q.kind == 'id' and q.name not in CONS: return True
  if p.kind == 'id' and q.kind == 'id': return p.name == q.name
  if p.kind == 'id' or q.kind == 'id':
    h = hterm.strip_app(q if p.kind == 'id' else p)[0]
    return h.kind == 'id' and h.name == (p.name if p.kind == 'id'
                                         else q.name)
  if p.kind == 'num' and q.kind == 'num': return p.text == q.text
  if p.kind == 'num' or q.kind == 'num': return False
  if p.kind == 'list' and q.kind == 'list':
    return len(p.items) == len(q.items) and \
           all(overlap(a, b) for a, b in zip(p.items, q.items))
  if p.kind == 'list' or q.kind == 'list':
    o, l = (q, p) if p.kind == 'list' else (p, q)
    # a list pattern against a :: pattern
    if o.kind == 'infix' and o.op == '::':
      if not l.items: return False
      return overlap(o.l, l.items[0]) and \
             overlap(o.r, Node_list(l.items[1:], l))
    return False
  if p.kind == 'infix' and q.kind == 'infix':
    if p.op != q.op: return False
    return overlap(p.l, q.l) and overlap(p.r, q.r)
  if p.kind == 'infix' or q.kind == 'infix': return False
  hp, ap = hterm.strip_app(p)
  hq, aq = hterm.strip_app(q)
  if hp.kind != 'id' or hq.kind != 'id': return True
  if hp.name != hq.name: return False
  return all(overlap(a, b) for a, b in zip(ap, aq))


def Node_list(items, tok):
  return hterm.Node('list', tok=tok.tok, items=items)


def fmt(text, indent=3, width=72):
  """the layout of a translated term in the HOL Light source"""
  lines = [l.rstrip() for l in text.split('\n') if l.strip()]
  if not lines: return ''
  base = len(lines[0]) - len(lines[0].lstrip())
  out = [lines[0].lstrip()]
  for l in lines[1:]:
    k = len(l) - len(l.lstrip())
    out.append(' ' * (indent + max(0, k - base)) + l.lstrip())
  return '\n'.join(wrap(l, indent, width) for l in out)


def wrap(line, indent, width):
  """break a line that is too long"""
  if len(line) + indent <= width: return line
  k = len(line) - len(line.lstrip())
  out = []
  cur = line
  while len(cur) + (indent if not out else 0) > width:
    cut = -1
    for i, c in enumerate(cur):
      if c == ' ' and i > k and \
         i + (indent if not out else 0) <= width and \
         cur[:i].count('"') % 2 == 0:
        cut = i
    if cut < 0: break
    out.append(cur[:cut])
    cur = ' ' * (k + 2) + cur[cut+1:]
  out.append(cur)
  return '\n'.join(out)


def wf_relation(extra):
  """the relation of a WF_REL_TAC in a HOL4 Termination block"""
  m = re.search(r'WF_REL_TAC\s*([`‘“])', extra)
  if not m: return None, extra
  q = m.group(1)
  close = {'`': '`', '‘': '’', '“': '”'}[q]
  i = m.end()
  if extra[i-1:i+1] == '``': i += 1
  j = extra.index(close, i)
  rel = extra[i:j]
  rest = extra[:m.start()] + extra[j+1:]
  return rel, rest


def mlpath(rel):
  return re.sub(r'Script\.sml$', '.ml', rel)


def port(thy, db=None):
  db = db or dbmod.Db()
  p = Porter(db, thy)
  text = p.run()
  text = '\n'.join(l.rstrip() for l in text.split('\n'))
  for i, l in enumerate(text.split('\n')):
    if len(l) > 72:
      p.warn.append('line %d is %d characters' % (i + 1, len(l)))
  path = ML + db.mlpath_of(thy)
  os.makedirs(os.path.dirname(path), exist_ok=True)
  open(path, 'w').write(text + '\n')
  return path, p.warn, p.amb


if __name__ == '__main__':
  db = dbmod.Db()
  for thy in sys.argv[1:]:
    path, warn, amb = port(thy, db)
    print('wrote', path)
    for w in warn: print('  !', w)
    if amb: print('  ambiguous fields:', amb)
