"""Translate a CakeML HOL4 script file to a HOL Light file.

  python3 -I tools/port.py <theory>

writes ml/<path>/<theory>.ml and reports what it could not do.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'
SRC = hol4.SRC

HEAD = '''(* =========================================================================\
 *)
(*  %s *)
(*  Ported from HOL4's %s%s *)
(* =========================================================================\
 *)
'''


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
    self.rel = db.thy_of_file[thy]
    names = db.names_for(thy)
    fields, amb = db.fields_for(thy)
    self.amb = amb
    self.ctx = hterm.Ctx(names=names,
                         fields={f: t for f, t in fields.items() if t},
                         recs=db.recs_for(thy), thy=thy)
    self.abbrevs = db.abbrevs_for(thy)
    self.out = []
    self.warn = []

  # -- helpers ---------------------------------------------------

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
    blocks = hol4.parse(SRC + self.rel)
    first = True
    for b in blocks:
      try:
        self.block(b)
      except Exception as ex:
        self.warn.append(f'{b.kind} {b.name}: {ex}')
        self.out.append(f'(* PORT FAILED: {b.kind} {b.name}: {ex}\n'
                        f'{b.text}\n*)\n')
    return '\n'.join(self.out)

  def block(self, b):
    k = b.kind
    if k == 'Comment':
      self.out.append(b.text)
    elif k == 'Theory':
      self.out.append(HEAD % (b.name, self.rel, ''))
    elif k == 'Ancestors':
      deps = [w for w in b.body.split()]
      needs = []
      for d in deps:
        if d in self.db.thy_of_file:
          path = self.db.thy_of_file[d]
          needs.append('needs "%s";;' % mlpath(path))
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
    body = b.body
    term = fmt(self.term(body))
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


def fmt(text, indent=3):
  """the layout of a translated term in the HOL Light source"""
  lines = [l.rstrip() for l in text.split('\n')]
  while lines and not lines[0].strip(): lines.pop(0)
  while lines and not lines[-1].strip(): lines.pop()
  if not lines: return ''
  base = len(lines[0]) - len(lines[0].lstrip())
  out = [lines[0].lstrip()]
  for l in lines[1:]:
    if not l.strip():
      out.append('')
    else:
      k = len(l) - len(l.lstrip())
      out.append(' ' * (indent + max(0, k - base)) + l.lstrip())
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
  path = ML + mlpath(p.rel)
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
