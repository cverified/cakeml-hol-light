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


def fill(pre, words, width=70):
  """lay out the words in lines of at most width characters, the
     first line starting with pre and the others indented by 3"""
  lines = []
  cur = pre
  for w in words:
    if cur == pre and (pre.endswith('"') or pre.endswith(' ')):
      cur += w
    elif len(cur) + 1 + len(w) <= width:
      cur += ' ' + w
    else:
      lines.append(cur)
      cur = '   ' + w
  lines.append(cur)
  return lines


# where the needs of a file go (they are known at the end of a run)
NEEDS = '(*__NEEDS__*)'


def strip_ml(text, strings=True):
  """the text without its comments (and, with strings, without its
     strings), which is what the needs of a file are computed from;
     a quotation is code, and a (* in one is not a comment"""
  out = []
  i = 0
  n = len(text)
  depth = 0
  while i < n:
    c = text[i]
    if depth:
      if text.startswith('(*', i): depth += 1; i += 2
      elif text.startswith('*)', i): depth -= 1; i += 2
      else: i += 1
      continue
    if text.startswith('(*', i):
      depth = 1; i += 2; continue
    if c == '`':
      j = text.find('`', i + 1)
      if j < 0: j = n
      out.append(text[i+1:j]); i = j + 1; continue
    if c == '"' and strings:
      i += 1
      while i < n and text[i] != '"':
        i += 2 if text[i] == '\\' else 1
      i += 1; continue
    out.append(c); i += 1
  return ''.join(out)


def ocaml_name(n):
  """the name of the OCaml binding of a definition: HOL Light's
     parser takes an identifier of capitals as a value name, but
     not one that starts with a capital and has small letters"""
  if n[:1].isupper() and not any(c.isupper() for c in n[1:]):
    return n[0].lower() + n[1:]
  return n


def shorten(text, width=72):
  """break the lines of a comment that are too long; a line that
     opens the comment is continued under its (* """
  return '\n'.join(wrap(l.rstrip(), 0, width,
                        3 if l.lstrip().startswith('(*') else 2,
                        hard=True)
                   for l in text.split('\n'))


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
    self.abbrevs = db.abbrevs_for(thy)
    self.ctx = hterm.Ctx(names=names, fields=flds,
                         tynames=db.names_for(thy, True),
                         overloaded=db.overloaded(),
                         recs=db.recs_for(thy), thy=thy,
                         accessors=overrides.ACCESSORS.get(thy, {}),
                         cons=db.cons_for(thy), abbrevs=self.abbrevs)
    self.out = []
    self.warn = []
    self.head = None
    self.deps = []
    self.bound = set()
    # an overload of an ancestor does not shadow a constant that
    # this theory defines itself (semanticPrimitives defines
    # num_cmp, which comparison has as an overload of num_compare)
    raw = {nm: txt for nm, txt in db.overloads_for(thy).items()
           if not any(t == thy and k in ('def', 'con', 'rel')
                      for t, k in db.defs.get(nm, []))}
    for _ in range(3):
      for nm, txt in raw.items():
        try: self.ctx.overloads[nm] = self.term(txt)
        except Exception: pass
    self.bound = set()

  # -- helpers ---------------------------------------------------

  def srcname(self):
    return re.sub(r'^.*/(cakeml-src|hol4-src)/', '', self.path)

  def nm(self, n):
    return self.ctx.name(n)

  def tnm(self, n):
    return self.ctx.tyname(n)

  def term(self, text):
    toks = hterm.tokenize(text)
    p = hterm.Parser(toks, self.ctx)
    e = p.parse()
    if p.peek().kind != 'eof':
      t = p.peek()
      raise SyntaxError(f'unparsed input at {t.pos}: {t.text!r}')
    old = self.ctx.vars
    self.ctx.vars = self.shadowing(e)
    try:
      return hterm.Printer(self.ctx).pr(e, 0)
    finally:
      self.ctx.vars = old

  def shadowing(self, e):
    """HOL4 lets a variable shadow a constant, HOL Light does not,
       so a bound variable whose name is a constant of the port or of
       HOL Light is renamed"""
    # an overload of HOL4 is a constant, not a variable, where it
    # occurs in a pattern
    names = hterm.bound_names(e, self.ctx.cons | set(self.ctx.overloads),
                              True)
    # a bound variable is not a reference to a constant, so it does
    # not make the file need the theory of a constant of that name
    self.bound |= names
    return {n: n + "'" for n in names if self.is_const(n)}

  def is_const(self, n):
    return (n in self.db.hl or n in self.db.provided or
            any(k not in ('type', 'tyabbrev')
                for _, k in self.db.defs.get(n, [])))

  def typ(self, text):
    ty = hterm.parse_type_text(text)
    ty = hterm.expand_type(ty, self.abbrevs)
    return hterm.print_type(ty, self.ctx)

  # -- the blocks ------------------------------------------------

  def run(self):
    blocks = hol4.parse(self.path)
    self.db.base_grammar(self.thy)
    chunks = []                 # (blank lines before, text)
    for b in blocks:
      before = len(self.out)
      try:
        # a loose_equality or tight_equality declaration changes the
        # precedence of = from here on
        mode = hol4.equality_mode(b.text) if b.kind == 'ML' else None
        if mode: hterm.set_equality(mode == 'loose')
        if b.kind == 'ML':
          for tok, prec, ass, _ in hol4.fixities(b.text):
            hterm.add_infix(tok, prec, ass)
          if hol4.pmatch_mode(b.text): hterm.enable_pmatch(True)
        self.block(b)
      except Exception as ex:
        self.warn.append(f'{b.kind} {b.name}: {ex}')
        self.out.append(f'(* PORT FAILED: {b.kind} {b.name}: {ex}\n'
                        f'{b.text}\n*)')
      new = self.out[before:]
      if new:
        # the needs of the port start a paragraph of their own
        blanks = max(1, b.blanks) if b.kind == 'Ancestors' else b.blanks
        chunks.append((blanks, '\n'.join(new)))
    # the blank lines of the HOL4 source are kept between the blocks,
    # so that a comment stays with what it belongs to
    text = ''
    for i, (blanks, c) in enumerate(chunks):
      if i: text += '\n' * (1 + min(blanks, 2))
      text += c
    text = (self.head + '\n' + text if self.head else text) + '\n'
    # the files that the translation needs
    deps = sorted(set(self.deps) |
                  self.db.providers(self.thy, strip_ml(text),
                                    self.bound))
    needs = sorted(set('needs "%s";;' % self.db.mlpath_of(d)
                       for d in deps if d in self.db.thy_of_file))
    return text.replace(NEEDS, '\n'.join(needs) if needs else
                        '(* this file needs nothing of the port *)')

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
      self.out.append(shorten(b.text))
    elif k == 'Theory':
      # the header of the port comes first, before the comments that
      # the HOL4 file has before its Theory line
      self.head = HEAD % (b.name, self.srcname(),
                          LIBNOTE if self.kind == 'lib' else '')
    elif k == 'Ancestors':
      # an ancestor may be marked as [qualified]
      deps = [re.sub(r'\[.*\]', '', w) for w in b.body.split()] + \
             overrides.EXTRA_NEEDS.get(self.thy, [])
      # the needs are computed from the translation, which uses the
      # names that the port gives the constants, so they are filled
      # in at the end of the run
      self.deps = deps
      self.out.append(NEEDS)
      ext = [d for d in deps if d not in self.db.thy_of_file]
      if ext:
        self.out.append('\n'.join(
          fill('(* HOL4 ancestors outside the port:', ext, 69)) + ' *)')
      # definitions that HOL4 generates with ML code, and that the
      # port has by hand
      if self.thy in overrides.EXTRA_HEAD:
        self.out.append('\n' + overrides.EXTRA_HEAD[self.thy].strip())
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
    elif k in ('Theorem', 'Triviality', 'ThmValue'):
      pass
    elif k == 'ML':
      if any(re.search(pat, b.text) for pat in IGNORE_ML):
        return
      self.warn.append('ML code skipped: ' + b.text.strip()[:60])
      self.out.append('(* HOL4 ML code, not ported:\n' +
                      shorten(b.text) + '\n*)')
    else:
      self.warn.append('unknown block ' + k)

  # -- datatypes -------------------------------------------------

  def datatype(self, b):
    specs = hol4.split_top(hol4.strip_comments(b.body), ';')
    # the names of this block are the ones of its own constants
    self.ctx.defining = set()
    for ty, cons, flds in hol4.datatype_names(b.body):
      self.ctx.defining |= set([ty] + cons + flds)
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
          argtys.append(tp.parse_dtarg())
        cons.append((cname, argtys))
      parts.append((ty, cons))
    if not parts: return
    spec = ';\n   '.join(
      '%s = %s' % (self.tnm(ty),
                   ' | '.join(
                     ' '.join([self.nm(c)] +
                              ['(%s)' % self.typ_ast(a) for a in args])
                     for c, args in cons))
      for ty, cons in parts)
    names = [ocaml_name(self.tnm(ty)) for ty, _ in parts]
    lhs = ','.join('%s_INDUCT' % n for n in names[:1]) + ',' + \
          ','.join('%s_RECURSION' % n for n in names[:1])
    # the specification is laid out in lines of at most 72
    # characters; a line that is continued ends in a backslash,
    # which OCaml leaves out of the string
    text = '\n'.join(
      ' \\\n'.join(fill('  "' if k == 0 else '   ', part.split(), 69))
      for k, part in enumerate(spec.split('\n')))
    overloads = self.overloads_of(
      [c for _, cons in parts for c, _ in cons])
    head = 'let %s = define_datatype' % lhs
    if len(head) > 72:
      head = 'let %s =\n  define_datatype' % lhs
      if max(len(l) for l in head.split('\n')) > 72:
        head = ('let %s,\n    %s =\n  define_datatype'
                % tuple(lhs.split(',')))
    self.out.append('%s\n%s";;' % (head, text))
    if overloads: self.out.append('\n'.join(overloads))
    self.ctx.defining = set()

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
    lines = []
    for i, (f, t) in enumerate(flds):
      pre = '  [' if i == 0 else '   '
      lines.append(' \\\n'.join(
        fill(pre + '"%s","' % f, t.split(' '), 70)) + '"')
    head = ('let %s_FIELDS = define_record "%s"'
            % (ocaml_name(self.tnm(ty)), self.tnm(ty)))
    if len(head) > 72:
      head = ('let %s_FIELDS =\n  define_record "%s"'
              % (ocaml_name(self.tnm(ty)), self.tnm(ty)))
    self.out.append('%s\n%s];;' % (head, ';\n'.join(lines)))

  def overloads_of(self, names):
    """the declarations that make the names of a block the overloads
       that HOL4 has for them"""
    out = []
    for nm in names:
      if nm not in self.ctx.overloaded: continue
      new = self.nm_defined(nm)
      if new == nm: continue
      text = 'hol4_overload "%s" "%s";;' % (nm, new)
      if len(text) > 72:
        text = 'hol4_overload "%s"\n  "%s";;' % (nm, new)
      out.append(text)
    return out

  def nm_defined(self, n):
    """the name of the constant that a block defines"""
    old = self.ctx.defining
    self.ctx.defining = {n}
    try:
      return self.ctx.name(n)
    finally:
      self.ctx.defining = old

  # -- definitions -----------------------------------------------

  def definition(self, b):
    name = ocaml_name(b.name)
    key = (self.thy, b.name)
    if key in overrides.NOT_YET:
      self.warn.append('%s: PENDING (%s)'
                       % (b.name, overrides.NOT_YET[key].split('\n')[0]))
      self.out.append('(* PENDING: %s\n%s *)'
                      % (overrides.NOT_YET[key], shorten(b.text.strip())))
      return
    key = (self.thy, name)
    if key in overrides.REPLACE:
      self.out.append(overrides.REPLACE[key].strip())
      return
    body = b.body
    self.ctx.defining = set(dbmod.definition_names(body))
    self.ctx.intnums = key in overrides.INT_NUMERALS
    self.ctx.wordnot = key in overrides.WORD_NOT
    if key in overrides.CLAUSE_FORM:
      term = None
      clauses = self.clause_form(body)
    elif (key in overrides.MATCH_FORM or self.overlapping(body) or
          self.multi_pattern(body)):
      # one clause with a match, which HOL Light handles far better
      # than a definition by patterns on several arguments
      term = fmt(self.match_form(body))
    elif self.clause_clash(body):
      term = None
      clauses = self.clause_form(body)
    else:
      term = fmt(self.term(body))
    rel = overrides.MEASURE.get(key)
    if term is None and rel is not None:
      text = ('(* the termination relation is not in the HOL4 '
              'source *)\nlet %s = cake_define_list_wf\n  `%s`\n'
              '  %s;;' % (name, rel, clauses))
    elif term is None:
      text = ('let %s = cake_define_list\n  %s;;' % (name, clauses))
    elif rel is not None:
      text = ('(* the termination relation is not in the HOL4 '
              'source *)\nlet %s = cake_define_wf\n  `%s`\n'
              '  `%s`;;' % (name, rel, term))
    elif b.extra is None:
      text = 'let %s = cake_define\n  `%s`;;' % (name, term)
    else:
      wf, rest = wf_relation(b.extra)
      if wf is None:
        self.warn.append(f'{name}: no WF_REL_TAC in the Termination')
        text = (shorten('(* TERMINATION: %s *)' % b.extra.strip()) +
                '\nlet %s = cake_define\n  `%s`;;' % (name, term))
      else:
        text = (shorten('\n'.join(
                  fill('(* HOL4 termination:', rest.split(), 69))
                + ' *)') +
                '\nlet %s = cake_define_wf\n  `%s`\n  `%s`;;'
                % (name, fmt(self.term(wf), last=1), term))
    # the definition is followed by the overloads of HOL4, where the
    # name it gives a constant is one that other theories use too
    overloads = self.overloads_of(sorted(self.ctx.defining))
    self.out.append(text if not overloads else
                    text + '\n' + '\n'.join(overloads))
    self.ctx.intnums = False
    self.ctx.wordnot = False
    self.ctx.defining = set()

  def clause_form(self, body):
    """the clauses of a definition as separate quotations: HOL4
       typechecks every clause of a definition on its own, so the
       same variable name can have different types in two clauses,
       which one HOL Light quotation cannot"""
    toks = hterm.tokenize(hol4.strip_comments(body))
    e = hterm.Parser(toks, self.ctx).parse()
    old = self.ctx.vars
    self.ctx.vars = self.shadowing(e)
    try:
      p = hterm.Printer(self.ctx)
      cls = [fmt(p.pr(cl, 0), indent=4, last=3)
             for cl in hterm.conjuncts_of(e)]
    finally:
      self.ctx.vars = old
    return '[`' + '`;\n   `'.join(cls) + '`]'

  # -- a definition as one clause with a match -------------------

  def clause_clash(self, body):
    """does a variable of a definition occur in two clauses in
       places where its type can differ (as x does in ast's
       every_exp, where one clause has Fun x e and another one
       Let x e1 e2)?  HOL4 typechecks every clause on its own, so
       the port then writes the clauses as separate quotations"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
      cls = hterm.clauses_of(e)
    except Exception:
      return False
    if len(cls) < 2: return False
    global CONS
    CONS = self.ctx.cons
    # the type of a variable in a pattern is the type of the
    # argument of the constructor it sits in; the clause form is
    # only needed where those types can differ
    where = {}
    def walk(p, ty):
      while p.kind in ('paren', 'typed'): p = p.e
      if p.kind == 'id':
        # a wildcard is a fresh variable in every clause anyway, and
        # a position whose type is not known says nothing
        if (p.name == '_' or ty is None or p.name in CONS or
            p.name in hterm.HLCONS): return
        where.setdefault(p.name, set()).add(ty)
        return
      if p.kind == 'app':
        h, args = hterm.strip_app(p)
        nm = h.name if h.kind == 'id' else '?'
        for j, a in enumerate(args):
          tys = self.db.con_argty.get((nm, j))
          walk(a, min(tys) if tys and len(tys) == 1 else None)
        return
      if p.kind == 'infix':
        walk(p.l, None); walk(p.r, None)
    for _, args, _ in cls:
      for i, a in enumerate(args): walk(a, ('arg', i))
    return any(len(v) > 1 for v in where.values())

  def multi_pattern(self, body):
    """does a definition that is not recursive match on more than
       one argument?  HOL Light's machinery for a definition by
       patterns is very slow for those, and a match is not"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
      cls = hterm.clauses_of(e)
    except Exception:
      return False
    if len(cls) < 2: return False
    heads = set(h.name for h, _, _ in cls if h.kind == 'id')
    # a recursive definition keeps its clauses: the termination
    # machinery does not look inside a match
    for _, _, r in cls:
      if any(nm in heads
             for nm in re.findall(r"[A-Za-z][A-Za-z0-9_']*",
                                  hterm.Printer(self.ctx).pr(r, 0))):
        return False
    global CONS
    CONS = self.ctx.cons
    pats = [args for _, args, _ in cls]
    n = min(len(a) for a in pats)
    posns = 0
    for i in range(n):
      if any(not is_var_pat(a[i]) for a in pats): posns += 1
    return posns >= 2

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
           and args[i].name != '_' and args[i].name not in names:
          nm = args[i].name; break
      if nm is None:
        nm = 'x' + str(i + 1)
        while nm in names: nm += "'"
      names.append(nm)
    pats = [i for i in range(n)
            if any(args[i].kind != 'id' or args[i].name in self.ctx.cons
                   for _, args, _ in cls)
            and not all(args[i].kind == 'id' and
                        args[i].name not in self.ctx.cons
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
    txt = (overrides.TYPE_TEXT.get((self.thy, b.name)) or
           dbmod.strip_quote(b.body))
    ty = hterm.parse_type_text(txt)
    params = hterm.type_vars_of(ty)
    if params:
      self.out.append(shorten(
        '(* HOL4 type abbreviation (expanded in the port):'
        '\n     %s = %s *)' % (b.name, txt)))
    else:
      # the type may be too long for one line
      body = self.typ(txt)
      head = 'new_type_abbrev("%s",`:' % self.tnm(b.name)
      text = '\n'.join(fill(head, body.split(' '), 69)) + '`);;'
      if max(len(l) for l in text.split('\n')) > 72:
        text = ('new_type_abbrev("%s",\n' % self.tnm(b.name) +
                '\n'.join(fill('  `:', body.split(' '), 69)) + '`);;')
      self.out.append(text)

  def overload(self, b):
    txt = dbmod.strip_quote(b.body)
    self.warn.append('Overload %s' % b.name)
    self.out.append(shorten(
      '(* HOL4 overload (expanded in the port):\n'
      '     %s = %s *)' % (b.name, txt)))

  def inductive(self, b):
    term = fmt(self.term(b.body))
    self.out.append('let %s = cake_inductive\n  `%s`;;'
                    % (ocaml_name(b.name), term))


CONS = set()           # the constructors in scope, set by the porter


def is_var_pat(p):
  """is this pattern a variable?"""
  while p.kind in ('paren', 'typed'): p = p.e
  return p.kind == 'id' and p.name not in CONS


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


def fmt(text, indent=3, width=72, last=3):
  """the layout of a translated term in the HOL Light source; the
     last line of the term is followed by a quote and a ;; (last
     characters), so it has to be that much shorter"""
  lines = [l.rstrip() for l in text.split('\n') if l.strip()]
  if not lines: return ''
  base = len(lines[0]) - len(lines[0].lstrip())
  out = [lines[0].lstrip()]
  for l in lines[1:]:
    k = len(l) - len(l.lstrip())
    out.append(' ' * min(indent + max(0, k - base), 30) + l.lstrip())
  return '\n'.join(
    wrap(l, indent, width - (last if i == len(out) - 1 else 0))
    for i, l in enumerate(out))


# the characters a term may be broken before: a newline is as good
# as a space between two tokens of HOL Light
SAFE = '([,#+|'


def wrap(line, indent, width, extra=2, hard=False):
  """break a line that is too long at a space (or, in a term, before
     a character that starts a token); the continuation is indented
     by extra, and with hard a line without any place to break is
     broken anyway (which only comments allow)"""
  k = len(line) - len(line.lstrip())
  ind = ' ' * (k + extra)
  out = []
  cur = line
  first = True
  while len(cur) + (indent if first else 0) > width:
    limit = width - (indent if first else 0)
    cut = -1
    drop = 0
    safe = -1
    quoted = False
    i = 0
    while i < len(cur) and i <= limit:
      c = cur[i]
      if quoted:
        # a backslash in a string escapes the next character
        if c == '\\': i += 2; continue
        if c == '"': quoted = False
        i += 1; continue
      if c == '"':
        quoted = True; i += 1; continue
      # the break has to be beyond the indentation of the
      # continuation, or the line would not get any shorter
      if i > len(ind):
        if c == ' ': cut = i; drop = 1
        elif c in SAFE and cur[i-1] != ' ': safe = i
      i += 1
    if cut < 0 and safe > 0: cut = safe; drop = 0
    if cut < 0:
      # nothing to break at: with a long indentation, try again with
      # a shorter one
      if len(ind) > 6:
        ind = ' ' * 6
        continue
      if not hard or limit <= len(ind) + 1: break
      cut = limit
      drop = 0
    out.append(cur[:cut])
    cur = ind + cur[cut+drop:]
    first = False
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
  text = re.sub(r'\n\n\n+', '\n\n\n', text).strip('\n')
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
