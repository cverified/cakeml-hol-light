"""Translate a CakeML HOL4 script file to a HOL Light file.

  python3 -I tools/port.py <theory>

writes ml/<path>/<theory>.ml and reports what it could not do.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, overrides
hterm.NAME_MAP = overrides.NAME_MAP
hterm.TYPE_MAP = overrides.TYPE_MAP

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
                         overloaded=db.overloaded_for(thy),
                         recs=db.recs_for(thy), thy=thy,
                         accessors=overrides.ACCESSORS.get(thy, {}),
                         updaters=overrides.UPDATERS.get(thy, {}),
                         cons=db.cons_for(thy), abbrevs=self.abbrevs,
                         ambfields=db.ambiguous_fields(),
                         con_argty=db.con_argty_for(thy))
    self.out = []
    self.warn = []
    self.head = None
    self.deps = []
    self.restore = set()   # the infixes to put back at the end
    self.bound = set()
    self.contys = set()
    # an overload of an ancestor does not shadow a constant that
    # this theory defines itself (semanticPrimitives defines
    # num_cmp, which comparison has as an overload of num_compare)
    raw = {nm: txt for nm, txt in db.overloads_for(thy).items()
           if not any(t == thy and k in ('def', 'con', 'rel')
                      for t, k in db.defs.get(nm, []))
           and not self.is_overloaded(nm, txt)}
    for _ in range(3):
      for nm, txt in raw.items():
        try: self.ctx.overloads[nm] = self.term(txt)
        except Exception: pass
    self.bound = set()

  # -- helpers ---------------------------------------------------

  def is_overloaded(self, nm, txt):
    """is this HOL4 overload one that the port declares as an
       overload of HOL Light instead of expanding it?  (the name of
       a constant of another theory of the port, which expanding
       would resolve the wrong way there)"""
    return (bool(re.match(r"^[A-Za-z][A-Za-z0-9_']*$", txt.strip())) and
            len({t for t, _ in self.db.defs.get(nm, [])}) > 1)

  def srcname(self):
    return re.sub(r'^.*/(cakeml-src|hol4-src)/', '', self.path)

  def nm(self, n):
    return self.ctx.name(n)

  def tnm(self, n):
    return self.ctx.tyname(n)

  def term(self, text, annotate=False):
    toks = hterm.tokenize(text)
    p = hterm.Parser(toks, self.ctx)
    e = p.parse()
    if p.peek().kind != 'eof':
      t = p.peek()
      raise SyntaxError(f'unparsed input at {t.pos}: {t.text!r}')
    old = self.ctx.vars
    self.ctx.vars = self.shadowing(e)
    # the patterns of the first clause of every function carry the
    # type of their constructor where its name is one that several
    # theories in scope have, so that it is resolved as HOL4 does
    seen = set()
    for cl in hterm.conjuncts_of(e):
      try:
        h = hterm.strip_app(hterm.clauses_of(cl)[0][0])[0]
        nm = h.name if h.kind == 'id' else None
      except Exception:
        nm = None
      if nm is None or nm in seen: continue
      seen.add(nm)
      self.annotate(cl, not annotate)
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
    # a name that the port overloads the accessors of a record
    # field with is a constant of HOL Light as well
    return (n in self.db.hl or n in self.db.provided or
            n in set(self.db.ambiguous_fields().values()) or
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
    # an infix that an ancestor overloads with a constant is written
    # as an application of that constant
    anc = self.db.ancestors(self.thy)
    for (thy, tok), (txt, loc) in self.db.ovl_infix.items():
      if (thy in anc and not loc and tok in hterm.OWN_INFIX
          and IDENT.match(txt)):
        hterm.set_infix_name(tok, self.ctx.name(txt))
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
          self.enable_monad(b.text)
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
    # an infix that this file overloads with an append of its own is
    # the one of HOL Light again for the files that come after
    if self.restore:
      text += '\n' + ''.join(
          'hol4_overload "%s" "%s";;\n'
          % (tok, overrides.BASE_INFIX_CONST[tok])
          for tok in sorted(self.restore))
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
      if self.hol_reln(b):
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
    # HOL Light gives the type the type variables of the whole
    # specification, in the order in which it sorts them, so the
    # port knows how to write the type of a constructor
    params = sorted(set(re.findall(r"'[A-Za-z][A-Za-z0-9_']*", spec)))
    for ty, _ in parts:
      self.db.ty_params[(self.thy, self.tnm(ty))] = params
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
    # the accessor and the update of a field that several record
    # types have become overloads of the name of the field
    amb = self.db.ambiguous_fields()
    for f, _ in flds:
      if f not in amb: continue
      for n, c in ((amb[f], f), (amb[f] + '_fupd', f + '_fupd')):
        text = ('hol4_overload "%s" "%s_%s";;'
                % (n, self.tnm(ty), c))
        if len(text) > 72:
          text = ('hol4_overload "%s"\n  "%s_%s";;'
                  % (n, self.tnm(ty), c))
        self.out.append(text)

  def overloads_of(self, names):
    """the declarations that make the names of a block the overloads
       that HOL4 has for them"""
    out = []
    for nm in names:
      # the declaration is global, so it is made for every name
      # that the port renames anywhere, not only for the ones that
      # are ambiguous in the scope of this theory
      if nm not in self.db.overloaded(): continue
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
    if key in overrides.EXTRA_BEFORE:
      self.out.append(overrides.EXTRA_BEFORE[key].strip() + '\n')
    if key in overrides.REPLACE:
      self.out.append(overrides.REPLACE[key].strip())
      return
    body = b.body
    self.ctx.defining = set(dbmod.definition_names(body))
    self.ctx.intnums = key in overrides.INT_NUMERALS
    self.ctx.intneg = key in overrides.INT_NEG
    self.ctx.intvars = self.int_vars(body)
    self.ctx.reclit = overrides.RECORD_OF.get(key)
    self.ctx.wordnot = key in overrides.WORD_NOT
    if key in overrides.CLAUSE_FORM:
      term = None
      clauses = self.clause_form(body)
    elif (key in overrides.MATCH_FORM or self.overlapping(body) or
          self.multi_pattern(body)):
      # one clause with a match, which HOL Light handles far better
      # than a definition by patterns on several arguments
      term = fmt(self.match_form(body))
    elif self.several_clauses(body):
      # HOL4 typechecks every clause of a definition on its own, so
      # the port writes them as separate quotations, with the type
      # of the pattern on each
      term = None
      clauses = self.clause_form(body)
    elif key in overrides.ANNOTATE:
      term = fmt(self.term(body, annotate=True))
    else:
      term = fmt(self.term(body))
    rel = overrides.MEASURE.get(key)

    def size_prelude(text):
      """a measure that uses the size function of a datatype needs
         it to be there; the port makes the size functions when a
         definition first needs one, which is too late for the
         measure itself"""
      out = ''
      for ty in sorted(set(re.findall(r"([A-Za-z0-9_']+)_size\b",
                                      text))):
        out += 'let _ = size_thms "%s";;\n' % ty
      return out

    sizes = size_prelude(rel) if rel else ''
    if term is None and rel is not None:
      text = (sizes + '(* the termination relation is not in the HOL4 '
              'source *)\nlet %s = cake_define_list_wf\n  `%s`\n'
              '  %s;;' % (name, rel, clauses))
    elif term is None:
      text = ('let %s = cake_define_list\n  %s;;' % (name, clauses))
    elif rel is not None:
      text = (sizes + '(* the termination relation is not in the HOL4 '
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
        wftext = fmt(self.term(wf), last=1)
        text = (size_prelude(wftext) +
                shorten('\n'.join(
                  fill('(* HOL4 termination:', rest.split(), 69))
                + ' *)') +
                '\nlet %s = cake_define_wf\n  `%s`\n  `%s`;;'
                % (name, wftext, term))
    # the definition is followed by the overloads of HOL4, where the
    # name it gives a constant is one that other theories use too
    overloads = self.overloads_of(sorted(self.ctx.defining))
    self.out.append(text if not overloads else
                    text + '\n' + '\n'.join(overloads))
    self.ctx.intnums = False
    self.ctx.wordnot = False
    self.ctx.intneg = False
    self.ctx.defining = set()

  def con_thy(self, nm, kinds=('con',)):
    """the theory whose constant of this name is meant.  Where the
       name is ambiguous it is the theory that comes last among the
       ones in scope, which is the one HOL4's overload resolution
       takes"""
    t, n = nm.split('$') if '$' in nm else (None, nm)
    if t: return t
    anc = self.db.ancestors(self.thy) | {self.thy}
    ts = [x for x, k in self.db.defs.get(n, [])
          if k in kinds and x in anc]
    if kinds == ('con',) and self.contys:
      ts = [x for x in ts if x in self.contys] or ts
    if not ts: return None
    rank = {thy: i for i, (thy, _, _) in enumerate(self.db.order)}
    return max(ts, key=lambda x: rank.get(x, -1))

  def const_name(self, nm):
    """the name that the port gives the constant that a name of a
       CakeML source means, also where that name is overloaded"""
    n = nm.split('$')[-1]
    t = self.con_thy(nm, ('con', 'def', 'rel'))
    return self.ctx.names.get((t, n), n) if t else self.ctx.name(nm)

  def con_name(self, nm):
    """the name that the port gives the constructor that an
       ambiguous name means; writing it out resolves the overload
       without a type annotation, which HOL Light cannot leave
       general (a type variable that the user writes is rigid)"""
    t = self.con_thy(nm)
    n = nm.split('$')[-1]
    return self.ctx.names.get((t, n)) if t else None

  def con_type(self, nm):
    """the type of a constructor, as the port writes it"""
    t = self.con_thy(nm)
    n = nm.split('$')[-1]
    if not t: return None
    for (t2, ty), (cons, _) in self.db.datatypes.items():
      if t2 == t and n in cons:
        nm = self.ctx.tyname(ty)
        ps = self.db.ty_params.get((t2, nm))
        return '(%s)%s' % (','.join(ps), nm) if ps else nm
    return None

  def ambiguous_con(self, nm):
    """is this the name of a constructor of more than one theory in
       scope, so that only the type says which one it is?"""
    if '$' in nm: return False
    anc = self.db.ancestors(self.thy) | {self.thy}
    return len([x for x, k in self.db.defs.get(nm, [])
                if k == 'con' and x in anc]) > 1

  def annotate_pat(self, p, ambiguous=False):
    """the pattern with the type of its constructor on it"""
    done = [False]
    def go(p):
      if done[0]: return p
      while p.kind == 'paren': p = p.e
      if p.kind == 'app':
        h, _ = hterm.strip_app(p)
        if h.kind == 'id' and (h.name in self.ctx.cons or
                               '$' in h.name):
          if ambiguous and not self.ambiguous_con(h.name):
            return p
          ty = self.con_type(h.name)
          # a type variable that the port writes is rigid in HOL
          # Light, so a type with parameters cannot be written in an
          # annotation; the name of the constructor itself then says
          # which one it is
          if ambiguous and ty and ty.startswith('('):
            nm = self.con_name(h.name)
            if nm:
              done[0] = True
              h.name = nm
            return p
          if ty:
            done[0] = True
            return hterm.Node('paren', tok=p.tok,
                     e=hterm.Node('typed', tok=p.tok, e=p,
                                  ty=hterm.tokenize(ty)))
        return p
      if p.kind == 'list':
        p.items = [go(a) for a in p.items]
        return p
      if p.kind == 'infix' and p.op in ('::', ','):
        p.l = go(p.l); p.r = go(p.r)
        return p
      return p
    return go(p)

  def annotate(self, cl, ambiguous=False):
    """the type of the pattern of a clause that is a quotation of
       its own: without it the clause can typecheck differently
       from the others (the name of a constructor is ambiguous)"""
    e = cl
    while e.kind == 'paren': e = e.e
    if not (e.kind == 'infix' and e.op in ('=', '<=>')): return cl
    _, args = hterm.strip_app(e.l)
    e.l = hterm.strip_app(e.l)[0]
    for a in args:
      e.l = hterm.Node('app', tok=e.l.tok, fn=e.l,
                       arg=self.annotate_pat(a, ambiguous))
    return cl

  def int_vars(self, body):
    """the variables of a definition that hold an integer: the ones
       that are the argument of a constructor whose type there is
       int, as i is in clos_known's [Tuple _ xs; Int i]"""
    out = set(); other = set()
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
    except Exception:
      return out

    def go(n):
      if n is None or not isinstance(n, hterm.Node): return
      if n.kind == 'app':
        h, args = hterm.strip_app(n)
        if h.kind == 'id':
          for i, a in enumerate(args):
            while a.kind == 'paren': a = a.e
            if a.kind != 'id': continue
            ty = self.ctx.con_argty.get((h.name, i))
            if ty in ('int', 'real'): out.add(a.name)
            elif ty: other.add(a.name)
      for k in ('e', 'l', 'r', 'fn', 'arg', 'body', 's', 'p', 'p2',
                'ty'):
        go(getattr(n, k, None))
      for k in ('items', 'stmts', 'arms', 'upds', 'vs', 'cls'):
        for x in getattr(n, k, None) or []:
          if isinstance(x, hterm.Node): go(x)
          elif isinstance(x, (tuple, list)):
            for y in x:
              if isinstance(y, hterm.Node): go(y)
    go(e)
    # a name that is the argument of a constructor whose type there
    # is not an integer as well says nothing
    return out - other

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
      cls = [fmt(p.pr(self.annotate(cl, True), 0), indent=4, last=3)
             for cl in hterm.conjuncts_of(e)]
    finally:
      self.ctx.vars = old
    return '[`' + '`;\n   `'.join(cls) + '`]'

  # -- a definition as one clause with a match -------------------

  def several_clauses(self, body):
    """has this definition more than one clause?  Then the clauses
       are quotations of their own, as in HOL4, where each of them
       is typechecked separately"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
      cls = hterm.clauses_of(e)
    except Exception:
      return False
    global CONS
    CONS = self.ctx.cons
    self.clause_clash(body)      # sets contys for the annotations
    return len(cls) > 1

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
    # the theories that can provide all the constructors of the
    # patterns: with those, the type of the argument of a
    # constructor is known even where the name is ambiguous
    cons_in = []
    def cons_of(p):
      while p.kind in ('paren', 'typed'): p = p.e
      if p.kind == 'app':
        h, args = hterm.strip_app(p)
        if h.kind == 'id': cons_in.append(h.name)
        for a in args: cons_of(a)
      elif p.kind == 'list':
        for a in p.items: cons_of(a)
      elif p.kind == 'infix':
        cons_of(p.l); cons_of(p.r)
    for _, args, _ in cls:
      for a in args: cons_of(a)
    # a constructor that the source qualifies (bvi$Call) says the
    # theory itself
    def split_con(nm):
      if '$' in nm:
        t, n = nm.split('$')
        return t, n
      return None, nm
    thys = None
    for nm in cons_in:
      t, n = split_con(nm)
      ts = ({t} if t else
            {t for t, k in self.db.defs.get(n, []) if k == 'con'})
      if not ts: continue
      thys = ts if thys is None else thys & ts
    self.contys = thys or set()
    def argty(nm, j):
      t, nm = split_con(nm)
      ts = {t} if t else thys
      if ts:
        out = {self.db.con_argty_thy[(t, nm, j)] for t in ts
               if (t, nm, j) in self.db.con_argty_thy}
        if out: return out
      return self.db.con_argty.get((nm, j))
    where = {}
    def walk(p, tys):
      while p.kind in ('paren', 'typed'): p = p.e
      if p.kind == 'id':
        # a wildcard is a fresh variable in every clause anyway, and
        # a position whose type is not known says nothing
        if (p.name == '_' or not tys or p.name in CONS or
            p.name in hterm.HLCONS): return
        where.setdefault(p.name, []).append(tys)
        return
      if p.kind == 'app':
        h, args = hterm.strip_app(p)
        nm = h.name if h.kind == 'id' else '?'
        for j, a in enumerate(args):
          walk(a, argty(nm, j))
        return
      if p.kind == 'list':
        for a in p.items: walk(a, None)
        return
      if p.kind == 'infix':
        walk(p.l, None); walk(p.r, None)
    for _, args, _ in cls:
      for i, a in enumerate(args): walk(a, {('arg', i)})
    # the clause form is needed where the places of a variable have
    # no type in common
    return any(not set.intersection(*map(set, v))
               for v in where.values() if len(v) > 1)

  def multi_pattern(self, body):
    """does a definition that is not recursive match on more than
       one argument, or with a pattern inside a constructor?  HOL
       Light's machinery for a definition by patterns is very slow
       for those, and a match is not"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
      cls = hterm.clauses_of(e)
    except Exception:
      return False
    if len(cls) < 2: return False
    # the names as the port writes them, which is how they are in
    # the right hand sides below
    heads = set(self.ctx.name(h.name) for h, _, _ in cls
                if h.kind == 'id')
    # a match is one clause, so it cannot define a family
    if len(heads) > 1: return False
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
      if any(nested_pat(a[i]) for a in pats): return True
    return posns >= 2

  def overlapping(self, body):
    """do the clauses of a definition overlap, so that they rely on
       HOL4's first match semantics?"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      cls = hterm.clauses_of(hterm.Parser(toks, self.ctx).parse())
    except Exception:
      return False
    # a match is one clause, so it cannot define a family
    if len({h.name for h, _, _ in cls if h.kind == 'id'}) > 1:
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
      # the pattern of the first arm carries the type, so that an
      # ambiguous constructor in it is resolved as HOL4 does
      if not arms:
        args = list(args)
        for i in pats:
          args[i] = self.annotate_pat(args[i], True)
      pat = ','.join(pr.pr(args[i], 60) for i in pats)
      if len(pats) > 1: pat = '(' + pat + ')'
      # the body of an arm needs its parentheses: a match, a let
      # or a conditional in it would swallow the arms after it
      arms.append((pat, pr.pr(hterm.rename_ast(r, sub), 2)))
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
    # an overload of one constant whose name other theories of the
    # port use for a constant of their own is an overload in HOL
    # Light as well; expanding it would resolve the name the wrong
    # way where another theory means its own constant
    if b.name and self.is_overloaded(b.name, txt):
      c = self.ctx.name(txt.strip())
      self.out.append('hol4_overload "%s" "%s";;' % (b.name, c))
      return
    # an overload of a symbolic infix the source declared itself is
    # written as an application of the constant it stands for
    if (b.name in hterm.OWN_INFIX and
        b.name not in hterm.BASE_INFIX and IDENT.match(txt.strip())):
      hterm.set_infix_name(b.name, self.ctx.name(txt.strip()))
      return
    # an infix that HOL Light has as well becomes an overload of
    # HOL Light, which resolves it by the type as HOL4 does
    if b.name in hterm.BASE_INFIX and IDENT.match(txt.strip()):
      c = self.const_name(txt.strip())
      self.out.append('hol4_overload "%s" "%s";;' % (b.name, c))
      if b.name in overrides.BASE_INFIX_CONST:
        self.restore.add(b.name)
      return
    self.warn.append('Overload %s' % b.name)
    self.out.append(shorten(
      '(* HOL4 overload (expanded in the port):\n'
      '     %s = %s *)' % (b.name, txt)))

  def enable_monad(self, text):
    """the do notation of a source is the bind of the monad that it
       enables; without one it is HOL4's overloaded monad_bind"""
    nm = hol4.monad_enabled(text)
    if nm is None: return
    m = self.db.monads.get(nm)
    if m is None:
      self.warn.append('unknown monad ' + nm)
      return
    out = {}
    for f in ('bind', 'ignorebind'):
      c = m.get(f)
      if c and IDENT.match(c): out[f] = self.ctx.name(c)
    hterm.set_monad(out)
    # HOL4's monadsyntax overloads return with the unit of the
    # monad, which may be a term and not a constant
    u = m.get('unit')
    if u:
      self.ctx.overloads['return'] = (
          self.ctx.name(u) if IDENT.match(u) else self.term(u))

  def hol_reln(self, b):
    r = hol4.hol_reln(b.text)
    if not r: return False
    name, body = r
    self.inductive(hol4.Block('Inductive', name + '_rules', [], body))
    return True

  def inductive(self, b):
    term = fmt(self.term(b.body))
    self.out.append('let %s = cake_inductive\n  `%s`;;'
                    % (ocaml_name(b.name), term))


IDENT = re.compile(r"^(\w+\$)?[A-Za-z_][A-Za-z0-9_']*$")

CONS = set()           # the constructors in scope, set by the porter


def is_var_pat(p):
  """is this pattern a variable?"""
  while p.kind in ('paren', 'typed'): p = p.e
  return p.kind == 'id' and p.name not in CONS


def vars_pat(p):
  """is this pattern a variable or a tuple of variables, which is
     what the argument of a constructor pattern can be without
     making the pattern a nested one?"""
  while p.kind in ('paren', 'typed'): p = p.e
  if p.kind == 'infix' and p.op == ',':
    return vars_pat(p.l) and vars_pat(p.r)
  return is_var_pat(p)


def nested_pat(p):
  """has this pattern a pattern inside a constructor?  HOL Light's
     machinery for a definition by patterns compiles those into a
     decision tree, which takes minutes where a match takes no
     time at all"""
  while p.kind in ('paren', 'typed'): p = p.e
  if p.kind == 'infix' and p.op == ',':
    return nested_pat(p.l) or nested_pat(p.r)
  if p.kind == 'infix' and p.op == '::':
    args = [p.l, p.r]
  elif p.kind == 'list':
    # [x] is CONS x NIL and [x; y] is CONS x (CONS y NIL)
    return len(p.items) > 1 or any(not vars_pat(a) for a in p.items)
  else:
    h, args = hterm.strip_app(p)
    if not (h.kind == 'id' and h.name in CONS): return False
  return any(not vars_pat(a) for a in args)


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
