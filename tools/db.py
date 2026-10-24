"""The database of the port: names, datatypes, records, type
abbreviations, and the HOL4 -> HOL Light name mapping.

The mapping rule: a CakeML name keeps its name, unless it is
defined in more than one of the ported theories, or clashes with a
HOL Light name; then it gets the name of its theory and an
underscore in front.  If one name of a datatype has to be
renamed, all the names of that datatype are renamed, so that the
constructors of a type stay uniform.
"""
import sys, os, re, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, grammardef, overrides

T = os.path.dirname(os.path.abspath(__file__)) + '/'
SRC = hol4.SRC
HOL4 = T + '../hol4-src/'

# theories that HOL Light provides itself, or that the port
# provides in ml/lib; the name is the HOL Light name
BUILTIN = {}


def load_order():
  """the theories to port: the HOL4 libraries first, then the
     CakeML definition theories (order.txt), then the CakeML proof
     theories, of which the port takes the definitions as well
     (order1b.txt, the second part of the first pass)"""
  libs = [(l.split('\t')[0], HOL4 + l.split('\t')[1].strip(), 'lib')
          for l in open(T + 'libs.txt').read().split('\n') if l]
  cake = [(l.split('\t')[0], SRC + l.split('\t')[1].strip(), 'cakeml')
          for l in open(T + 'order.txt').read().split('\n') if l]
  try:
    cake += [(l.split('\t')[0], SRC + l.split('\t')[1].strip(),
              'cakeml')
             for l in open(T + 'order1b.txt').read().split('\n') if l]
  except IOError:
    pass
  return libs + cake


# the words that HOL Light's term parser reserves: a constant of
# the port cannot have one of them for a name
RESERVED = set(['let', 'in', 'and', 'if', 'then', 'else',
                'match', 'with', 'function', 'when'])


def hl_types():
  """the type names of HOL Light and of the library layer"""
  return set(l.strip() for l in open(T + 'hl-types.txt') if l.strip())


def hl_names():
  return RESERVED | set(l.strip()
                        for l in open(T + 'hl-names.txt')
                        if l.strip())


def hl_idents():
  """the OCaml identifiers that are taken before the port loads:
     the bindings of HOL Light and of the hand written part of the
     library layer, which a binding of the port may not shadow
     (tools/mkhlidents.py writes the list)"""
  return set(l.strip() for l in open(T + 'hl-idents.txt')
             if l.strip())


# the hand written files of the library layer
HANDWRITTEN = ['hol4.ml', 'words4.ml', 'finite_map.ml', 'llist.ml',
               'path.ml']


# the HOL4 theory that every hand written file of ml/lib stands
# for: a name that such a file provides is that theory's, and it
# only wins over the constant of a ported theory of the same name
# where it is in the scope (llist's fromList is what a bare
# fromList means in a theory that has llist as an ancestor, and
# sptree's everywhere else)
HANDWRITTEN_THY = {'hol4.ml': None, 'words4.ml': 'words',
                   'finite_map.ml': 'finite_map',
                   'llist.ml': 'llist', 'path.ml': 'path'}


def provided_thys():
  """the theory that every provided name stands for"""
  out = {}
  for f in HANDWRITTEN:
    for nm in file_names(T + '../ml/lib/' + f):
      out.setdefault(nm, HANDWRITTEN_THY.get(f))
  return out


def file_names(path):
  """the constants that a hand written file of ml/lib defines"""
  s = open(path).read()
  names = set()
  for m in re.finditer(r'new_(?:recursive_)?definition\b[^`]*`([^`]*)`',
                       s):
    for cl in re.split(r'/\\\\', m.group(1)):
      mm = re.match(r"\s*\(?\s*([A-Za-z_][A-Za-z0-9_']*)", cl)
      # the first identifier of a clause is the constant it defines,
      # unless the clause starts with an annotated argument of an
      # infix, as in `(fm:(A,B)fmap) |+ kv = ...'
      if mm and not (len(mm.group(1)) <= 2 and mm.group(1).islower()):
        names.add(mm.group(1))
  for m in re.finditer(r'override_interface\("([^"]+)"', s):
    names.add(m.group(1))
  return names


def provided_names():
  """the HOL4 library constants that the hand written files of
     ml/lib provide"""
  names = set()
  for f in HANDWRITTEN:
    names |= file_names(T + '../ml/lib/' + f)
  return names


class Db:
  def __init__(self):
    self.order = load_order()
    self.hl = hl_names()
    self.hlids = hl_idents()
    self.provided = provided_names()
    self.provided_thy = provided_thys()
    self.read_fixities()
    d = json.load(open(T + 'deps.json'))
    self.deps = d['deps']
    # the ancestors of a theory whose names its parser does not
    # have (an Ancestors[ignore_grammar] block)
    self.nogram = d.get('nogram', {})
    self.defs = collections.defaultdict(list)   # name -> [(thy,kind)]
    self.datatypes = {}        # (thy,ty) -> ([cons],[fields])
    self.recs = {}             # (thy,ty) -> [fields]
    self.rectys = {}           # (thy,ty) -> {field: type text}
    self._fldtoks = None
    self.abbrevs = {}          # (thy,name) -> (params, type text)
    self.overloads = {}        # (thy,name) -> term text
    self.con_argty = {}        # (constructor,index) -> {type texts}
    self.con_argty_thy = {}    # (thy,constructor,index) -> type text
    self._overloaded = None
    self._dist = {}
    # the OCaml bindings that the theorems of the port have taken
    # (a theorem keeps its own name where no other theory and no
    # name of HOL Light has it)
    self.thmnames = set()
    # the OCaml binding that the port gives a theorem of a source,
    # by the name that HOL4 gives it: a source that states a
    # theorem as the value of another one (Theorem foo = bar) is
    # that binding in the port
    self.thmbind = {}
    self._ambflds = None
    self.ty_params = {}        # (thy,type) -> the type parameters
    self.monads = {'option': {'bind': 'OPTION_BIND',
                              'unit': 'SOME',
                              'ignorebind': 'OPTION_IGNORE_BIND',
                              'choice': 'OPTION_CHOICE'}}
    self.thy_of_file = {}
    self.kind_of_thy = {}
    self.scan()
    self.extra_defs()
    self.mapping()
    self.compute_needed()

  # ---------------------------------------------------------------

  def read_fixities(self):
    """the infixes that each source declares itself"""
    self.fix = {}
    self.fixname = {}    # an infix -> the constant that ML maps
                         # it to (set_mapped_fixity's term_name)
    self.ovl_infix = {}  # a symbolic infix -> the constant it means
    for thy, path, kind in self.order:
      try:
        text = open(path, encoding='utf-8').read()
      except Exception:
        text = ''
      self.fix[thy] = hol4.fixities(text)
      self.fixname[thy] = hol4.mapped_names(text)

  def grammar_type(self, thy, path, b):
    """register the datatype that mk_grammar_def makes, so that
       the theories after it know its constructors"""
    try:
      info = grammardef.parse_ml(open(path).read())
      i = b.text.index('mk_grammar_def')
      j = b.text.index('`', i)
      k = b.text.rindex('`')
      rules = grammardef.parse_bnf(b.text[j + 1:k])
      nts = grammardef.nonterminals(rules, info['ntprefix'])
    except Exception:
      return
    ty = info.get('nt_tyname')
    if not ty or not nts: return
    self.datatypes[(thy, ty)] = (nts, [])
    self.defs[ty].append((thy, 'type'))
    for c in nts:
      self.defs[c].append((thy, 'con'))
      self.con_argty_thy.pop((thy, c, 0), None)
    self.defs[info['gname']].append((thy, 'def'))

  def base_grammar(self, thy):
    """put the term grammar in the state in which a theory starts:
       the infixes that its ancestors declare permanently (a temp_
       declaration does not reach the theories that descend from the
       one that makes it)"""
    hterm.reset_grammar()
    hterm.set_equality(False)
    anc = self.ancestors(thy)
    for t, _, _ in self.order:
      if t == thy: break
      if t in anc:
        for tok, prec, ass, temp in self.fix.get(t, []):
          if not temp: hterm.add_infix(tok, prec, ass)
        # and the constant that the declaration maps it to, with
        # the name that HOL4 gives it (the port resolves it to the
        # name it uses itself in Porter.run)
        for tok, nm, temp in self.fixname.get(t, []):
          if not temp: hterm.set_infix_name(tok, nm)

  def scan(self):
    for thy, path, kind in self.order:
      self.thy_of_file[thy] = path
      self.kind_of_thy[thy] = kind
      self.base_grammar(thy)
      only = overrides.ONLY_NAMES.get(thy)
      for b in hol4.parse(path):
        # of a library theory that the port only needs a part of,
        # the other blocks are not there at all: their names
        # would clash with the ones of the port for nothing
        if only is not None and b.kind not in ('ML', 'Ancestors'):
          nms = [b.name] if b.name else []
          if b.kind == 'Datatype':
            for ty, cons, flds in hol4.datatype_names(b.body):
              nms += [ty] + list(cons)
          if not any(n in only for n in nms): continue
        mode = hol4.equality_mode(b.text) if b.kind == 'ML' else None
        if mode: hterm.set_equality(mode == 'loose')
        if b.kind == 'ML':
          for tok, prec, ass, _ in hol4.fixities(b.text):
            hterm.add_infix(tok, prec, ass)
          if hol4.pmatch_mode(b.text): hterm.enable_pmatch(True)
          # the datatype of the nonterminals that HOL4's
          # mk_grammar_def makes with ML code (gram's MMLnonT)
          if 'mk_grammar_def' in b.text:
            self.grammar_type(thy, path, b)
        if (b.kind == 'Overload' and b.name and
            not b.name[0].isalpha()):
          self.ovl_infix[(thy, b.name)] = (
              strip_quote(b.body).strip(), 'local' in b.attrs)
        if b.kind == 'Ancestors':
          # a comment in the list is not an ancestor (dataSem says
          # "data_to_word (* TODO: immoral, semantics shouldn't
          # depend on compiler *)", whose words would be the
          # theories compiler and semantics), and a theory that is
          # only qualified is one all the same
          anc = [w.split('[')[0]
                 for w in hol4.strip_comments(b.body).split()]
          self.deps[thy] = sorted(set(self.deps.get(thy, []) +
                                      [a for a in anc if a]))
        if b.kind == 'Datatype':
          # the texts of the argument types of the constructors: they
          # tell whether a variable in a pattern can have different
          # types in different clauses
          for part in hol4.split_top(hol4.strip_comments(b.body), ';'):
            m = re.match(r"\s*[A-Za-z][A-Za-z0-9_']*\s*=\s*(.*)$",
                         part, re.S)
            if not m or m.group(1).strip().startswith('<|'): continue
            for alt in hol4.split_top(m.group(1), '|'):
              alt = alt.strip()
              if not alt: continue
              try:
                tys = hterm.dtarg_texts(alt)
              except Exception:
                continue
              con = alt.split()[0]
              for j, t in enumerate(tys):
                self.con_argty.setdefault((con, j), set()).add(t)
                self.con_argty_thy[(thy, con, j)] = t
          for ty, cons, flds in hol4.datatype_names(b.body):
            self.datatypes[(thy, ty)] = (cons, flds)
            self.defs[ty].append((thy, 'type'))
            for c in cons: self.defs[c].append((thy, 'con'))
            if flds:
              self.recs[(thy, ty)] = flds
          try:
            for ty, ftys in hol4.datatype_fieldtypes(b.body).items():
              self.rectys[(thy, ty)] = ftys
          except Exception:
            pass
        elif b.kind == 'Definition':
          for nm in definition_names(b.body):
            self.defs[nm].append((thy, 'def'))
        elif b.kind in ('Inductive', 'CoInductive'):
          # the rules of an inductive are implications, which
          # definition_names does not look at: the relations
          # are the heads of their conclusions
          for nm in (definition_names(b.body) or
                     rule_names(b.body) or
                     ([b.name] if b.name else [])):
            self.defs[nm].append((thy, 'rel'))
        elif b.kind == 'Type':
          txt = (overrides.TYPE_TEXT.get((thy, b.name)) or
                 strip_quote(b.body))
          try:
            ty = hterm.parse_type_text(txt)
          except Exception:
            continue
          if not b.name: continue
          params = hterm.type_vars_of(ty)
          self.abbrevs[(thy, b.name)] = (params, txt)
          self.defs[b.name].append((thy, 'tyabbrev'))
        elif b.kind == 'ML':
          for nm, flds in hol4.monad_decls(b.text):
            self.monads[nm] = flds
          for nm in self.monad_funs(thy, b.text):
            self.defs[nm].append((thy, 'def'))
          r = hol4.hol_reln(b.text)
          if r:
            for nm in definition_names(r[1]):
              self.defs[nm].append((thy, 'rel'))
          for m in re.finditer(r'(?:temp_)?type_abbrev\s*\(\s*"([^"]+)"'
                               r'\s*,\s*(?:``|\u201c)\s*:(.*?)'
                               r'(?:``|\u201d)', b.text, re.S):
            nm, txt = m.group(1), m.group(2).strip()
            try:
              ty = hterm.parse_type_text(txt)
            except Exception:
              continue
            self.abbrevs[(thy, nm)] = (hterm.type_vars_of(ty), txt)
            self.defs[nm].append((thy, 'tyabbrev'))
        elif b.kind == 'Overload':
          if b.name:
            local = 'local' in b.attrs
            if not local:
              self.defs[b.name].append((thy, 'overload'))
            self.overloads[(thy, b.name)] = (strip_quote(b.body), local)

  def monad_funs(self, thy, text):
    """the constants that the monadic machinery of ml_monadBaseLib
       makes out of an ML block (tools/port.py writes out the
       definitions): the get_f and set_f of the fields of the
       state record, the raise_C and handle_C of the constructors
       of the exception type, the f_length, f_sub and update_f of
       the fixed size array fields and the run function.  The
       exception functions are only the ones of a theory that has
       the exception type itself: where the type is another
       theory's (linear_scan uses reg_alloc's state_exn), the
       constants of that theory are the ones the port uses"""
    out = []
    m = hol4.MONAD_ACCESS_FUNS.search(text)
    if m:
      for f in self.recs.get((thy, m.group(1)), []):
        out += ['get_' + f, 'set_' + f]
    m = hol4.MONAD_EXN_FUNS.search(text)
    if m and (thy, m.group(1)) in self.datatypes:
      for c in self.datatypes[(thy, m.group(1))][0]:
        out += ['raise_' + c, 'handle_' + c]
    m = hol4.MONAD_ARR_FUNS.search(text)
    if m:
      for x in m.group(1).split(','):
        x = x.strip()
        if x.endswith('_accessors'):
          f = x[:-len('_accessors')]
          out += [f + '_length', f + '_sub', 'update_' + f]
    m = hol4.MONAD_RUN_FUN.search(text)
    if m: out.append('run_' + m.group(3))
    return out

  def extra_defs(self):
    """the constants that the port declares itself"""
    for thy, nm in overrides.EXTRA_DEFS:
      if not any(t == thy for t, _ in self.defs.get(nm, [])):
        self.defs[nm].append((thy, 'def'))
    # and the datatypes that it takes over from a theory that is
    # not ported
    for (thy, ty), cons in overrides.EXTRA_DATATYPES.items():
      if (thy, ty) in self.datatypes: continue
      self.datatypes[(thy, ty)] = ([c for c, _ in cons], [])
      self.defs[ty].append((thy, 'type'))
      for c, argtys in cons:
        self.defs[c].append((thy, 'con'))
        for j, t in enumerate(argtys):
          self.con_argty.setdefault((c, j), set()).add(t)
          self.con_argty_thy[(thy, c, j)] = t

  # ---------------------------------------------------------------

  def mapping(self):
    """compute the HOL4 -> HOL Light name mapping"""
    multi = {nm for nm, v in self.defs.items()
             if len({t for t, _ in v}) > 1}
    # the name that the port overloads the accessors of a record
    # field with is an overloaded name, so a constant of that name
    # is renamed
    multi |= set(self.ambiguous_fields().values())
    self.rename = {}          # (thy,name) -> new name
    # which datatypes have to be renamed as a whole
    bad_types = set()
    for (thy, ty), (cons, flds) in self.datatypes.items():
      if any(c in multi or c in self.hl for c in cons):
        bad_types.add((thy, ty))
    for (thy, ty), (cons, flds) in self.datatypes.items():
      if ty in multi or ty in self.hl:
        self.rename[(thy, ty)] = prefix(thy, ty)
      if (thy, ty) in bad_types:
        for c in cons:
          self.rename[(thy, c)] = prefix(thy, c)
    for nm, v in self.defs.items():
      for thy, kind in v:
        if (thy, nm) in self.rename: continue
        if kind in ('con', 'type'): continue
        if self.kind_of_thy.get(thy) == 'lib' and nm in self.provided:
          continue
        if nm in multi or nm in self.hl:
          self.rename[(thy, nm)] = prefix(thy, nm)
    self.rename.update(overrides.RENAME)
    # the prefix can give a constant the name of another one
    # (clos_to_bvl defines compile_inc as well as
    # clos_to_bvl_compile_inc); the renamed one then gets a prime
    # a type and a constant of the same name do not clash (HOL
    # Light keeps them apart), so the two are looked at on their
    # own
    tykinds = ('type', 'tyabbrev')

    def istype(thy, nm):
      ks = [k for t, k in self.defs.get(nm, []) if t == thy]
      return bool(ks) and all(k in tykinds for k in ks)

    kept = {True: set(), False: set()}
    for nm, v in self.defs.items():
      for t, k in v:
        if (t, nm) not in self.rename:
          kept[k in tykinds].add(nm)
    taken = {True: {}, False: {}}
    for key in sorted(self.rename):
      ty = istype(*key)
      if key in overrides.RENAME:
        taken[ty][self.rename[key]] = key
        continue
      new = self.rename[key]
      while new in kept[ty] or new in taken[ty]:
        new += "'"
      self.rename[key] = new
      taken[ty][new] = key

  # ---------------------------------------------------------------

  # ---------------------------------------------------------------
  # which definitions of the HOL4 libraries the port needs
  # ---------------------------------------------------------------

  def compute_needed(self):
    # the names that each block defines, and the names it uses
    blocks = []                      # (thy, [names], set(uses))
    self.defining_block = {}         # (thy,name) -> block index
    for thy, path, kind in self.order:
      for b in hol4.parse(path):
        # phase two states the theorems of the CakeML sources, so
        # what their statements use is needed as well (the port of
        # a HOL4 library theory has the definitions that CakeML
        # needs, and mlstring's theorems need toto's TotOrd)
        if b.kind not in ('Datatype', 'Definition', 'Inductive',
                          'CoInductive', 'Type', 'Overload',
                          'Theorem', 'Triviality'):
          continue
        names = []
        if b.kind in ('Theorem', 'Triviality'):
          body = hol4.strip_comments(b.body or '')
          blocks.append((thy, [], set(re.findall(
            r"[A-Za-z][A-Za-z0-9_']*", body)), kind))
          continue
        if b.kind == 'Datatype':
          for ty, cons, flds in hol4.datatype_names(b.body):
            names += [ty] + cons + flds
        elif b.kind == 'Definition':
          names += definition_names(b.body, b.name)
        elif b.kind in ('Inductive', 'CoInductive'):
          # the rules of an inductive are implications, whose
          # conclusions name the relations (the peg_eval of HOL4's
          # pegTheory, which 67 statements of pegComplete read as
          # a variable because nothing said that the library layer
          # needs it)
          names += (definition_names(b.body) or
                    rule_names(b.body) or
                    ([b.name] if b.name else []))
        elif b.name:
          names.append(b.name)
        body = hol4.strip_comments(b.body) + \
               (hol4.strip_comments(b.extra) if b.extra else '')
        uses = set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", body))
        i = len(blocks)
        blocks.append((thy, names, uses, kind))
        for nm in names:
          if (thy, nm) not in self.defining_block:
            self.defining_block[(thy, nm)] = i
    # a name can be defined in several theories; index by name too
    byname = {}
    for i, (thy, names, _, kind) in enumerate(blocks):
      for nm in names:
        byname.setdefault(nm, []).append(i)
    needed = set(i for i, (thy, _, _, kind) in enumerate(blocks)
                 if kind == 'cakeml')
    # the definitions of a HOL4 library theory that the port needs
    # although no ported definition mentions them (because HOL4
    # generates what mentions them in ML)
    for thy, nm in overrides.ALSO_NEEDED:
      for j in byname.get(nm, []):
        if blocks[j][0] == thy:
          needed.add(j)
    stack = list(needed)
    while stack:
      i = stack.pop()
      thy, _, uses, _ = blocks[i]
      anc = self.ancestors(thy) | {thy}
      for nm in uses:
        for j in byname.get(nm, []):
          if j not in needed and blocks[j][0] in anc:
            needed.add(j); stack.append(j)
    self.needed_names = set()
    for i in needed:
      thy, names, _, _ = blocks[i]
      for nm in names:
        self.needed_names.add((thy, nm))

  def is_needed(self, thy, names):
    if any((thy, nm) in overrides.ALSO_NEEDED for nm in names):
      return True
    if self.kind_of_thy.get(thy) == 'lib' and \
       all(nm in self.provided for nm in names):
      return False
    return any(((thy, nm) in self.needed_names or
                (thy, nm) in overrides.ALSO_NEEDED) and
               (thy, nm) not in overrides.NOT_NEEDED for nm in names)

  def providers(self, thy, text, bound=()):
    """the ported theories that define a name the text uses; the
     needs of a file of the port are these, not only the ancestors
     that HOL4 lists (an ancestor provides what its own ancestors
     provide, which a file of the port does not)"""
    used = set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", text))
    rank = dict((t, i) for i, (t, _, _) in enumerate(self.order))
    anc = self.ancestors(thy) - {thy}
    over = self.overloaded()
    out = set()
    for nm in used:
      if nm in bound: continue
      # a name that this theory defines itself needs nothing, and
      # neither does one that the text would not write this way
      # (because the port renamed the constant)
      if any(t == thy for t, _ in self.defs.get(nm, [])): continue
      # a name can be defined in several theories; the one to take
      # is an ancestor, and otherwise the first one of the order
      ts = [t for t, _ in self.defs.get(nm, [])
            if t in self.thy_of_file and
               rank.get(t, 0) < rank.get(thy, 0) and
               (nm in over or self.rename.get((t, nm), nm) == nm)]
      if not ts: continue
      good = [t for t in ts if t in anc]
      out.add(min(good if good else ts, key=lambda t: rank[t]))
    return out

  def mlpath_of(self, thy):
    """where the port of a theory goes"""
    if self.kind_of_thy[thy] == 'lib':
      return 'lib/' + thy + '.ml'
    p = self.thy_of_file[thy]
    p = re.sub(r'^.*/cakeml-src/', '', p)
    return re.sub(r'Script\.sml$', '.ml', p)

  def gram_ancestors(self, thy):
    """the ancestors whose names the parser of a theory has: the
       ones of its Ancestors blocks and all of theirs, but not the
       ones that only an Ancestors[ignore_grammar] block brings.
       The grammar of an ancestor has the names of its own
       ancestors in it, so closLang's constructors are in the scope
       of clos_to_bvlProof (through closSem) although its
       ignore_grammar block names closLang, while
       clos_constantProof's parts is not: nothing else of the
       theory depends on it, and the statement that writes parts
       means a variable of its own (it writes the other names of
       that theory with the theory in front of them)"""
    ng = set(self.nogram.get(thy, []))
    out = {thy}
    for t in self.deps.get(thy, []):
      if t in ng: continue
      out |= self.ancestors(t)
    return out

  def scope(self, thy):
    """the theories whose names a theory can use without writing
       the theory in front of them: its ancestors, or, where the
       source restricts the grammar with set_grammar_ancestry,
       the theories that it names and their ancestors
       (backendProof's config is backend's, although compiler is
       an ancestor of it as well)"""
    g = overrides.GRAMMAR_ANCESTRY.get(thy)
    if not g: return self.ancestors(thy)
    out = {thy}
    for t in g: out |= self.ancestors(t)
    return out

  def distance(self, thy):
    """how far every ancestor of a theory is from it: the length of
       the shortest path of the Ancestors blocks.  A name that
       several theories define is the one of the closest of them
       (the Loc of data_to_word_gcProof is wordLang's, which is
       three steps away, and not semanticPrimitives', which is
       six), as HOL4 resolves it to the one of the theory that its
       own ancestry loads last"""
    if thy in self._dist: return self._dist[thy]
    out = {thy: 0}
    front = [thy]
    d = 0
    while front:
      d += 1
      nxt = []
      for t in front:
        for u in self.deps.get(t, []):
          if u not in out:
            out[u] = d; nxt.append(u)
      front = nxt
    self._dist[thy] = out
    return out

  def ancestors(self, thy):
    seen = set(); st = [thy]
    while st:
      t = st.pop()
      if t in seen: continue
      seen.add(t)
      st += self.deps.get(t, [])
    return seen

  def overloaded(self):
    """the names of the port's constants that HOL4 writes without a
       prefix: the port declares them as overloads of the constants
       it renamed, which is what HOL4 does with a name that several
       theories define (it resolves it by the type)"""
    if self._overloaded is not None: return self._overloaded
    tykinds = ('type', 'tyabbrev')
    out = set()
    for (thy, nm), new in self.rename.items():
      kinds = [k for t, k in self.defs.get(nm, []) if t == thy]
      if kinds and all(k in tykinds for k in kinds): continue
      # a name of the hand written library layer that stands for
      # a HOL4 theory (llist's fromList) is overloaded all the
      # same, because a ported theory may have a notion of that
      # name too (sptree's fromList) and HOL4 resolves the name
      # by the type; a name of the compatibility layer itself
      # (EVERY, ALL) and a name of HOL Light are not
      lib = nm in self.provided and self.provided_thy.get(nm)
      if nm in self.hl and not lib: continue
      if nm in self.provided and not lib: continue
      out.add(nm)
    self._overloaded = out
    return out

  def overloaded_for(self, thy):
    """the names that this theory writes without a prefix: the ones
       that more than one theory in its scope defines.  Where only
       one theory in scope has the name, HOL4 resolves it to that
       one, so the port writes the name of that constant"""
    anc = self.scope(thy) | {thy}
    tykinds = ('type', 'tyabbrev')
    out = set()
    for nm in self.overloaded():
      ts = set(t for t, k in self.defs.get(nm, [])
               if t in anc and k not in tykinds)
      if len(ts) > 1: out.add(nm)
    return out

  def hidden_for(self, thy, blocks):
    """the names that HOL4 reads as a variable in this theory, and
       that the port has as a constant: no theory in the scope of
       this one defines them (the unification library's vars is
       not in scope in data_to_word_memoryProof, which uses vars
       for a variable of its own), and HOL Light has no scope of
       its own to keep them apart.  The statements of the theory
       are read with these constants hidden; only the names that
       the statements of the source use are in the list.

       The test is the whole ancestry of the theory, and not the
       scope that a set_grammar_ancestry of the source restricts
       its grammar to: HOL4 reads a name that one ancestor
       defines as that constant, whether the grammar of the
       theory has it or not (backendProof restricts its grammar
       and uses closProps' obeys_max_app all the same)."""
    anc = self.gram_ancestors(thy)
    ids = set()
    for b in blocks:
      if b.kind in ('Theorem', 'Triviality'):
        ids |= set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", b.body or ''))
    out = set()
    for n in ids:
      # a constant that HOL4 hides from its parser is a variable
      # of a statement that writes it (overrides.HOL4_HIDDEN)
      if n in overrides.HOL4_HIDDEN:
        out.add(n); continue
      if n in self.hl or n in self.provided: continue
      ts = {t for t, k in self.defs.get(n, [])
            if k in ('def', 'con', 'rel')}
      if not ts or (ts & anc): continue
      # the port writes the name of the constant, so one that it
      # renamed hides nothing -- unless it overloads the bare name
      # with the constant it renamed, which puts the name back
      # (linear_scanProof's id is linear_scanProof_id and id is an
      # overload of it, so a statement of another theory that
      # writes id for a variable of its own reads the overload)
      if any(self.rename.get((t, n), n) == n for t in ts) or \
         n in self.overloaded():
        out.add(n)
    # a name that the accessors of a record field have as well is
    # not hidden: hiding it would take those with it, and only the
    # constant that the file cannot see is taken out of the
    # interface (ml/lib/theorem.ml's cake_hide_consts)
    flds = self.field_tokens()
    consts = []
    # only a constant that is there when the file loads can come
    # out of the interface, so a theory that comes after this one
    # in the load order is not in the list (closSem reads compile
    # for a variable of its own, and backend's compile is not
    # defined until forty files later)
    before = set()
    for t, _, _ in self.order:
      before.add(t)
      if t == thy: break
    for n in sorted(out & flds):
      ts = {t for t, k in self.defs.get(n, [])
            if k in ('def', 'con', 'rel')}
      for t in sorted((ts - anc) & before):
        consts.append((n, self.rename.get((t, n), n)))
    return sorted(out - flds), consts

  def field_tokens(self):
    """the names that the port overloads with the accessor or the
       update of a record field: the name of the field itself, or
       the name that HOL4 gives the accessor where every record
       that has the field is called the same (db.ambiguous_fields)
       -- and the _fupd of each"""
    if self._fldtoks is not None: return self._fldtoks
    out = set()
    for f, tok in self.ambiguous_fields().items():
      out |= {tok, tok + '_fupd'}
    for flds in self.recs.values():
      for f in flds: out |= {f, f + '_fupd'}
    self._fldtoks = out
    return out

  def types_in_scope(self, thy):
    """the names of every type and type abbreviation that a theory
       in the scope of this one defines, under the name that HOL4
       gives it and the one that the port gives it.  The parser
       needs them to see where a type that is not in parentheses
       ends: HOL4 reads ls:'a word_loc list as one type, and a
       name that is no type of its own ends it"""
    scope = self.scope(thy)
    out = set()
    for nm, v in self.defs.items():
      for t, k in v:
        if k in ('type', 'tyabbrev') and t in scope:
          out.add(nm)
          out.add(self.rename.get((t, nm), nm))
    return out

  def defnames_for(self, thy):
    """the names that a theory in the scope of this one defines as
       a constant of its own, which is what HOL4 reads such a name
       as (and not, where the name ends in _size, as the size
       function of a datatype of that name)"""
    anc = self.scope(thy) | {thy}
    return {nm for nm, v in self.defs.items()
            if any(t in anc and k in ('def', 'con', 'rel')
                   for t, k in v)}

  def names_for(self, thy, types=False):
    """the name mapping to use when translating theory thy; with
       types it is the mapping of the type names, which is a
       different one (a type and a constant can have the same name,
       as the type v and the constant v do)"""
    anc = self.scope(thy)
    tykinds = ('type', 'tyabbrev')
    out = {}
    for (t, nm), new in self.rename.items():
      kinds = [k for t2, k in self.defs.get(nm, []) if t2 == t]
      if types:
        if not any(k in tykinds for k in kinds): continue
      else:
        if kinds and all(k in tykinds for k in kinds): continue
      # a name that the hand written library layer provides keeps
      # its meaning where it stands on its own; the renamed
      # constant of the theory is reached by its own name
      # (llist's fromList is the one that a bare fromList means,
      # sptree's is sptree_fromList)
      if (t in anc or t == thy) and nm not in self.provided:
        out[nm] = new
      out[(t, nm)] = new
    # a constant that is renamed where the type of the same name
    # is not
    if not types:
      for (t, nm), new in overrides.RENAME_CONST.items():
        if t in anc or t == thy: out[nm] = new
        out[(t, nm)] = new
    return out

  def con_arity(self, thy, con):
    """how many arguments a constructor of a theory takes"""
    n = 0
    while (thy, con, n) in self.con_argty_thy: n += 1
    return n

  def ambiguous_fields(self):
    """the record fields that more than one record type of the port
       has, and the name that the port overloads their accessors
       with.  HOL4 resolves such a field by the type of the record,
       so HOL Light has to resolve it the same way.  Where the
       record types all have the same name in HOL4 (the state of
       every intermediate language) the overload is the name that
       HOL4 gives the accessor (state_clock); otherwise it is the
       name of the field itself"""
    if self._ambflds is not None: return self._ambflds
    out = collections.defaultdict(set)
    for (t, ty), flds in self.recs.items():
      for f in flds:
        out[f].add((t, ty))
    self._ambflds = {}
    for f, tys in out.items():
      if len(tys) < 2 or f in overrides.FIELD_DEFAULT: continue
      names = set(ty for _, ty in tys)
      self._ambflds[f] = (names.pop() + '_' + f if len(names) == 1
                          else f)
    return self._ambflds

  def fields_for(self, thy):
    """field name -> record type, for the records in scope"""
    anc = self.scope(thy) | {thy}
    out = {}; amb = collections.defaultdict(list)
    for (t, ty), flds in self.recs.items():
      if t not in anc: continue
      name = self.rename.get((t, ty), ty)
      for f in flds:
        amb[f].append(name)
    for f, tys in amb.items():
      out[f] = (tys[0] if len(set(tys)) == 1
                else overrides.FIELD_DEFAULT.get(f))
    return out, {f: tys for f, tys in amb.items() if len(set(tys)) > 1}

  def cons_for(self, thy):
    """the constructor names in scope, as the CakeML sources write them"""
    anc = self.scope(thy) | {thy}
    out = set(['NONE', 'SOME', 'NIL', 'CONS', 'INL', 'INR', 'T', 'F',
               'LN', 'LS', 'BN', 'BS'])
    for (t, ty), (cons, flds) in self.datatypes.items():
      if t in anc: out |= set(cons)
    return out

  def recs_for(self, thy):
    anc = self.scope(thy) | {thy}
    return {self.rename.get((t, ty), ty): flds
            for (t, ty), flds in self.recs.items() if t in anc}

  def rectys_for(self, thy):
    """the type of every field of every record in scope, by the
       name that the port gives the record type (a numeral beside
       an element of a field that holds integers is &n)"""
    anc = self.scope(thy) | {thy}
    return {self.rename.get((t, ty), ty): ftys
            for (t, ty), ftys in self.rectys.items() if t in anc}

  def con_argty_for(self, thy):
    """the type of the argument of a constructor, as far as the
       theories in scope agree on it (the numerals of an argument
       whose type is int or real are written &n)"""
    anc = self.scope(thy) | {thy}
    out = {}
    for (t, con, j), ty in self.con_argty_thy.items():
      if t not in anc: continue
      k = (con, j)
      if k in out and out[k] != ty: out[k] = None
      else: out.setdefault(k, ty)
    return {k: v for k, v in out.items() if v is not None}

  def overloads_for(self, thy):
    """the overloads in scope: the local ones only in their own theory"""
    anc = self.scope(thy)
    return {nm: txt for (t, nm), (txt, local) in self.overloads.items()
            if t == thy or (t in anc and not local)}

  def overload_thy_for(self, thy):
    """the theory that declares every overload in the scope of this
       one: the body of an overload is read in the context of that
       theory, where the record field that it mentions is the one
       that HOL4 means (labSem's read_reg is s.regs of a labSem
       state, also in a theory that has stackSem's regs in scope)"""
    anc = self.scope(thy)
    rank = {t: i for i, (t, _, _) in enumerate(self.order)}
    out = {}
    for (t, nm), (txt, local) in self.overloads.items():
      if not (t == thy or (t in anc and not local)): continue
      if nm not in out or rank.get(t, -1) > rank.get(out[nm], -1):
        out[nm] = t
    return out

  def abbrevs_for(self, thy):
    anc = self.scope(thy) | {thy}
    rank = {t: i for i, (t, _, _) in enumerate(self.order)}
    # HOL4's 'a set is HOL Light's A->bool
    out = {'set': (["'a"], hterm.parse_type_text("'a -> bool"))}
    for (t, nm), (params, txt) in self.abbrevs.items():
      if t not in anc: continue
      ty = hterm.parse_type_text(txt)
      # a CakeML source may qualify the name (sptree$num_map)
      out[t + '$' + nm] = (params, ty)
      # a theory that comes after the one of the abbreviation and
      # has a datatype of that name means its own type, not the
      # abbreviation (data_to_word_memoryProof's tag is a
      # datatype of its own, and bvl's tag is num)
      if any(t2 in anc and rank.get(t2, -1) > rank.get(t, -1)
             for (t2, ty2) in self.datatypes if ty2 == nm):
        continue
      out[nm] = (params, ty)
    return out


def definition_names(body, name=None):
  """the constants that a Definition block defines, from its term.
     Where the term does not parse as a clause of them, the name
     that the text gives is taken, as far as the name of the block
     says it is the one (HOL4 reads the = of mw_ok xs = ~(xs = [])
     ==> ~(LAST xs = 0w) as the one of the definition, and the
     parser of the port as the one of the antecedent)"""
  try:
    toks = hterm.tokenize(hol4.strip_comments(body))
    e = hterm.Parser(toks).parse()
  except Exception:
    return hol4.definition_names(body)
  out = []
  def conjuncts(e):
    if e.kind == 'infix' and e.op in ('/\\', '\\/') and e.op == '/\\':
      return conjuncts(e.l) + conjuncts(e.r)
    if e.kind == 'paren': return conjuncts(e.e)
    if e.kind == 'quant' and e.q == '!': return conjuncts(e.body)
    return [e]
  for cl in conjuncts(e):
    while cl.kind in ('paren',):
      cl = cl.e
    if cl.kind == 'quant' and cl.q == '!':
      cl = cl.body
      while cl.kind == 'paren': cl = cl.e
    if cl.kind != 'infix' or cl.op not in ('=', '<=>'): continue
    hop = hterm.head_of(cl.l)
    if hop.kind == 'id' and hop.name not in out:
      out.append(hop.name)
  if not out and name:
    out = [n for n in hol4.definition_names(body)
           if n == name or name.startswith(n + '_')]
  return out


def rule_names(body):
  """the relations that the rules of an Inductive block define:
     the head of the conclusion of every rule (definition_names
     only sees the clauses that are equations)"""
  try:
    toks = hterm.tokenize(hol4.strip_comments(body))
    e = hterm.Parser(toks).parse()
  except Exception:
    return []
  out = []

  def conjuncts(e):
    if e.kind == 'infix' and e.op == '/\\':
      return conjuncts(e.l) + conjuncts(e.r)
    if e.kind == 'paren': return conjuncts(e.e)
    if e.kind == 'quant' and e.q == '!': return conjuncts(e.body)
    return [e]

  for cl in conjuncts(e):
    while cl.kind == 'paren': cl = cl.e
    if cl.kind == 'quant' and cl.q == '!':
      cl = cl.body
      while cl.kind == 'paren': cl = cl.e
    while cl.kind == 'infix' and cl.op == '==>':
      cl = cl.r
      while cl.kind == 'paren': cl = cl.e
    try:
      hop = hterm.head_of(cl)
    except Exception:
      continue
    if hop.kind == 'id' and hop.name not in out:
      out.append(hop.name)
  return out


def prefix(thy, nm):
  return nm if thy == nm else thy + '_' + nm


def strip_quote(s):
  """the contents of the first quotation of a block (what follows it,
     a comment or ML code, is not part of it)"""
  s = s.strip()
  for a, b in [('``', '``'), ('“', '”'), ('‘', '’'),
               ('`', '`')]:
    if s.startswith(a):
      s = s[len(a):]
      k = s.find(b)
      if k >= 0: s = s[:k]
      break
  s = s.strip()
  if s.startswith(':'): s = s[1:]
  return s.strip()


if __name__ == '__main__':
  db = Db()
  print('names', len(db.defs), 'renamed', len(db.rename))
  print('datatypes', len(db.datatypes), 'records', len(db.recs),
        'abbrevs', len(db.abbrevs))
  f, amb = db.fields_for('evaluate')
  print('ambiguous fields in evaluate:', amb)
  print('clock ->', f.get('clock'))
  print(sorted(set(db.rename.values()))[:20])
