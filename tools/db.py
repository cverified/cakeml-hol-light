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
import hol4, hterm, overrides

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


def hl_names():
  return set(l.strip() for l in open(T + 'hl-names.txt') if l.strip())


# the hand written files of the library layer
HANDWRITTEN = ['hol4.ml', 'words4.ml', 'finite_map.ml', 'llist.ml']


def provided_names():
  """the HOL4 library constants that the hand written files of
     ml/lib provide"""
  s = ''.join(open(T + '../ml/lib/' + f).read() for f in HANDWRITTEN)
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


class Db:
  def __init__(self):
    self.order = load_order()
    self.hl = hl_names()
    self.provided = provided_names()
    self.read_fixities()
    self.deps = json.load(open(T + 'deps.json'))['deps']
    self.defs = collections.defaultdict(list)   # name -> [(thy,kind)]
    self.datatypes = {}        # (thy,ty) -> ([cons],[fields])
    self.recs = {}             # (thy,ty) -> [fields]
    self.abbrevs = {}          # (thy,name) -> (params, type text)
    self.overloads = {}        # (thy,name) -> term text
    self.con_argty = {}        # (constructor,index) -> {type texts}
    self.con_argty_thy = {}    # (thy,constructor,index) -> type text
    self._overloaded = None
    self.ty_params = {}        # (thy,type) -> the type parameters
    self.monads = {'option': {'bind': 'OPTION_BIND',
                              'unit': 'SOME',
                              'ignorebind': 'OPTION_IGNORE_BIND'}}
    self.thy_of_file = {}
    self.kind_of_thy = {}
    self.scan()
    self.mapping()
    self.compute_needed()

  # ---------------------------------------------------------------

  def read_fixities(self):
    """the infixes that each source declares itself"""
    self.fix = {}
    self.ovl_infix = {}  # a symbolic infix -> the constant it means
    for thy, path, kind in self.order:
      try:
        text = open(path, encoding='utf-8').read()
      except Exception:
        text = ''
      self.fix[thy] = hol4.fixities(text)

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

  def scan(self):
    for thy, path, kind in self.order:
      self.thy_of_file[thy] = path
      self.kind_of_thy[thy] = kind
      self.base_grammar(thy)
      for b in hol4.parse(path):
        mode = hol4.equality_mode(b.text) if b.kind == 'ML' else None
        if mode: hterm.set_equality(mode == 'loose')
        if b.kind == 'ML':
          for tok, prec, ass, _ in hol4.fixities(b.text):
            hterm.add_infix(tok, prec, ass)
          if hol4.pmatch_mode(b.text): hterm.enable_pmatch(True)
        if (b.kind == 'Overload' and b.name and
            not b.name[0].isalpha()):
          self.ovl_infix[b.name] = strip_quote(b.body).strip()
        if b.kind == 'Ancestors':
          anc = [w for w in b.body.split()]
          self.deps[thy] = sorted(set(self.deps.get(thy, []) + anc))
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
        elif b.kind == 'Definition':
          for nm in definition_names(b.body):
            self.defs[nm].append((thy, 'def'))
        elif b.kind in ('Inductive', 'CoInductive'):
          for nm in definition_names(b.body):
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

  # ---------------------------------------------------------------

  def mapping(self):
    """compute the HOL4 -> HOL Light name mapping"""
    multi = {nm for nm, v in self.defs.items()
             if len({t for t, _ in v}) > 1}
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
        if b.kind not in ('Datatype', 'Definition', 'Inductive',
                          'CoInductive', 'Type', 'Overload'):
          continue
        names = []
        if b.kind == 'Datatype':
          for ty, cons, flds in hol4.datatype_names(b.body):
            names += [ty] + cons + flds
        elif b.kind in ('Definition', 'Inductive', 'CoInductive'):
          names += definition_names(b.body)
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
      if nm in self.hl or nm in self.provided: continue
      out.add(nm)
    self._overloaded = out
    return out

  def names_for(self, thy, types=False):
    """the name mapping to use when translating theory thy; with
       types it is the mapping of the type names, which is a
       different one (a type and a constant can have the same name,
       as the type v and the constant v do)"""
    anc = self.ancestors(thy)
    tykinds = ('type', 'tyabbrev')
    out = {}
    for (t, nm), new in self.rename.items():
      kinds = [k for t2, k in self.defs.get(nm, []) if t2 == t]
      if types:
        if not any(k in tykinds for k in kinds): continue
      else:
        if kinds and all(k in tykinds for k in kinds): continue
      if t in anc or t == thy:
        out[nm] = new
      out[(t, nm)] = new
    return out

  def fields_for(self, thy):
    """field name -> record type, for the records in scope"""
    anc = self.ancestors(thy) | {thy}
    out = {}; amb = collections.defaultdict(list)
    for (t, ty), flds in self.recs.items():
      if t not in anc: continue
      name = self.rename.get((t, ty), ty)
      for f in flds:
        amb[f].append(name)
    for f, tys in amb.items():
      out[f] = tys[0] if len(set(tys)) == 1 else None
    return out, {f: tys for f, tys in amb.items() if len(set(tys)) > 1}

  def cons_for(self, thy):
    """the constructor names in scope, as the CakeML sources write them"""
    anc = self.ancestors(thy) | {thy}
    out = set(['NONE', 'SOME', 'NIL', 'CONS', 'INL', 'INR', 'T', 'F',
               'LN', 'LS', 'BN', 'BS'])
    for (t, ty), (cons, flds) in self.datatypes.items():
      if t in anc: out |= set(cons)
    return out

  def recs_for(self, thy):
    anc = self.ancestors(thy) | {thy}
    return {self.rename.get((t, ty), ty): flds
            for (t, ty), flds in self.recs.items() if t in anc}

  def con_argty_for(self, thy):
    """the type of the argument of a constructor, as far as the
       theories in scope agree on it (the numerals of an argument
       whose type is int or real are written &n)"""
    anc = self.ancestors(thy) | {thy}
    out = {}
    for (t, con, j), ty in self.con_argty_thy.items():
      if t not in anc: continue
      k = (con, j)
      if k in out and out[k] != ty: out[k] = None
      else: out.setdefault(k, ty)
    return {k: v for k, v in out.items() if v is not None}

  def overloads_for(self, thy):
    """the overloads in scope: the local ones only in their own theory"""
    anc = self.ancestors(thy)
    return {nm: txt for (t, nm), (txt, local) in self.overloads.items()
            if t == thy or (t in anc and not local)}

  def abbrevs_for(self, thy):
    anc = self.ancestors(thy) | {thy}
    # HOL4's 'a set is HOL Light's A->bool
    out = {'set': (["'a"], hterm.parse_type_text("'a -> bool"))}
    for (t, nm), (params, txt) in self.abbrevs.items():
      if t in anc:
        out[nm] = (params, hterm.parse_type_text(txt))
    return out


def definition_names(body):
  """the constants that a Definition block defines, from its term"""
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
