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
  """the theories to port: the HOL4 libraries first, then CakeML"""
  libs = [(l.split('\t')[0], HOL4 + l.split('\t')[1].strip(), 'lib')
          for l in open(T + 'libs.txt').read().split('\n') if l]
  cake = [(l.split('\t')[0], SRC + l.split('\t')[1].strip(), 'cakeml')
          for l in open(T + 'order.txt').read().split('\n') if l]
  return libs + cake


def hl_names():
  return set(l.strip() for l in open(T + 'hl-names.txt') if l.strip())


def provided_names():
  """the HOL4 library constants that ml/lib/hol4.ml provides"""
  s = open(T + '../ml/lib/hol4.ml').read()
  names = set()
  for m in re.finditer(r'new_(?:recursive_)?definition\b[^`]*`([^`]*)`',
                       s):
    for cl in re.split(r'/\\\\', m.group(1)):
      mm = re.match(r"\s*\(?\s*([A-Za-z_][A-Za-z0-9_']*)", cl)
      if mm: names.add(mm.group(1))
  for m in re.finditer(r'override_interface\("([^"]+)"', s):
    names.add(m.group(1))
  return names


class Db:
  def __init__(self):
    self.order = load_order()
    self.hl = hl_names()
    self.provided = provided_names()
    self.deps = json.load(open(T + 'deps.json'))['deps']
    self.defs = collections.defaultdict(list)   # name -> [(thy,kind)]
    self.datatypes = {}        # (thy,ty) -> ([cons],[fields])
    self.recs = {}             # (thy,ty) -> [fields]
    self.abbrevs = {}          # (thy,name) -> (params, type text)
    self.overloads = {}        # (thy,name) -> term text
    self.thy_of_file = {}
    self.kind_of_thy = {}
    self.scan()
    self.mapping()
    self.compute_needed()

  # ---------------------------------------------------------------

  def scan(self):
    for thy, path, kind in self.order:
      self.thy_of_file[thy] = path
      self.kind_of_thy[thy] = kind
      for b in hol4.parse(path):
        if b.kind == 'Ancestors':
          anc = [w for w in b.body.split()]
          self.deps[thy] = sorted(set(self.deps.get(thy, []) + anc))
        if b.kind == 'Datatype':
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
          txt = strip_quote(b.body)
          try:
            ty = hterm.parse_type_text(txt)
          except Exception:
            continue
          if not b.name: continue
          params = hterm.type_vars_of(ty)
          self.abbrevs[(thy, b.name)] = (params, txt)
          self.defs[b.name].append((thy, 'tyabbrev'))
        elif b.kind == 'ML':
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
    return any((thy, nm) in self.needed_names and
               (thy, nm) not in overrides.NOT_NEEDED for nm in names)

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

  def names_for(self, thy):
    """the name mapping to use when translating theory thy"""
    anc = self.ancestors(thy)
    out = {}
    for (t, nm), new in self.rename.items():
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
  s = s.strip()
  for a, b in [('``', '``'), ('“', '”'), ('‘', '’'),
               ('`', '`')]:
    if s.startswith(a):
      s = s[len(a):]
      if s.endswith(b): s = s[:-len(b)]
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
