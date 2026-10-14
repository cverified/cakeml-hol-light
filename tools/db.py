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
import hol4, hterm

T = os.path.dirname(os.path.abspath(__file__)) + '/'
SRC = hol4.SRC

# theories that HOL Light provides itself, or that the port
# provides in ml/lib; the name is the HOL Light name
BUILTIN = {}


def load_order():
  return [tuple(l.split('\t'))
          for l in open(T + 'order.txt').read().split('\n') if l]


def hl_names():
  return set(l.strip() for l in open(T + 'hl-names.txt') if l.strip())


class Db:
  def __init__(self):
    self.order = load_order()
    self.hl = hl_names()
    self.deps = json.load(open(T + 'deps.json'))['deps']
    self.defs = collections.defaultdict(list)   # name -> [(thy,kind)]
    self.datatypes = {}        # (thy,ty) -> ([cons],[fields])
    self.recs = {}             # (thy,ty) -> [fields]
    self.abbrevs = {}          # (thy,name) -> (params, type text)
    self.thy_of_file = {}
    self.scan()
    self.mapping()

  # ---------------------------------------------------------------

  def scan(self):
    for thy, rel in self.order:
      rel = rel.strip()
      self.thy_of_file[thy] = rel
      for b in hol4.parse(SRC + rel):
        if b.kind == 'Datatype':
          for ty, cons, flds in hol4.datatype_names(b.body):
            self.datatypes[(thy, ty)] = (cons, flds)
            self.defs[ty].append((thy, 'type'))
            for c in cons: self.defs[c].append((thy, 'con'))
            if flds:
              self.recs[(thy, ty)] = flds
        elif b.kind == 'Definition':
          for nm in hol4.definition_names(b.body):
            self.defs[nm].append((thy, 'def'))
        elif b.kind in ('Inductive', 'CoInductive'):
          for nm in hol4.definition_names(b.body):
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
        elif b.kind == 'Overload':
          if b.name:
            self.defs[b.name].append((thy, 'overload'))

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
        if nm in multi or nm in self.hl:
          self.rename[(thy, nm)] = prefix(thy, nm)

  # ---------------------------------------------------------------

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

  def recs_for(self, thy):
    anc = self.ancestors(thy) | {thy}
    return {self.rename.get((t, ty), ty): flds
            for (t, ty), flds in self.recs.items() if t in anc}

  def abbrevs_for(self, thy):
    anc = self.ancestors(thy) | {thy}
    out = {}
    for (t, nm), (params, txt) in self.abbrevs.items():
      if t in anc:
        out[nm] = (params, hterm.parse_type_text(txt))
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
