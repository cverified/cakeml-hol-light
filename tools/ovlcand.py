"""the overloaded names of a statement, with their candidates

  python3 -I tools/ovlcand.py <theory> <name>...
  python3 -I tools/ovlcand.py --unstated

HOL Light resolves a name that several constants of the port have
by the type, and says "overload resolution" when no assignment of
constants to the names of a statement fits.  Which names those can
be is what this says: every name of the statement that the port
overloads, with the constants that the name stands for and the
file that overloads it.  A name with many candidates is where to
look first, and a name with exactly one is where the port has lost
the overload that HOL4 has.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, thmcheck

ML = T + '../ml/'
OVL = re.compile(r'hol4_(?:field_)?overload\s*\n?\s*"([^"]+)"\s*\n?\s*'
                 r'"([^"]+)"')


def overloads():
  """token -> [(constant, the file that overloads it)]"""
  out = collections.defaultdict(list)
  for dp, _, fs in os.walk(ML):
    for f in sorted(fs):
      if not f.endswith('.ml'): continue
      p = os.path.join(dp, f)
      for m in OVL.finditer(open(p).read()):
        out[m.group(1)].append((m.group(2), os.path.relpath(p, ML)))
  return out


def main():
  if not sys.argv[1:]:
    print(__doc__); return
  ovl = overloads()
  want = []
  if sys.argv[1] == '--unstated':
    names = set()
    for l in open(T + '../tmp/unstated.txt'):
      if '\t' in l: names.add(l.split('\t')[0])
    for dp, _, fs in os.walk(ML):
      for f in sorted(fs):
        if not f.endswith('.ml'): continue
        p = os.path.join(dp, f)
        for nm, line, stmt in thmcheck.statements(p):
          if re.sub(r'\[.*', '', nm) in names:
            want.append((os.path.relpath(p, ML), nm, stmt))
  else:
    db = dbmod.Db()
    thy = sys.argv[1]
    keep = set(sys.argv[2:])
    f = db.mlpath_of(thy)
    for nm, line, stmt in thmcheck.statements(ML + f):
      if not keep or re.sub(r'\[.*', '', nm) in keep:
        want.append((f, nm, stmt))
  for f, nm, stmt in want:
    ids = sorted(set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", stmt)))
    rows = [(i, ovl[i]) for i in ids if i in ovl]
    print('--- %s %s' % (f, nm))
    for i, cands in sorted(rows, key=lambda r: -len(r[1])):
      print('  %-24s %s' % (i, ', '.join(c for c, _ in cands)[:110]))


if __name__ == '__main__':
  main()
