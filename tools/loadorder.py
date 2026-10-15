"""the files of the port in an order in which every file comes after
   the ones that it needs, so that loading them one after the other
   loads each of them once"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod

db = dbmod.Db()
files = [db.mlpath_of(thy) for thy, _, _ in dbmod.load_order()]
deps = {}
for f in files:
  text = open('ml/' + f).read()
  deps[f] = [m for m in re.findall(r'needs "([^"]*)";;', text)
             if m in files]
out, seen, path = [], set(), set()


def visit(f):
  if f in seen: return
  if f in path: raise SystemExit('cycle at ' + f)
  path.add(f)
  for d in deps[f]: visit(d)
  path.discard(f)
  seen.add(f); out.append(f)


for f in files: visit(f)
print('\n'.join(out))
