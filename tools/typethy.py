"""check that the type of every constant of the port only mentions
   types of theories that the HOL4 source of its own theory has as
   an ancestor.  A constant whose type mentions another one got an
   overloaded name of a theory that is not in its scope (wordSem's
   add_ret_loc with flatSem's Loc in it), which is a silent error
   of the port: the definition typechecks, but says something else
   than the HOL4 source does.

     tools/bin/types [session]
"""
import sys, os, re

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, C + '/tools')
import db as dbmod

db = dbmod.Db()

# the HOL Light name of a constant or a type -> the theory it is of
# (the name that the port gives it, which is the name of the source
# where the port does not rename it: a check that only looked at
# the renamed ones left nine constants out of ten)
TYKINDS = ('type', 'tyabbrev')
const_thy = {}
type_thy = {}
for thy, path, kind in dbmod.load_order():
  names = db.names_for(thy)
  tynames = db.names_for(thy, True)
  for nm, ks in db.defs.items():
    kinds = [k for t, k in ks if t == thy]
    if not kinds: continue
    if not all(k in TYKINDS for k in kinds):
      const_thy.setdefault(names.get((thy, nm), nm), thy)
    if any(k in TYKINDS for k in kinds):
      type_thy.setdefault(tynames.get((thy, nm), nm), thy)

bad = []
for line in open(C + '/tmp/consts.txt'):
  if '\t' not in line: continue
  name, ty = line.rstrip('\n').split('\t', 1)
  thy = const_thy.get(name)
  if not thy: continue
  anc = db.ancestors(thy) | {thy}
  for t in sorted(set(re.findall(r"(?<!')\b[A-Za-z][A-Za-z0-9_']*",
                                 ty))):
    t2 = type_thy.get(t)
    if t2 and t2 not in anc:
      bad.append((thy, name, t, t2, ty))
      break
for thy, name, t, t2, ty in bad:
  print('%-20s %-28s %s of %s\n    %s' % (thy, name, t, t2, ty[:70]))
print(len(bad), 'constants whose type is outside the scope of their '
      'theory')
