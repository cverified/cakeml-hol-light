"""print the HOL4 source of a definition of the port: the block
   as it stands in the CakeML or HOL4 file, with its Termination
   if it has one.

     python3 -I tools/source.py <name>...

   A name is the one of a constant of the port (the port's name
   or HOL4's).
"""
import sys, os, re
C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, C + '/tools')
import db as dbmod, hol4

db = dbmod.Db()
# the HOL4 name of a constant that the port renamed
back = {}
for (thy, nm), new in db.rename.items():
  back.setdefault(new, (thy, nm))

for arg in sys.argv[1:]:
  thy, nm = back.get(arg, (None, arg))
  thys = [thy] if thy else [t for t, k in db.defs.get(nm, [])]
  if not thys:
    print('%s: nothing of the sources defines it' % arg); continue
  for t in thys:
    path = db.thy_of_file.get(t)
    if not path: continue
    found = False
    for b in hol4.parse(path):
      if b.kind not in ('Definition', 'Inductive', 'CoInductive'):
        continue
      if nm not in dbmod.definition_names(b.body): continue
      found = True
      print('=== %s (%s)' % (nm, path.replace(C + '/', '')))
      print(b.text.strip()[:2000])
      if b.extra and b.extra.strip():
        print('--- Termination:')
        print(b.extra.strip()[:600])
    if not found:
      print('%s: no Definition block in %s' % (nm, t))
