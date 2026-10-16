"""say where a name comes from: which HOL4 theory defines it,
   whether the port has that theory, and what the port calls it.

     python3 -I tools/whereis.py <name>...

   For a constant that a cheat of ml/CHEATS.md misses, this says
   whether the port has to take another library theory, or
   whether HOL Light has the notion under another name.
"""
import sys, os
C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, C + '/tools')
import db as dbmod

db = dbmod.Db()
ported = {t for t, _, _ in dbmod.load_order()}
import re, subprocess


def search(nm):
  """where a HOL4 source outside the port defines the name"""
  pats = [r'Definition\s+%s(_def)?\b' % nm,
          r'Inductive\s+%s\b' % nm,
          r'val\s+%s(_def)?\s*=' % nm,
          r'\(%s_rules' % nm,
          r'Overload\s+%s\b' % nm,
          r'Theorem\s+%s(_def)?\b' % nm]
  out = []
  for tree in (C + '/hol4-src', C + '/cakeml-src'):
    if not os.path.isdir(tree): continue
    try:
      r = subprocess.run(['grep', '-rnE', '|'.join(pats), tree],
                         capture_output=True, text=True,
                         timeout=120)
    except Exception:
      continue
    for l in r.stdout.split('\n')[:400]:
      if l.strip(): out.append(l.replace(C + '/', ''))
  return out


for nm in sys.argv[1:]:
  v = db.defs.get(nm)
  if not v:
    print('%-28s nothing of the ported sources defines it' % nm)
    if nm in db.hl: print('%-28s   (HOL Light has it)' % '')
    for l in search(nm)[:6]:
      print('%-28s   %s' % ('', l[:100]))
    continue
  for thy, kind in v:
    print('%-28s %-8s %-22s %s' %
          (nm, kind, thy,
           'ported' if thy in ported else 'NOT ported'))
    f = db.thy_of_file.get(thy)
    if f and thy not in ported:
      print('%-28s   %s' % ('', f.replace(C + '/', '')))
  new = db.rename.get((v[0][0], nm))
  if new: print('%-28s   the port calls it %s' % ('', new))
