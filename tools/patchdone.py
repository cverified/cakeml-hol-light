"""say which THM_PATCH and DEF_PATCH entries left no trace

  python3 -I tools/patchdone.py

A patch whose text does not match is an error that the port
reports, but a patch whose *key* names no block of the source is
silent: tools/overrides.py keys a THM_PATCH by the name the HOL4
source gives the theorem, not by the binding the port writes, and
the two differ whenever two files state a theorem of one name
(lab_to_targetProof's `Inst_lemma` is the port's `inst_lemma`).
Such an entry does nothing at all and the statement stays wrong.

This reads the ported files and says, of every patch, whether the
text it puts in is there.  A `no trace` line is an entry to look
at: either the key is wrong or the patch is dead.
"""
import os, sys
T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import overrides, db as dbmod

ML = T + '../ml/'
db = dbmod.Db()
text = {}
for thy, _, _ in dbmod.load_order():
  try:
    text[thy] = open(ML + db.mlpath_of(thy)).read()
  except IOError:
    pass
bad = 0
for table, name in ((overrides.THM_PATCH, 'THM_PATCH'),
                    (overrides.DEF_PATCH, 'DEF_PATCH')):
  for (thy, nm), pairs in sorted(table.items()):
    if thy not in text: continue
    if not isinstance(pairs, list): continue
    for old, new in pairs:
      if ' '.join(new.split()) not in ' '.join(text[thy].split()):
        print('%-10s %-26s %-22s no trace of %s'
              % (name, thy, nm, new[:40]))
        bad += 1
        break
print('%d patch entries, %d that left no trace'
      % (sum(len(v) for t in (overrides.THM_PATCH, overrides.DEF_PATCH)
             for v in [t] for v in []) or
         sum(1 for t in (overrides.THM_PATCH, overrides.DEF_PATCH)
             for _ in t), bad))
