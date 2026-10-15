"""port every theory of the load order (the HOL4 library theories
   of ml/lib as well) into ml/"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod, port as portmod

db = dbmod.Db()
t0 = time.time()
n = bad = 0
for thy, path, kind in dbmod.load_order():
  p, warn, amb = portmod.port(thy, db)
  n += 1
  k = open(p).read().count('PORT FAILED')
  bad += k
  if k: print('%-24s %d PORT FAILED' % (thy, k))
print(n, 'files,', bad, 'PORT FAILED, %.1fs' % (time.time() - t0))
