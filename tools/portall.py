"""port every theory of the load order (the HOL4 library theories
   of ml/lib as well) into ml/"""
import sys, os, re, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod, port as portmod

db = dbmod.Db()
t0 = time.time()
n = bad = 0
T = os.path.dirname(os.path.abspath(__file__))
# every doubt that the translation of a theory has, so that the
# whole port's are in one place (tools/warnings.txt)
out = open(T + '/warnings.txt', 'w')
kinds = {}
for thy, path, kind in dbmod.load_order():
  p, warn, amb = portmod.port(thy, db)
  n += 1
  k = open(p).read().count('PORT FAILED')
  bad += k
  if k: print('%-24s %d PORT FAILED' % (thy, k))
  for w in warn:
    out.write('%s\t%s\n' % (thy, w.replace('\n', ' ')))
    key = re.sub(r'[^a-z ].*', '', w.split(':')[0]).strip() or w[:20]
    kinds[key] = kinds.get(key, 0) + 1
out.close()
# the preface of a file says which files need it, which is only
# known when every file has its needs
import preface
preface.main()
print(n, 'files,', bad, 'PORT FAILED, %.1fs' % (time.time() - t0))
print('warnings in tools/warnings.txt:')
for k, v in sorted(kinds.items(), key=lambda kv: -kv[1])[:12]:
  print('%6d  %s' % (v, k))
