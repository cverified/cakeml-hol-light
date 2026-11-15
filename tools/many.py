"""port several theories into a scratch directory in one pass

  python3 -I tools/many.py <dir> <theory>...

(with no theory names, every theory of the load order).  The port
of a theory depends on what the port of its ancestors made of
them, so the whole order is walked and only the ones that are
asked for are written."""
import sys, os
T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, port as portmod
if not sys.argv[1:]:
  print(__doc__); sys.exit(0)
out = sys.argv[1].rstrip('/') + '/'
want = set(sys.argv[2:])
portmod.ML = out
portmod.check_no_run = lambda: None
db = dbmod.Db()
left = set(want)
for thy, path, kind in dbmod.load_order():
  if want and thy not in want:
    try: portmod.port(thy, db)
    except Exception: pass
    continue
  try:
    p, warn, amb = portmod.port(thy, db)
    bad = open(p).read().count('PORT FAILED')
    print('wrote %-28s %s' % (thy, 'PORT FAILED %d' % bad if bad else ''))
  except Exception as e:
    print('FAILED %-28s %s' % (thy, e))
  left.discard(thy)
  if want and not left: break
for thy in sorted(left): print('not in the load order:', thy)
