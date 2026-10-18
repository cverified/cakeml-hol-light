"""what a change to the translation changes in the port

  python3 -I tools/dryport.py <directory>

ports every theory of the load order into that directory (which it
makes if it is not there) and says which files of `ml/` would
differ and by how many lines.  So a change to the translation is
seen before it is written into `ml/`, which is what to use while a
run is going: nothing may write into `ml/` then
(`tools/bin/trydef`, `tools/bin/tryport`, this).
"""
import sys, os, difflib

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, port as portmod


def main():
  if not sys.argv[1:]:
    print(__doc__); return 0
  out = sys.argv[1].rstrip('/') + '/'
  real = portmod.ML
  portmod.ML = out
  # the port of a scratch directory writes nothing into ml/, so a
  # run of checkseq is no reason not to
  portmod.check_no_run = lambda: None
  db = dbmod.Db()
  n = bad = 0
  for thy, path, kind in dbmod.load_order():
    try:
      p, warn, amb = portmod.port(thy, db)
    except Exception as e:
      print('%-24s FAILED %s' % (thy, e))
      bad += 1
      continue
    n += 1
    if open(p).read().count('PORT FAILED'):
      print('%-24s PORT FAILED' % thy)
      bad += 1
  # the preface of a file says which files need it, which is only
  # known when every file has its needs
  import preface
  preface.main()
  diff = []
  for thy, path, kind in dbmod.load_order():
    try:
      old = open(real + db.mlpath_of(thy)).read()
      new = open(out + db.mlpath_of(thy)).read()
    except OSError:
      continue
    if old == new: continue
    d = [l for l in difflib.unified_diff(old.split('\n'),
                                         new.split('\n'), n=0)
         if l[:1] in '+-' and l[:3] not in ('---', '+++')]
    diff.append((thy, len(d)))
  print('%d files, %d that failed, %d that differ from ml/'
        % (n, bad, len(diff)))
  for thy, k in sorted(diff, key=lambda x: -x[1]):
    print('%6d  %s' % (k, thy))
  return bad


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
