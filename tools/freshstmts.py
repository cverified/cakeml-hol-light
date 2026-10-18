"""the statements of a fresh translation, for tools/bin/diag

  python3 -I tools/freshstmts.py <theory>...

writes tmp/stmts.txt from the translation that the tools make
*now*, without writing anything into ml/, so that a session can
read the statements of a theory while a run is going.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, port as portmod, thmcheck

HIDE = re.compile(r'^cake_hide \[(.*?)\];;', re.S | re.M)


def main():
  if not sys.argv[1:]:
    print(__doc__); return
  want = sys.argv[1:]
  db = dbmod.Db()
  texts = {}
  anc = set()
  for thy in want:
    anc |= db.ancestors(thy)
  for thy, path, kind in dbmod.load_order():
    if thy not in anc: continue
    text = portmod.Porter(db, thy).run()
    if thy in want: texts[thy] = text
  n = 0
  with open(T + '../tmp/stmts.txt', 'w') as o:
    for thy in want:
      text = texts.get(thy)
      if text is None: continue
      f = db.mlpath_of(thy)
      m = HIDE.search(text)
      if m:
        o.write('@@@HIDE\t%s\n'
                % ' '.join(re.findall(r'"([^"]+)"', m.group(1))))
      for nm, line, stmt in thmcheck.scan(text):
        o.write('@@@\t%s\t%d\t%s\n%s\n' % (f, line, nm, stmt))
        n += 1
  print('%d statements of %d theories in tmp/stmts.txt'
        % (n, len(texts)))


if __name__ == '__main__':
  main()
