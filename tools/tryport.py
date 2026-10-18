"""translate a theory without writing the file

  python3 -I tools/tryport.py <theory> [<name>...]

prints the port of the named blocks (or of the whole theory), so
that a change to the translation can be tried while a run is
going and nothing may write into ml/.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod, port as portmod


def main():
  if not sys.argv[1:]:
    print(__doc__); return
  thy = sys.argv[1]
  want = sys.argv[2:]
  db = dbmod.Db()
  for t, _, _ in dbmod.load_order():
    if t in db.ancestors(thy) - {thy}:
      portmod.Porter(db, t).run()
  p = portmod.Porter(db, thy)
  text = p.run()
  if not want:
    print(text)
  else:
    for nm in want:
      m = re.search(r'^let [A-Za-z0-9_\']+ = cake_theorem\s*\n?\s*'
                    r'"%s(\[[^"]*\])?"(.*?);;\n' % re.escape(nm),
                    text, re.S | re.M)
      if not m:
        m = re.search(r'^let %s[A-Za-z0-9_\']* =.*?;;\n'
                      % re.escape(nm), text, re.S | re.M)
      print(m.group(0) if m else '%s: not in the port' % nm)
  for w in p.warn:
    if not want or any(nm in w for nm in want):
      print('  !', w)


if __name__ == '__main__':
  main()
