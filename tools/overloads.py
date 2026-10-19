"""every Overload of a source has a counterpart in the port

  python3 -I tools/overloads.py [<theory>...]

Phase one ports every `Overload` of a source (`CLAUDE.md`).  The
port has one either as an overload of HOL Light
(`hol4_overload`, `overload_interface`, ...) or, where it cannot
declare one, as a pointer at the source that names it -- the port
then writes out what the name stands for.  This checks that one
of the two is there for every `Overload` block, as
`tools/coverage.py` does for the other blocks.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import hol4, db as dbmod, port as portmod

DECL = (r'(?:hol4_overload|hol4_field_overload|hol4_only|'
        r'overload_interface|override_interface)\s*"%s"')
AT = r'the (?:overload|Overload|infix) %s'


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  n = bad = 0
  for thy, path, kind in dbmod.load_order():
    if want and thy not in want: continue
    p = portmod.Porter(db, thy)
    try:
      flat = ' '.join(open(portmod.ML +
                           db.mlpath_of(thy)).read().split())
    except OSError:
      continue
    for b in hol4.parse(path):
      if b.kind != 'Overload' or not p.wanted(b): continue
      n += 1
      nm = b.name
      if not nm: continue
      if re.search(DECL % re.escape(nm), flat): continue
      if re.search(AT % re.escape(nm), flat): continue
      bad += 1
      if bad <= 10:
        print('%s: the Overload %s' % (re.sub(r'^.*/', '', path), nm))
  print('%d Overload blocks of the sources, %d with no counterpart '
        'in the port' % (n, bad))


if __name__ == '__main__':
  main()
