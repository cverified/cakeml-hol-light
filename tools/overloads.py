"""every Overload and Type of a source has a counterpart

  python3 -I tools/overloads.py [<theory>...]

Phase one ports every `Overload` and every `Type` of a source
(`CLAUDE.md`).  The port has an overload either as an overload of
HOL Light (`hol4_overload`, `overload_interface`, ...) or, where
it cannot declare one, as a pointer at the source that names it
-- the port then writes out what the name stands for.  A type
abbreviation is a `new_type_abbrev` where it has no parameters
(HOL Light has none with them) and a pointer otherwise.  This
checks that one of the two is there for every such block, as
`tools/coverage.py` does for the other blocks.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import hol4, hterm, db as dbmod, port as portmod

DECL = (r'(?:hol4_overload|hol4_field_overload|hol4_only|'
        r'overload_interface|override_interface)\s*"%s"')
AT = r'the (?:overload|Overload|infix) %s'
ABBREV = r'new_type_abbrev\s*\(\s*"%s"'
AT_TY = r'the type abbreviation %s'


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  n = bad = nty = badty = 0
  for thy, path, kind in dbmod.load_order():
    if want and thy not in want: continue
    p = portmod.Porter(db, thy)
    try:
      flat = ' '.join(open(portmod.ML +
                           db.mlpath_of(thy)).read().split())
    except OSError:
      continue
    for b in hol4.parse(path):
      if b.kind == 'Type' and p.wanted(b) and b.name:
        nty += 1
        # the port prefixes the name of a type abbreviation that
        # another theory has one of as well (sptree's num_set)
        nms = [b.name, p.tnm(b.name)]
        if not any(re.search(ABBREV % re.escape(x), flat) or
                   re.search(AT_TY % re.escape(x), flat)
                   for x in nms):
          badty += 1
          if badty <= 10:
            print('%s: the Type %s'
                  % (re.sub(r'^.*/', '', path), b.name))
        continue
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
  print('%d Type blocks of the sources, %d with no counterpart '
        'in the port' % (nty, badty))


if __name__ == '__main__':
  main()
