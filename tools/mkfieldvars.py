"""tools/fieldvars.py from the harvest of a run

  python3 -I tools/mkfieldvars.py [the harvest file]

reads a harvest of (theorem, variable, type) lines -- the table was
made once, from a session that had the whole port of the shape
that read every statement with the overloads taken away -- and
writes the table that the statements of the port are annotated
from.  A variable whose type has a type variable of its
own cannot be annotated (the annotation would not unify), so its
theorem goes into READ instead: those statements are read with the
overloads of the field names taken away.
"""
import os, sys, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'


def main():
  src = sys.argv[1] if sys.argv[1:] else T + '../tmp/fieldvars-all.txt'
  tab = collections.defaultdict(dict)
  read = set()
  for l in open(src):
    p = l.split(None, 2)
    if len(p) < 3: continue
    nm, var, ty = p[0], p[1], p[2].strip()
    if '?' in ty: read.add(nm); continue
    tab[nm].setdefault(var, ty)
  doc = open(T + 'fieldvars.py').read().split('VARS = {')[0]
  out = [doc.rstrip() + '\n', 'VARS = {']
  for nm in sorted(tab):
    vs = ', '.join('(%r, %r)' % (v, t) for v, t in sorted(tab[nm].items()))
    out.append('  %r: [%s],' % (nm, vs))
  out += ['}', '', 'READ = [']
  for nm in sorted(read):
    out.append('  %r,' % nm)
  out.append(']')
  open(T + 'fieldvars.py', 'w').write('\n'.join(out) + '\n')
  print('%d statements say the type of a variable, %d are read with'
        ' the overloads taken away' % (len(tab), len(read)))
  return 0


if __name__ == '__main__':
  sys.exit(main())
