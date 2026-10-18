"""a name that the port writes and has no constant of

  python3 -I tools/freenames.py

Every identifier of every quotation of `ml/` that is no constant
of the port is a variable of the term, and HOL4 generalises the
free variables of a theorem, so most of them are right.  What is
not right is a name that the port *means* as a constant: an
accessor of a record that has no field of that name
(`wordSem_state_ok`), or a name that a theory of HOL4 defines and
the port has lost.  This says which those are.

It needs `tools/constants.txt`, the name of every constant of the
port, which `tools/bin/intargs` dumps out of a session.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, nohol4

ML = T + '../ml/'


def main():
  try:
    consts = set(l.strip() for l in open(T + 'constants.txt')
                 if l.strip())
  except OSError:
    print('no tools/constants.txt: run tools/bin/intargs first')
    return 0
  db = dbmod.Db()
  # the accessors that the records of the port can have
  recs = {}
  for (thy, ty), flds in db.recs.items():
    recs.setdefault(db.rename.get((thy, ty), ty), set()).update(flds)
  bad = collections.Counter()
  where = {}
  for dp, _, fs in os.walk(ML):
    for f in sorted(fs):
      if not f.endswith('.ml'): continue
      p = os.path.join(dp, f)
      code = nohol4.code_free(open(p, encoding='utf-8').read())
      for m in re.finditer(r'`([^`]*)`', code):
        for i in set(re.findall(r"[A-Za-z][A-Za-z0-9_']*",
                                m.group(1))):
          if i in consts: continue
          # a name of the shape of an accessor of a record of the
          # port, which the port means as one
          rec = next((r for r in recs if i.startswith(r + '_')), None)
          if rec is None: continue
          bad[i] += 1
          where.setdefault(i, (os.path.relpath(p, ML),
                               code[:m.start()].count('\n') + 1))
  print('%d names of the shape of an accessor that the port has no '
        'constant of' % len(bad))
  for i, k in bad.most_common(20):
    print('%6d  %-36s %s:%d' % (k, i, where[i][0], where[i][1]))
  return len(bad)


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
