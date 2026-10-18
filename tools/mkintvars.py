"""the variables of a statement that hold an integer, from a run

  python3 -I tools/mkintvars.py

HOL Light says of a statement that it cannot read "i cannot have
type num and int simultaneously", which names the variable that
holds an integer and that nothing in the statement says so of.
This turns those messages (tmp/unstated.txt, which tools/bin/thms
writes from a session of a run, or tmp/diag.out of
tools/bin/diag) into the entries of overrides.THM_INT_VARS, which
the port reads to write the numerals beside such a variable as
integers.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod

NUMINT = re.compile(r"([A-Za-z_][A-Za-z0-9_']*) cannot have type "
                    r"(?:num and int|int and num)")


def rows():
  """(file, name, message) of every statement a session could not
     read, from the diagnosis or from the report of a run"""
  out = []
  try:
    for l in open(T + '../tmp/diag.out'):
      f = l.rstrip('\n').split('\t')
      if len(f) >= 5 and f[0] in ('FAIL', 'BADTYPE'):
        out.append((f[1], f[3], f[4]))
  except OSError:
    pass
  if out: return out
  for l in open(T + '../tmp/unstated.txt'):
    if '\t' in l:
      nm, msg = l.rstrip('\n').split('\t', 1)
      out.append((None, nm, msg))
  return out


def main():
  db = dbmod.Db()
  thy_of = {db.mlpath_of(t): t for t, _, _ in db.order}
  byname = collections.defaultdict(set)
  for f, nm, msg in rows():
    m = NUMINT.search(msg)
    if not m: continue
    thy = thy_of.get(f) if f else None
    byname[(thy, re.sub(r'\[.*', '', nm))].add(m.group(1))
  for (thy, nm), vs in sorted(byname.items(),
                              key=lambda kv: (str(kv[0][0]), kv[0][1])):
    print("  ('%s', '%s'): [%s],"
          % (thy, nm, ', '.join("'%s'" % v for v in sorted(vs))))
  print('# %d theorems' % len(byname))


if __name__ == '__main__':
  main()
