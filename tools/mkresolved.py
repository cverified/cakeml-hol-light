"""the table of what an overloaded name means, read off HOL Light

  python3 -I tools/mkresolved.py consts <directory>
  python3 -I tools/mkresolved.py table <directory>

HOL4 resolves an overloaded name by the type that makes the term
typecheck.  So does HOL Light, against the interface that the port
builds one scope at a time (ml/lib/theorem.ml, cake_theory), and
PLAN.md decided that the port is to let it: a resolution round
ports with CAKE_RESOLVE=1, which writes every overloaded name as
the source writes it, loads that, and reads back the constant the
typechecker took.

`consts' writes the names of the constants that such a log is
about -- the ones two theories of a scope share -- which
tools/resolve.ml reads so that it logs nothing else.

`table' reads the log of the round and writes tools/resolved.txt,
whose lines are

  <theory> <block> <HOL4 name> <the constant of the port>

A block that used two constants of one name is no answer for that
name and is left out, with a line on stderr.
"""
import sys, os, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod


def candidates(db):
  """for every theory, the constants that each of its overloaded
     names could mean: the ones that the theories in its scope
     define under that name, and the one that the hand written
     library layer provides under it"""
  out = {}
  tykinds = ('type', 'tyabbrev')
  for thy, path, kind in dbmod.load_order():
    anc = db.scope(thy) | {thy}
    lib = db.lib_ambiguous(thy)
    d = {}
    for nm in set(db.overloaded_for(thy)) | set(lib):
      cs = []
      for t, k in db.defs.get(nm, []):
        if t not in anc or k in tykinds: continue
        new = db.rename.get((t, nm), nm)
        if new not in cs: cs.append(new)
      if nm in lib and lib[nm] not in cs: cs.append(lib[nm])
      if len(cs) > 1: d[nm] = cs
    out[thy] = d
  return out


def main():
  if len(sys.argv) < 3:
    print(__doc__); return 0
  what, out = sys.argv[1], sys.argv[2].rstrip('/') + '/'
  db = dbmod.Db(); db.scan(); db.mapping()
  cand = candidates(db)
  if what == 'consts':
    os.makedirs(out, exist_ok=True)
    cs = set()
    for d in cand.values():
      for v in d.values(): cs |= set(v)
    with open(out + 'consts.txt', 'w') as f:
      for c in sorted(cs): f.write(c + '\n')
    # and the overloads of the library layer that the round has to
    # register itself: the port's own files register what they
    # define (cake_ovl), and ml/lib registers only four of these
    lib = db.lib_candidates()
    with open(out + 'baseovl.txt', 'w') as f:
      for nm in sorted(lib): f.write('%s\t%s\n' % (nm, lib[nm]))
    print('%d constants to log, in %sconsts.txt; %d overloads of'
          ' the library layer' % (len(cs), out, len(lib)))
    return 0
  if what != 'table':
    print(__doc__); return 1
  # the constant of a name in a block: a block that used two of
  # them says nothing, and one that used none is not in the log
  got = collections.defaultdict(set)
  n = 0
  for l in open(out + 'resolve.txt'):
    v = l.rstrip('\n').split('\t')
    if len(v) != 3: continue
    thy, blk, c = v
    n += 1
    for nm, cs in cand.get(thy, {}).items():
      if c in cs: got[(thy, blk, nm)].add(c)
  bad = 0
  with open(T + 'resolved.txt', 'w') as f:
    for k in sorted(got):
      v = got[k]
      if len(v) != 1:
        bad += 1
        print('two constants of %s in %s %s: %s'
              % (k[2], k[0], k[1], ' '.join(sorted(v))),
              file=sys.stderr)
        continue
      f.write('%s\t%s\t%s\t%s\n' % (k + (v.pop(),)))
  print('%d lines of log, %d resolutions, %d names a block used'
        ' twice' % (n, len(got) - bad, bad))
  return 0


if __name__ == '__main__':
  sys.exit(main())
