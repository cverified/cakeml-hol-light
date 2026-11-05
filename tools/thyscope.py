"""a theorem that reads a name of a theory its source cannot see

  python3 -I tools/thyscope.py

HOL4 reads an overloaded name as the constant of a theory in the
ancestry of the file that writes it, and a name of any other
theory is not in its grammar at all.  The port has one interface,
so every theory's overload of a name is in it, and where the types
do not pin a name down HOL Light takes the constant that was
registered last -- the load order then decides what the statement
says (ISSUES.md "A statement that means another theory's
constant").

This says of every theorem of the port whether its statement reads
a constant of a theory that the Ancestors blocks of its source
cannot see.  It reads the constants out of tmp/csts.txt, which
tools/mkcsts.py writes from the theorems that a session has, so
these are the statements as the port really read them and not a
re-reading.  Of a finding it says whether the scope of the file
has a constant of the same overloaded name (then the statement
means that one and the port has it wrong) or not (then the port
writes the name of the constant itself, or tools/deps.py has the
ancestry of the source short).
"""
import os, re, sys, json, collections
T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import mkscope
C = T + '../'


def overloads():
  """the constants that the port overloads a name with"""
  out = collections.defaultdict(set)
  for dp, dn, fn in os.walk(C + 'ml'):
    for f in sorted(fn):
      if not f.endswith('.ml'): continue
      for m in re.finditer(r'hol4_(?:field_)?overload(?:_last)?'
                           r'\s+"([^"]+)"\s+"([^"]+)"',
                           open(os.path.join(dp, f)).read()):
        out[m.group(1)].add(m.group(2))
  return out


def main():
  thys = mkscope.theories()
  cthy = mkscope.constant_theories()
  ovl = overloads()
  name_of = collections.defaultdict(set)
  for n, cs in ovl.items():
    for c in cs: name_of[c].add(n)
  hard, soft = [], []
  nthm = 0
  for l in open(C + 'tmp/csts.txt'):
    f, b, cs = (l.rstrip('\n').split('\t') + ['', '', ''])[:3]
    thy = os.path.basename(f)[:-3]
    ok = mkscope.scope(thy) & set(thys)
    nthm += 1
    for c in cs.split():
      t = cthy.get(c, '')
      if t == '' or t == thy or t in ok: continue
      alt = set(c2 for n in name_of.get(c, ())
                for c2 in ovl[n] if cthy.get(c2, '') in ok)
      (hard if alt else soft).append((thy, b, c, t, sorted(alt)))
  for thy, b, c, t, alt in hard:
    print('%s$%s reads %s of %s, and %s is in its scope'
          % (thy, b, c, t, ' '.join(alt)))
  print('%d theorems of the port' % nthm)
  print('%d name(s) of a theory out of the scope of the source, in '
        '%d theorem(s), that the scope has a constant of the same '
        'overload for' % (len(hard),
                          len(set((t, b) for t, b, _, _, _ in hard))))
  print('%d further name(s) of a theory out of that scope, in %d '
        'theorem(s), that no overload of the scope has: the port '
        'writes the name of the constant itself, or the ancestry is '
        'short' % (len(soft),
                   len(set((t, b) for t, b, _, _, _ in soft))))
  cnt = collections.Counter((thy, c) for thy, b, c, t, a in hard)
  for (thy, c), n in cnt.most_common(12):
    print('  %-24s %-28s %d' % (thy, c, n))


if __name__ == '__main__':
  main()
