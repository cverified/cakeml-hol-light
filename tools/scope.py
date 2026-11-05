"""what the scope of a file changes in the statements it reads

  python3 -I tools/scope.py

tools/scope.ml reads every statement of the port twice in a session
that has the port loaded: once with the interface cut down to the
theories that the source of its file can see (tmp/scope.out) and
once as the session has it (tmp/plain.out, the baseline).  This
compares the two.

The baseline matters because a re-reading in a session that has the
whole port loaded fails for statements that their own file read
without trouble -- every file's overloads are in the interface then
-- so a statement that neither reading can read is no finding of
the scope.  What the scope breaks is the statements that only it
cannot read; what it is for is the statements whose constants it
changes (SCHANGE: the statement the run made is on the left).
"""
import os, sys, collections
T = os.path.dirname(os.path.abspath(__file__)) + '/'
C = T + '../'


def read(f):
  out = collections.defaultdict(dict)
  for l in open(C + f):
    p = l.rstrip('\n').split('\t')
    if len(p) < 5: continue
    out[p[0]][(p[1], p[3])] = p[4]
  return out


def main():
  sc, pl = read('tmp/scope.out'), read('tmp/plain.out')
  sfail, pfail = set(sc['SFAIL']), set(pl['SFAIL'])
  print('%d statements that the scope of their file cannot read, '
        '%d of which the session cannot read either'
        % (len(sfail), len(sfail & pfail)))
  only = sorted(sfail - pfail)
  print('%d that only the scope cannot read:' % len(only))
  byfile = collections.Counter(f for f, _ in only)
  for f, n in byfile.most_common(14):
    print('  %-46s %d' % (f, n))
  print('%d that only the session cannot read (the scope puts them '
        'right)' % len(pfail - sfail))
  ch = sc['SCHANGE']
  print('%d statements whose constants the scope changes:' % len(ch))
  cnt = collections.Counter()
  for (f, nm), d in ch.items():
    a, _, b = d.partition(' / the scope ')
    cnt[(a.replace('the run ', '').strip(), b.strip())] += 1
  for (a, b), n in cnt.most_common(16):
    print('  %-34s -> %-30s %d' % (a[:34], b[:30], n))
  # a name that the cut leaves no constant of at all is a free
  # variable of the statement, which says less than the source
  gained = []
  for k, v in sc['SFREE'].items():
    was = set(pl['SFREE'].get(k, '').split())
    new = [w for w in v.split() if w not in was]
    if new and k not in set(pl['SFAIL']): gained.append((k, new))
  print('%d statements with a free variable that the session reads '
        'as a constant:' % len(gained))
  cnt = collections.Counter(w for _, ws in gained for w in ws)
  for w, n in cnt.most_common(12):
    print('  %-28s %d' % (w, n))


if __name__ == '__main__':
  main()
