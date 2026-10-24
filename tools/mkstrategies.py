"""tools/strategies.py from the harvest of a run

  python3 -I tools/mkstrategies.py

reads tmp/strategies.txt (constant and strategy, which
tools/bin/strategies writes from a session) and tmp/dry/defbind.txt
(the theory of each constant) and writes the constants that
new_definition makes.
"""
import os, sys, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'


def main():
  thy = {}
  try:
    for l in open(T + '../tmp/dry/defbind.txt'):
      t, c, _ = l.split()
      thy.setdefault(c, t)
  except OSError:
    print('no tmp/dry/defbind.txt: run tools/bin/dryport first')
    return 1
  prim = []
  kinds = collections.Counter()
  for l in open(T + '../tmp/strategies.txt'):
    p = l.split()
    if len(p) < 2: continue
    c, s = p[0], p[1]
    kinds[s] += 1
    if s == 'new_definition' and c in thy:
      prim.append((thy[c], c))
  out = [open(T + 'strategies.py').read().split('PRIMITIVE')[0]
         + 'PRIMITIVE = {']
  for t, c in sorted(set(prim)):
    out.append('  (%r, %r),' % (t, c))
  out.append('}')
  open(T + 'strategies.py', 'w').write('\n'.join(out) + '\n')
  for k, n in kinds.most_common():
    print('%6d  %s' % (n, k))
  print('%6d  of them are new_definition in a file of the port'
        % len(set(prim)))
  return 0


if __name__ == '__main__':
  sys.exit(main())
