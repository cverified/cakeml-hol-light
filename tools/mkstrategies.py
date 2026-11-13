"""tools/strategies.py from the harvest of a run

  python3 -I tools/mkstrategies.py

reads tmp/strategies.txt (constant, strategy, whether the
termination was assumed, and the relation, which tools/harvest.ml
writes from a session) and tmp/dry/defbind.txt (the theory of each
constant) and writes how every definition of the port was made.
"""
import os, sys, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'

HEAD = '''"""how each definition of the port was made

A definition of a source goes through cake_define, which tries one
strategy after another, because no single primitive of HOL Light
takes what HOL4 writes.  Searching for the way again on every load
is both slow and silent about what came out, so a run harvests
what worked and the files say it themselves.

WAY holds it, as (theory, constant) -> (strategy, assumed,
relation): the strategy that made the definition, whether its
termination condition was assumed rather than proved, and the
relation it was made with ('' where there was none).

PRIMITIVE is the constants where the strategy is HOL Light's own
new_definition, which is the common case.

tools/bin/strategies harvests both from a run (cake_strategies).
"""
'''


def main():
  thy = {}
  try:
    for l in open(T + '../tmp/dry/defbind.txt'):
      t, c, _ = l.split()
      thy.setdefault(c, t)
  except OSError:
    print('no tmp/dry/defbind.txt: run tools/bin/dryport first')
    return 1
  way = {}
  kinds = collections.Counter()
  rels = collections.Counter()
  for l in open(T + '../tmp/strategies.txt'):
    p = l.rstrip('\n').split('\t')
    if len(p) < 4: continue
    c, s, ch, rel = p[0], p[1], p[2], p[3]
    s = '' if s == '-' else s
    rel = '' if rel == '-' else rel
    kinds[s or '(assumed)'] += 1
    if rel: rels[s] += 1
    if c in thy: way[(thy[c], c)] = (s, ch == 'cheat', rel)
  out = [HEAD, 'WAY = {']
  for k in sorted(way):
    out.append('  %r:\n    %r,' % (k, way[k]))
  out.append('}')
  out.append('')
  out.append('PRIMITIVE = {k for k, v in WAY.items()'
             " if v[0] == 'new_definition'}")
  open(T + 'strategies.py', 'w').write('\n'.join(out) + '\n')
  for k, n in kinds.most_common():
    print('%6d  %-20s %s' % (n, k, ('%d with a relation' % rels[k])
                             if rels[k] else ''))
  print('%6d  in a file of the port' % len(way))
  return 0


if __name__ == '__main__':
  sys.exit(main())
