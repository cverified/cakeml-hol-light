"""put the theories of a widened scope into the porting order

  python3 -I tools/mkorder.py          say what would change
  python3 -I tools/mkorder.py -w       write order.txt and order1b.txt

tools/order.txt and tools/order1b.txt are the order in which
tools/port.py visits the theories, which is what the resolution of
a name that several theories define depends on (tools/db.py,
`front_thy`).  They are not the load order: that is
tools/load.txt, which tools/loadorder.py derives from the `needs`
lines of the files themselves, and it does put a proof theory in
front of a definition theory where one needs it (targetSem needs
evaluateProps and asmProps).

So the two files are not regenerated.  What this does is add the
theories of tools/closure2.txt that are in neither of them, each
in front of the first theory that needs it and after the ones it
needs; everything already there keeps its place.  A theory goes
in order1b.txt when its source is in a `proofs/` directory or its
name has `Proof` or `Props` in it, and in order.txt otherwise.
Entries of tools/excluded.txt are left out, and an entry that is
already there stays even when the closure no longer has it
(order.txt has panLang, which the port needs for compiler.ml).
"""
import json, os, sys

T = os.path.dirname(os.path.abspath(__file__)) + '/'
R = T + '../cakeml-src/'
d = json.load(open(T + 'deps.json'))
thy2file = d['thy2file']; deps = d['deps']
rels = set(l.strip() for l in open(T + 'closure2.txt') if l.strip())
out = set(l.split('\t')[0] for l in open(T + 'excluded.txt') if l.strip())
scope = {t for t, f in thy2file.items()
         if os.path.relpath(f, R) in rels and t not in out}


def isproof(t):
  f = os.path.relpath(thy2file[t], R)
  return '/proofs/' in f or 'Proof' in f or 'Props' in f


def read(name):
  return [l.split('\t')[0] for l in open(T + name) if l.strip()]


was = {'order.txt': read('order.txt'), 'order1b.txt': read('order1b.txt')}
placed = set(was['order.txt']) | set(was['order1b.txt'])
new = sorted(scope - placed)
print('%d theories in the scope, %d already placed, %d new'
      % (len(scope), len(scope & placed), len(new)))
for name in ('order.txt', 'order1b.txt'):
  want = [t for t in new if isproof(t) == (name == 'order1b.txt')]
  # a stable topological sort: the ones already there keep their
  # order, and a new one is emitted after the ones it needs
  keep = set(was[name]) | set(want)
  order, seen, stack = [], set(), []

  def visit(t):
    if t in seen or t not in keep: return
    if t in stack: print('CYCLE', t, '<-', ' '.join(stack)); return
    stack.append(t); seen.add(t)
    for a in deps.get(t, []): visit(a)
    stack.pop(); order.append(t)

  for t in was[name] + want: visit(t)
  s = ''.join('%s\t%s\n' % (t, os.path.relpath(thy2file[t], R))
              for t in order)
  old = open(T + name).read()
  if s == old:
    print('%-13s unchanged, %d theories' % (name, len(order)))
  else:
    moved = [t for i, t in enumerate(was[name])
             if order.index(t) != i - sum(1 for u in order[:order.index(t)]
                                          if u in set(want))]
    print('%-13s %d -> %d theories, %d added%s'
          % (name, len(was[name]), len(order), len(want),
             ', %d of the old moved' % len(moved) if moved else ''))
    if '-w' in sys.argv: open(T + name, 'w').write(s)
if '-w' not in sys.argv: print('(dry run; -w writes)')
