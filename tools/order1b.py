"""the proof theories of the second part of the first pass, in an
   order in which every one comes after the theories it needs: the
   ones of the closure (closure2.txt) that are not definition
   theories (order.txt) and not excluded (excluded.txt).

     python3 -I tools/order1b.py     writes tools/order1b.txt
"""
import json, os
T = '/home/freek/claude/hol-light/cakeml/tools/'
R = '/home/freek/claude/hol-light/cakeml/cakeml-src/'
d = json.load(open(T + 'deps.json'))
thy2file = d['thy2file']; deps = d['deps']
rels = set(l.strip() for l in open(T + 'closure2.txt') if l.strip())
defs = set(l.split('\t')[0] for l in open(T + 'order.txt') if l.strip())
out = set(l.split('\t')[0] for l in open(T + 'excluded.txt')
          if l.strip())
proofs = {t for t, f in thy2file.items()
          if os.path.relpath(f, R) in rels and t not in defs and
          t not in out}
order = []; seen = set()


def visit(t, stack=()):
  if t in seen or t not in proofs: return
  if t in stack: print('CYCLE', t, stack); return
  seen.add(t)
  for a in sorted(deps[t]): visit(a, stack + (t,))
  order.append(t)


for t in sorted(proofs): visit(t)
with open(T + 'order1b.txt', 'w') as f:
  for t in order:
    f.write('%s\t%s\n' % (t, os.path.relpath(thy2file[t], R)))
print(len(order), 'proof theories')
