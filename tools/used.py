import sys, os, re, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4
T = '/home/freek/claude/hol-light/cakeml/tools/'
defined = set(l.split('\t')[0] for l in open(T + 'names.txt'))
order = [l.split('\t') for l in open(T + 'order.txt').read().split('\n') if l]
use = collections.defaultdict(set)
for thy, rel in order:
  for b in hol4.parse(hol4.SRC + rel.strip()):
    if b.kind not in ('Definition', 'Datatype', 'Inductive', 'Type',
                      'Overload', 'CoInductive'): continue
    body = hol4.strip_comments(b.body)
    for w in re.findall(r"[A-Za-z][A-Za-z0-9_']*", body):
      use[w].add(thy)
rest = {w: v for w, v in use.items() if w not in defined}
cnt = collections.Counter({w: len(v) for w, v in rest.items()})
print(len([w for w, c in cnt.items() if c >= 3]), 'identifiers used in >=3 theories and not defined in the port')
for w, c in cnt.most_common(400):
  if c >= 3: print(f'{w}:{c}', end='  ')
print()
