import json, sys, os
d = json.load(open('/home/freek/claude/hol-light/cakeml/tools/deps.json'))
thy2file = d['thy2file']; deps = d['deps']
start = sys.argv[1] if len(sys.argv)>1 else 'compilerProof'
seen = set(); ext = set()
stack=[start]
while stack:
  t = stack.pop()
  if t in seen: continue
  if t not in thy2file:
    ext.add(t); continue
  seen.add(t)
  for a in deps.get(t,[]): stack.append(a)
print('internal:', len(seen))
print('external(HOL4 lib):', len(ext))
print(' '.join(sorted(ext)))
rel = sorted(os.path.relpath(thy2file[t], '/home/freek/claude/hol-light/cakeml/cakeml-src') for t in seen)
open('/home/freek/claude/hol-light/cakeml/tools/closure.txt','w').write('\n'.join(rel)+'\n')
import collections
c = collections.Counter(os.path.dirname(r) for r in rel)
for k,v in sorted(c.items()): print(v, k)
tot = sum(len(open('/home/freek/claude/hol-light/cakeml/cakeml-src/'+r,encoding='utf-8',errors='replace').readlines()) for r in rel)
print('total lines', tot)
