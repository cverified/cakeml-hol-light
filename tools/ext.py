import json,os,re,collections
T='/home/freek/claude/hol-light/cakeml/tools/'
R='/home/freek/claude/hol-light/cakeml/cakeml-src/'
d=json.load(open(T+'deps.json')); thy2file=d['thy2file']; deps=d['deps']
rels=set(l.strip() for l in open(T+'closure2.txt') if l.strip())
defthys=[t for t,f in thy2file.items()
         if os.path.relpath(f,R) in rels and not ('/proofs' in f or 'Props' in f or 'Proof' in f)]
use=collections.defaultdict(list)
for t in defthys:
  for a in deps[t]:
    if a not in thy2file: use[a].append(t)
for a in sorted(use): print(f'{a:22s} {len(use[a]):3d}  {" ".join(sorted(use[a])[:6])}')
print(len(defthys),'def theories')
