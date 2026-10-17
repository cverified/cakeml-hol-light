import json,os
T='/home/freek/claude/hol-light/cakeml/tools/'
R='/home/freek/claude/hol-light/cakeml/cakeml-src/'
d=json.load(open(T+'deps.json')); thy2file=d['thy2file']; deps=d['deps']
rels=set(l.strip() for l in open(T+'closure2.txt') if l.strip())
# the encoders and the configurations of the targets are out of the
# scope of the port (tools/excluded.txt)
out=set(l.split('\t')[0] for l in open(T+'excluded.txt') if l.strip())
defset={t for t,f in thy2file.items() if os.path.relpath(f,R) in rels
        and t not in out
        and not ('/proofs' in f or 'Props' in f or 'Proof' in f)}
order=[]; seen=set()
def visit(t,stack=()):
  if t in seen or t not in defset: return
  if t in stack: print('CYCLE',t,stack); return
  seen.add(t)
  for a in sorted(deps[t]):
    if a in defset: visit(a,stack+(t,))
  order.append(t)
for t in sorted(defset): visit(t)
with open(T+'order.txt','w') as f:
  for t in order:
    f.write(f'{t}\t{os.path.relpath(thy2file[t],R)}\n')
print(len(order))
