import json, sys, collections
d = json.load(open('/home/freek/claude/hol-light/cakeml/tools/deps.json'))
thy2file=d['thy2file']; deps=d['deps']
start='compilerProof'
# BFS
prev={start:None}; q=collections.deque([start])
while q:
  t=q.popleft()
  for a in deps.get(t,[]):
    if a not in prev and a in thy2file:
      prev[a]=t; q.append(a)
for tgt in sys.argv[1:]:
  if tgt not in prev: print(tgt,'NOT REACHED'); continue
  p=[];x=tgt
  while x: p.append(x); x=prev[x]
  print(' <- '.join(p))
