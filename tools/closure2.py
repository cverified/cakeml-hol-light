import json, os, collections, re, sys
T='/home/freek/claude/hol-light/cakeml/tools/'
R='/home/freek/claude/hol-light/cakeml/cakeml-src/'
d=json.load(open(T+'deps.json')); thy2file=d['thy2file']; deps=d['deps']
CUT={'basisProg','panPtreeConversion','pan_to_target','panStatic','pan_passes',
     'CommandLineProof','ml_translator'}
seen=set(); ext=set(); st=['compilerProof']
while st:
  t=st.pop()
  if t in seen or t in CUT: continue
  if t not in thy2file: ext.add(t); continue
  seen.add(t)
  st+=deps.get(t,[])
rel=sorted(os.path.relpath(thy2file[t],R) for t in seen)
open(T+'closure2.txt','w').write('\n'.join(rel)+'\n')
c=collections.Counter(os.path.dirname(r) for r in rel)
tot=0; defs=0; dats=0
for r in rel:
  s=open(R+r,encoding='utf-8',errors='replace').read()
  tot+=s.count('\n')
  defs+=len(re.findall(r'^Definition\b',s,re.M))+len(re.findall(r'^val _ = Define',s,re.M))
  dats+=len(re.findall(r'^Datatype\b',s,re.M))
for k,v in sorted(c.items()): print(v,k)
print('files',len(rel),'lines',tot,'Definitions',defs,'Datatypes',dats)
