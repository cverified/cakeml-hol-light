import json,os,re,collections
T='/home/freek/claude/hol-light/cakeml/tools/'
R='/home/freek/claude/hol-light/cakeml/cakeml-src/'
rels=[l.strip() for l in open(T+'closure2.txt') if l.strip()]
rels=[r for r in rels if not ('/proofs' in r or 'Props' in r or 'Proof' in r)]
term=0; defs=0; mutual=0; mutterm=0; names=collections.Counter()
examples=[]
for r in rels:
  s=open(R+r,encoding='utf-8',errors='replace').read()
  for m in re.finditer(r'^Definition\s+(\S+?):\n(.*?)^End\s*$', s, re.M|re.S):
    defs+=1
    nm=m.group(1); body=m.group(2)
    hast = '\nTermination' in body
    # function names on lhs of top-level clauses
    fns=set(re.findall(r'^\s*(?:\(\s*)?([a-zA-Z_][a-zA-Z0-9_\']*)\b', body, re.M))
    # crude: names appearing right after /\ or at clause start before = 
    cl=re.findall(r'(?:^|/\\\s*)\s*\(?\s*([a-zA-Z_][a-zA-Z0-9_\']*)[^=\n]*=[^=]', body, re.M)
    cl=[c for c in cl if c not in ('if','let','case','T','F')]
    mut = len(set(cl))>1
    if hast: term+=1
    if mut: mutual+=1
    if hast and mut: mutterm+=1; examples.append((r,nm))
print('defs',defs,'with Termination',term,'multi-name clauses',mutual,'both',mutterm)
print('\n'.join(f'{a}: {b}' for a,b in examples[:40]))
