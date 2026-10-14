import json,os,re,collections
T='/home/freek/claude/hol-light/cakeml/tools/'
R='/home/freek/claude/hol-light/cakeml/cakeml-src/'
rels=[l.strip() for l in open(T+'closure2.txt') if l.strip()]
pat={'Definition':r'^Definition\b','Datatype':r'^Datatype:','Inductive':r'^(?:Co)?Inductive\b',
     'Type':r'^Type\b','Overload':r'^Overload\b','Theorem':r'^(?:Theorem|Triviality)\b',
     'Define':r'^val _ = (?:t?Define|zDefine)'}
tot=collections.Counter(); cat=collections.defaultdict(collections.Counter)
for r in rels:
  s=open(R+r,encoding='utf-8',errors='replace').read()
  k='proofs' if '/proofs' in r or 'Props' in r or 'Proof' in r else 'defs'
  for n,p in pat.items():
    c=len(re.findall(p,s,re.M)); tot[n]+=c; cat[k][n]+=c
  cat[k]['lines']+=s.count('\n'); cat[k]['files']+=1
for k in cat: print(k, dict(cat[k]))
