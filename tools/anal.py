import sys, os, re, collections
sys.path.insert(0, '/home/freek/claude/hol-light/cakeml/tools')
import hol4
T='/home/freek/claude/hol-light/cakeml/tools/'
order=[l.split('\t') for l in open(T+'order.txt').read().split('\n') if l]
tot=0; rec=0; lam=0; mut=0; mutrec=0; term=0
examples=[]
for thy, rel in order:
  for b in hol4.parse(hol4.SRC+rel.strip()):
    if b.kind!='Definition': continue
    tot+=1
    body=hol4.strip_comments(b.body)
    names=hol4.definition_names(body)
    nm=set(names)
    isrec=False; islam=False
    for cl in hol4.split_clauses(body):
      if '=' not in cl: continue
      i=cl.index('=')
      rhs=cl[i+1:]
      ids=set(re.findall(r"[A-Za-z][A-Za-z0-9_']*",rhs))
      if ids & nm:
        isrec=True
        # recursive call inside a lambda?
        for m in re.finditer(r'[λ\\]', rhs):
          seg=rhs[m.start():]
          if set(re.findall(r"[A-Za-z][A-Za-z0-9_']*",seg)) & nm:
            islam=True
    if isrec: rec+=1
    if islam: lam+=1; examples.append((thy,b.name))
    if len(nm)>1: mut+=1
    if len(nm)>1 and isrec: mutrec+=1
    if b.extra: term+=1
print(f'definitions {tot}, recursive {rec}, recursive under a lambda {lam}, '
      f'multi-head {mut}, multi-head recursive {mutrec}, with Termination {term}')
print(' '.join(f'{a}:{b}' for a,b in examples[:60]))
