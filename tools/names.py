"""Builds the table of all names defined by the ported theories.

Writes tools/names.txt with lines "cakeml-name theory kind".
Reports the names that are defined in more than one theory, and
the names that clash with HOL Light.
"""
import sys, os, re, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4

T = '/home/freek/claude/hol-light/cakeml/tools/'
SRC = hol4.SRC

hl = set()
for l in open(T + '../tmp/hl-names.txt'):
  if l.startswith('C ') or l.startswith('T '):
    hl.add(l.split()[1])

defined = collections.defaultdict(list)   # name -> [(thy,kind)]
order = [l.split('\t') for l in open(T + 'order.txt').read().split('\n') if l]
for thy, rel in order:
  for b in hol4.parse(SRC + rel.strip()):
    if b.kind == 'Datatype':
      for ty, cons, flds in hol4.datatype_names(b.body):
        defined[ty].append((thy, 'type'))
        for c in cons: defined[c].append((thy, 'con'))
        for f in flds: defined[f].append((thy, 'field'))
    elif b.kind == 'Definition':
      for nm in hol4.definition_names(b.body):
        defined[nm].append((thy, 'def'))
    elif b.kind in ('Inductive', 'CoInductive'):
      for nm in hol4.definition_names(b.body):
        defined[nm].append((thy, 'rel'))
    elif b.kind == 'Type':
      if b.name: defined[b.name].append((thy, 'tyabbrev'))
    elif b.kind == 'Overload':
      if b.name: defined[b.name].append((thy, 'overload'))

with open(T + 'names.txt', 'w') as f:
  for nm in sorted(defined):
    for thy, kind in defined[nm]:
      f.write(f'{nm}\t{thy}\t{kind}\n')

multi = {nm: v for nm, v in defined.items() if len({t for t, _ in v}) > 1}
clash = {nm: v for nm, v in defined.items() if nm in hl}
print('total names', len(defined))
print('defined in more than one theory:', len(multi))
print('clashing with HOL Light:', len(clash), sorted(clash)[:40])
cnt = collections.Counter({nm: len({t for t, _ in v}) for nm, v in multi.items()})
for nm, c in cnt.most_common(30):
  print(f'  {nm:22s} {c}  {" ".join(sorted({t for t,_ in multi[nm]}))[:80]}')
