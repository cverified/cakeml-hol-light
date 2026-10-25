"""the statements of tmp/unstated.txt that read with cake_as_vars
   go into fieldvars.READ"""
import os, sys

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import fieldvars

nm_of = {}
p = T + '../tmp/dry/thmbind.txt'
if os.path.exists(p):
  for l in open(p):
    thy, nm, b = l.split(); nm_of[b] = nm
add = set()
drop = set()
for l in open(T + '../tmp/unstated.txt'):
  f = l.rstrip('\n').split('\t')
  if len(f) < 3: continue
  if f[2].startswith('AS_VARS'):
    add.add(nm_of.get(f[1], f[1]))
  # a statement that reads plainly as well needs no entry: the
  # round that put it there read a failing proof as a statement
  # that does not read
  elif f[2].startswith('PROOF PLAINOK'):
    drop.add(nm_of.get(f[1], f[1]))
if not add and not drop:
  print('no statement to add or to drop'); sys.exit(1)
vars_ = {k: v for k, v in fieldvars.VARS.items() if k not in add}
read = sorted((set(fieldvars.READ) | add) - drop)
doc = open(T + 'fieldvars.py').read().split('VARS = {')[0]
out = [doc.rstrip() + '\n', 'VARS = {']
for nm in sorted(vars_):
  out.append('  %r: [%s],'
             % (nm, ', '.join('(%r, %r)' % (v, t)
                              for v, t in sorted(vars_[nm]))))
out += ['}', '', 'READ = [']
for nm in read: out.append('  %r,' % nm)
out.append(']')
open(T + 'fieldvars.py', 'w').write('\n'.join(out) + '\n')
print('  %d added, %d dropped: %d annotated, %d read'
      % (len(add - set(fieldvars.READ)),
         len(drop & set(fieldvars.READ)), len(vars_), len(read)))
