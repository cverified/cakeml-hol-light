"""merge sections into a .prf, keeping the order of the source

  python3 -I tmp/addprf.py <prf> <ml> <new sections file>...

A section of a new file replaces one of the same name in the .prf.
The sections come out in the order in which the file of the port
states the theorems.
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stmts

def parse(p):
  out, name, body = [], None, []
  for l in open(p):
    if l.startswith('### '):
      if name: out.append((name, body))
      name, body = l[4:].strip(), []
    elif name is not None:
      body.append(l)
  if name: out.append((name, body))
  return out

prf, ml = sys.argv[1], sys.argv[2]
secs = {}
order = []
for n, b in parse(prf):
  if n not in secs: order.append(n)
  secs[n] = b
for f in sys.argv[3:]:
  for n, b in parse(f):
    if n not in secs: order.append(n)
    secs[n] = b

# where the file of the port states each theorem: a section of the
# store names a theorem by its binding, and one that the file
# states more than once by the binding and the count
# (tools/stmts.py knows the shape)
pos = {}
seen = {}
for b, _, _, line, _ in stmts.theorems(open(ml).read()):
  seen[b] = seen.get(b, 0) + 1
  pos.setdefault(b, line)
  pos['%s#%d' % (b, seen[b])] = line

def key(n):
  if n not in pos:
    sys.stderr.write('addprf: %s is no theorem of the file\n' % n)
    sys.exit(1)
  return pos[n]

order.sort(key=key)
with open(prf, 'w') as f:
  for n in order:
    f.write('### %s\n' % n)
    f.writelines(secs[n])
print('%d section(s)' % len(order))
