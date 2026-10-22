"""merge sections into a .prf, keeping the order of the source

  python3 -I tmp/addprf.py <prf> <ml> <new sections file>...

A section of a new file replaces one of the same name in the .prf.
The sections come out in the order in which the file of the port
states the theorems.
"""
import sys, re

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

src = open(ml).read()
pos = {}
seen = {}
for m in re.finditer(r'cake_theorem "([A-Za-z_0-9\']+)', src):
  n = m.group(1)
  seen[n] = seen.get(n, 0) + 1
  pos.setdefault(n, m.start())
  pos['%s#%d' % (n, seen[n])] = m.start()

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
