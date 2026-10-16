"""the definitions that the first pass assumes, with the goal that
   their termination proof was left with

     python3 -I tools/cheatgoals.py [why ...]

   joins ml/CHEATS.md (the name, the file and the reason) with
   tmp/debug.txt (the goals that a run with CAKE_DEBUG=1 logs,
   which say of which definition they are).  With arguments only
   the cheats whose reason has one of them in it are printed."""
import sys, re, collections

sys.path.insert(0, 'tools')
from goals import untype          # the printer's type annotations

def cheats():
  out = []
  for l in open('ml/CHEATS.md'):
    m = re.match(r'\| `([^`]*)` \| `([^`]*)` \| (.*) \|', l)
    if m: out.append((m.group(1), m.group(2), m.group(3).strip()))
  return out

def goals():
  """definition -> [(goal, assumptions)]"""
  text = open('tmp/debug.txt', errors='replace').read().split('\n')
  out = collections.defaultdict(list)
  i = 0
  while i < len(text):
    m = re.match(r'unsolved termination goal of (.*):$', text[i])
    if not m:
      i += 1
      continue
    nm = m.group(1)
    i += 1
    g = []
    while i < len(text) and not text[i].startswith('  asm: ') and \
          not text[i].startswith('cannot prove') and \
          not text[i].startswith('unsolved termination goal'):
      g.append(text[i].strip()); i += 1
    asms = []
    while i < len(text) and text[i].startswith('  asm: '):
      asms.append(untype(text[i][7:].strip())); i += 1
    out[nm].append((untype(' '.join(g)), asms))
  return out

want = [a.lower() for a in sys.argv[1:]]
gs = goals()
# a goal is logged under the names of the block, which are the
# names of a family of functions together
byname = {}
for nm, v in gs.items():
  for n in nm.split(', '): byname.setdefault(n, []).append((nm, v))
n = 0
for name, f, why in cheats():
  if want and not any(w in why.lower() for w in want): continue
  n += 1
  print('%-34s %-44s %s' % (name, f, why))
  for nm, v in byname.get(name, []):
    for g, asms in v[:2]:
      print('    goal: %s' % g[:150])
      for a in asms[:4]:
        print('      asm: %s' % a[:120])
print()
print('%d cheats' % n)
