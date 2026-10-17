"""the definitions whose termination the first pass assumes, as
   the port writes them down

     python3 -I tools/mkcheats.py > tools/cheats.txt

   reads ml/CHEATS.md (which a run writes) and gives, for every
   definition that HOL Light could make if its termination were
   given, the theory and the name of the phrase that defines it.
   tools/port.py writes CHEAT_TAC in the place of the Termination
   tactic of HOL4 for those, so that what is left to do is visible
   in the file and local to it.

   A definition that HOL Light cannot make at all is left out: a
   body with a type variable that the constant does not reflect,
   or a constant that the port does not have.  A CHEAT_TAC cannot
   help there (it cannot introduce a constant), and those are the
   ones to work on.
"""
import re, os, sys

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# the reasons that a CHEAT_TAC cannot do anything about
HOPELESS = ('new_definition:', 'free:')


def rows():
  for l in open(C + '/ml/CHEATS.md'):
    m = re.match(r'\| `([^`]*)` \| `([^`]*)` \| (.*) \|', l)
    if m and m.group(2):
      yield m.group(1), m.group(2), m.group(3).strip()


def binding(f, name):
  """the phrase of the port that defines a constant, by its name"""
  try:
    src = open(C + '/ml/' + f).read()
  except OSError:
    return None
  for m in re.finditer(r'^let ([A-Za-z0-9_\']+) = .*?;;$', src,
                       re.M | re.S):
    if name in re.findall(r"`\(?([A-Za-z0-9_']+)", m.group(0)):
      return m.group(1)
  return None


out, skipped, lost = [], 0, []
for name, f, why in rows():
  if why.startswith(HOPELESS):
    skipped += 1
    continue
  b = binding(f, name)
  if b is None:
    lost.append(name)
    continue
  thy = os.path.basename(f)[:-3]
  out.append((thy, b))

for thy, b in sorted(set(out)):
  print(thy, b)
sys.stderr.write('%d phrases, %d that no CHEAT_TAC can help, '
                 '%d not found\n' % (len(set(out)), skipped, len(lost)))
if lost:
  sys.stderr.write('  not found: ' + ' '.join(lost[:8]) + '\n')
