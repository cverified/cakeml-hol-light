"""the proofs a run says do not go through, out of the store

  python3 -I tools/dropfails.py [--dry]

after a run (tools/bin/runall, or TOLERANT=1 with
tools/bin/harvestall).  It reads two things, because a proof can
fail in two ways:

- tmp/unstated.txt, which a tolerant load writes for every
  theorem whose proof **raised**;
- the phrase markers of tmp/cs.out, for a proof that names a
  value this port has not got: that one does not compile, so the
  try round it never runs and nothing is logged.  Where the
  marker is a comment rather than the binding (a theorem with a
  comment of its own in front of it), the store section that
  names the unbound value is the one to take out.

A name is only dropped when the store has it, and `drop` writes
why into tools/lightcake/<theory>.nofill, so that the next fill
leaves it out.  With --dry nothing is written.
"""
import os, re, sys, collections
C = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + '/'
sys.path.insert(0, C + 'tools')
import lightcake as L, proofstore

dry = '--dry' in sys.argv
fails = collections.defaultdict(dict)   # theory -> {binding: why}

def thy_of(path):
  return re.sub(r'\.ml$', '', os.path.basename(path))

p = C + 'tmp/unstated.txt'
if os.path.exists(p):
  for l in open(p):
    f = l.rstrip('\n').split('\t')
    if len(f) < 3: continue
    fails[thy_of(f[0])][f[1]] = ' '.join(f[2].split())[:160]

MARK = re.compile(r"^(\S+\.ml)\s.*?(Exception|Error):\s*(.*?)"
                  r"\[at \d+: (?:\(\* [^*]*\*\) )?"
                  r"(?:let ([A-Za-z0-9_']+)[ ,])?")
UNBOUND = re.compile(r"Unbound value ([A-Za-z0-9_']+)")
# the phrase of a theorem that has a comment of its own in front
# of it is marked by the comment, so the marker does not name the
# binding; where the message is an unbound value, the proof that
# names it is the one to take out
noname = collections.defaultdict(set)
p = C + 'tmp/cs.out'
if os.path.exists(p):
  for l in open(p):
    m = MARK.match(l)
    if not m: continue
    why = ' '.join((m.group(2) + ': ' + m.group(3)).split())[:160]
    if m.group(4):
      fails[thy_of(m.group(1))].setdefault(m.group(4), why)
    else:
      u = UNBOUND.search(l)
      if u: noname[thy_of(m.group(1))].add((u.group(1), why))

tot = 0
for thy in sorted(set(fails) | set(noname)):
  a = L.ours_of(thy)
  if not a: continue
  mlrel = re.sub(r'^.*/ml/', '', a)
  there = set(proofstore.load(mlrel))
  byb = dict((b, n) for n, b in L.our_thms(a).items())
  ns = [byb.get(b, b) for b in fails[thy]]
  # and the ones found by the name they could not resolve
  store = proofstore.load(mlrel)
  for u, _ in noname.get(thy, ()):
    rx = re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(u) +
                    r"(?![A-Za-z0-9_'])")
    ns += [n for n, t in store.items() if rx.search(t)]
  ns = sorted(set(n for n in ns if n in there))
  if not ns: continue
  tot += len(ns)
  print('%s: %s' % (thy, ' '.join(ns)))
  if not dry:
    L.drop([thy] + ns)
print('%d proofs of the store did not go through' % tot)
