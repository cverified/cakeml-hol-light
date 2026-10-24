"""the table of the statements that HOL Light does not read

  tools/bin/harvestall
  python3 -I tools/mkunstated.py > tools/unstated.py

The harvest writes a line per statement to tmp/unstated.txt (the
file of the port, the binding and the message of HOL Light); this
turns it into the table that tools/port.py reads, keyed by the
theory and the name of the source, which is what the port has
when it writes the block.  A proof that fails is in the harvest
too (a cheat proves nothing but it is a cheat, not a failure), so
only a message of the parser counts.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod

# the messages of HOL Light's parser and of the goal stack, which
# say that the statement is not a statement it reads; anything
# else is a proof that did not go through
# Printexc.to_string writes a failure as Failure("...."), so the
# message is matched without the quotes around it
PARSE = ('typechecking error', 'Unparsed input',
         'Non-boolean goal', 'term_of_preterm',
         'overload resolution', '"find"')


def main():
  db = dbmod.Db()
  thy_of = {}
  for thy, _, _ in dbmod.load_order():
    try: thy_of[db.mlpath_of(thy)] = thy
    except Exception: pass
  # the binding of a theorem is not the name of the source where
  # the port gave it the theory in front, so the table is keyed by
  # the name the source has: the dump of a port run says which
  bind = {}
  p = T + '../tmp/dry/thmbind.txt'
  if os.path.exists(p):
    for l in open(p):
      thy, nm, b = l.split()
      bind[(thy, b)] = nm
  out = []
  seen = set()
  for l in open(T + '../tmp/unstated.txt'):
    parts = l.rstrip('\n').split('\t')
    if len(parts) < 3: continue
    f, b, msg = parts[0], parts[1], parts[2]
    if not any(k in msg for k in PARSE): continue
    rel = re.sub(r'^.*/ml/', '', f)
    thy = thy_of.get(rel)
    if thy is None: continue
    nm = bind.get((thy, b), b)
    if (thy, nm) in seen: continue
    seen.add((thy, nm))
    out.append((thy, nm, msg))
  print(open(T + 'unstated.py').read().split('NAMES = set([')[0]
        + 'NAMES = set([')
  for thy, nm, msg in out:
    m = ' '.join(msg.split())[:60]
    print("  ('%s', '%s')," % (thy, nm))
  print('])')
  print('# %d statements' % len(out), file=sys.stderr)


if __name__ == '__main__':
  main()
