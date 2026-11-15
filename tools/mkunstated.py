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

The entries are grouped by what the parser said, with one of its
messages in front of each group: a statement is won back by
putting that right, so the table says what to work on and not
only which statements are out.
"""
import sys, os, re, collections

# A harvest in which a file did not load gives the files after it
# statements that fail for want of a constant, and those are not
# statements to take out of the port: an entry of a file that
# loaded is what the session says, and of a file that did not it
# is what the table said before.

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
      # the binding of a theorem that the port derives is an
      # expression and not an identifier (cake_cases foo), so it
      # is the rest of the line and not one field
      parts = l.split()
      if len(parts) < 3: continue
      thy, nm, b = parts[0], parts[1], ' '.join(parts[2:])
      bind[(thy, b)] = nm
  out = []
  seen = set()
  for l in open(T + '../tmp/unstated.txt'):
    parts = l.rstrip('\n').split('\t')
    if len(parts) < 3: continue
    f, b, msg = parts[0], parts[1], parts[2]
    # a theorem that HOL4 states as the value of an expression is
    # not a statement of the source: what it says is
    # overrides.NO_DERIVE's to record, not this table's
    if msg.startswith('VALUE'): continue
    # a PROOF entry is one whose statement read on its own and
    # whose proof did not, so it says nothing about the statement
    # -- and a tactic of a hand-written proof holds terms of its
    # own, which fail with the same message a statement does
    if msg.startswith('PROOF'): continue
    if not any(k in msg for k in PARSE): continue
    rel = re.sub(r'^.*/ml/', '', f)
    thy = thy_of.get(rel)
    if thy is None: continue
    nm = bind.get((thy, b), b)
    if (thy, nm) in seen: continue
    seen.add((thy, nm))
    out.append((thy, nm, msg))
  # a file that did not load says nothing about the statements
  # after the phrase it stopped at, and a file that needs it is
  # missing what it defines: so an entry of a file that loaded,
  # and whose ancestors all loaded, is what the session says,
  # and every other one is what the table said before
  import unstated
  bad, seen = set(), set()
  for l in open(T + '../tmp/cs.out'):
    rel = l.split()[0] if l.split() else ''
    if rel in thy_of:
      seen.add(thy_of[rel])
      if 'Exception' in l or 'Error' in l: bad.add(thy_of[rel])
  # a file the run did not reach says nothing either
  bad |= {t for t in db.kind_of_thy if t not in seen}
  # and a file whose ancestor did not load is missing what that
  # one defines, whether it loaded itself or not
  bad = {t for t in db.kind_of_thy
         if (db.ancestors(t) | {t}) & bad}
  out = [r for r in out if r[0] not in bad]
  seen = {(r[0], r[1]) for r in out}
  out += [(thy, nm, 'the file did not load in this run')
          for (thy, nm) in sorted(unstated.NAMES)
          if thy in bad and (thy, nm) not in seen]

  print(open(T + 'unstated.py').read().split('NAMES = set([')[0]
        + 'NAMES = set([')
  # grouped by what the parser said, so that the table says what
  # has to be put right and not only which statements are out
  def why(msg):
    m = ' '.join(msg.split())
    for k in PARSE:
      if k in m: return (k, m[:120])
    return ('', m[:120])
  rows = sorted(out, key=lambda r: (why(r[2])[0], r[0], r[1]))
  last = None
  for thy, nm, msg in rows:
    k, m = why(msg)
    if k != last:
      print('  # %s' % m)
      last = k
    print('  (%r, %r),' % (thy, nm))
  print('])')
  print('# %d statements' % len(out), file=sys.stderr)


if __name__ == '__main__':
  main()
