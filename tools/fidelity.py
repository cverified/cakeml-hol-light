"""check that no name of a HOL4 definition is missing from its port

  python3 -I tools/fidelity.py [theory...]

For every definition block of a HOL4 source, this takes the names
of the constants that its term mentions, maps them through the
naming of the port, and reports the ones that do not occur in the
file of the port.  A missing name means that the port dropped a
part of the definition (a clause of a pattern match, say).
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, port as portmod

KINDS = ('Definition', 'Inductive', 'CoInductive')

db = dbmod.Db()
thys = sys.argv[1:] or [t for t, _, _ in dbmod.load_order()]
tot = bad = 0
for thy in thys:
  path = db.thy_of_file.get(thy)
  if not path: continue
  p = portmod.Porter(db, thy)
  try:
    text = open(portmod.ML + db.mlpath_of(thy)).read()
  except Exception:
    continue
  db.base_grammar(thy)
  words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text))
  anc = db.ancestors(thy) | {thy}
  for b in hol4.parse(path):
    if b.kind == 'ML':
      for tok, prec, ass, _ in hol4.fixities(b.text):
        hterm.add_infix(tok, prec, ass)
      continue
    if b.kind not in KINDS or not p.wanted(b): continue
    body = hol4.strip_comments(b.body)
    miss = []
    for nm in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", body))):
      kinds = [k for t, k in db.defs.get(nm, [])
               if t in anc and k in ('con', 'def', 'rel')]
      if not kinds: continue
      # the port may write the name with the prefix of the theory
      # that defines the constant, or of a record type, and it
      # renames a bound variable of that name with a prime
      if any(w == nm or w == nm + "'" or w.endswith('_' + nm)
             for w in words):
        continue
      # an overload of HOL4 that the port expands is gone on purpose
      if any((t, nm) in db.overloads for t in anc): continue
      miss.append(nm)
    tot += 1
    if miss:
      bad += 1
      print('%-22s %-28s %s' % (thy, b.name, ' '.join(miss[:8])))
print('%d definitions, %d with a name missing' % (tot, bad))
