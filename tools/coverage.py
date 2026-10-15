"""what of every file of the port is there and what is not

  python3 -I tools/coverage.py [theory...]

For every block of a HOL4 source that the port has to have, this
checks that the names it defines are in the file of the port (a
PENDING comment does not count).  It reports the counts and the
blocks that are missing.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, port as portmod

KINDS = ('Datatype', 'Definition', 'Inductive', 'CoInductive')


def names_of(b, p):
  """the names that a block defines, as (name, is a type)"""
  if b.kind == 'Datatype':
    out = []
    for ty, cons, flds in hol4.datatype_names(b.body):
      out += [(ty, True)] + [(c, False) for c in cons]
    return out
  if b.kind == 'Type':
    return [(b.name, True)] if b.name else []
  return [(nm, False) for nm in dbmod.definition_names(b.body)]


def main():
  db = dbmod.Db()
  thys = sys.argv[1:] or [t for t, _, k in db.order]
  tot = [0, 0, 0]
  rows = []
  for thy in thys:
    path = db.thy_of_file.get(thy)
    if not path: continue
    p = portmod.Porter(db, thy)
    try:
      text = portmod.strip_ml(open(portmod.ML +
                                   db.mlpath_of(thy)).read(), False)
    except Exception:
      text = ''
    want = have = 0
    missing = []
    db.base_grammar(thy)
    for b in hol4.parse(path):
      if b.kind == 'ML':
        for tok, prec, ass, _ in hol4.fixities(b.text):
          hterm.add_infix(tok, prec, ass)
      if b.kind == 'Type':
        if not p.wanted(b): continue
        try:
          ty = hterm.parse_type_text(dbmod.strip_quote(b.body))
          if hterm.type_vars_of(ty): continue
        except Exception:
          continue
      elif b.kind not in KINDS or not p.wanted(b):
        continue
      want += 1
      nms = names_of(b, p)
      ok = True
      for nm, isty in nms:
        new = p.tnm(nm) if isty else p.nm_defined(nm)
        if not re.search(r'\b%s\b' % re.escape(new), text) and \
           not re.search(r'\b%s\b' % re.escape(nm), text):
          ok = False
      if ok: have += 1
      else:
        missing.append('%s %s' % (b.kind, b.name or
                                  [n for n, _ in nms[:1]]))
    tot[0] += want; tot[1] += have; tot[2] += len(missing)
    rows.append((thy, want, have, missing))
  print('%-28s %6s %6s' % ('theory', 'blocks', 'in'))
  for thy, want, have, missing in rows:
    if want != have or '-v' in sys.argv:
      print('%-28s %6d %6d' % (thy, want, have))
      for m in missing: print('        missing:', m)
  print('%-28s %6d %6d  (%d missing)' % ('TOTAL', tot[0], tot[1], tot[2]))


main()
