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

# phase two: the theorems of a CakeML source are in the port as
# well, with CHEAT_TAC where HOL4 has its proof.  A theorem is in
# when the port binds it (let <the name of the source> = prove),
# or binds it under the name of its theory and says the name of
# the source in the comment over it.
THMKINDS = ('Theorem', 'Triviality', 'ThmValue')


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


def bound(text, thy, name):
  """does the port bind a theorem of this name?  The binding is
     the name of the source, or that name with the theory in front
     of it where another file of the port has the name already
     (tools/port.py's bindname)"""
  for nm in (portmod.ocaml_name(name),
             portmod.ocaml_name(thy + '_' + name)):
    if re.search(r'^let %s = prove$' % re.escape(nm), text, re.M) or \
       re.search(r'^let %s = [A-Za-z_]' % re.escape(nm), text, re.M) or \
       re.search(r'^let %s =$' % re.escape(nm), text, re.M):
      return True
  return False


def pointed(flat, name):
  """does a pointer of the port name this theorem?  Where the port
     cannot state a theorem it writes a comment that points at the
     lines of the source and names it (CLAUDE.md), so a theorem
     that is neither stated nor pointed at is one that a reader of
     the two files side by side would miss"""
  if not name: return True
  return bool(re.search(r'\(\* HOL4 [^*]*%s' % re.escape(name), flat))


def main():
  db = dbmod.Db()
  thys = sys.argv[1:] or [t for t, _, k in db.order]
  tot = [0, 0, 0, 0, 0, 0]
  rows = []
  for thy in thys:
    path = db.thy_of_file.get(thy)
    if not path: continue
    p = portmod.Porter(db, thy)
    try:
      raw = open(portmod.ML + db.mlpath_of(thy)).read()
      text = portmod.strip_ml(raw, False)
      flat = ' '.join(raw.split())
    except Exception:
      text = flat = ''
    want = have = twant = thave = nopoint = 0
    missing = []
    tmissing = []
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
      elif b.kind in THMKINDS:
        if not p.wanted(b): continue
        twant += 1
        if b.name and (
            bound(text, thy, b.name) or
            re.search(r'\(\* %s[][\s*]' % re.escape(b.name), raw)):
          thave += 1
        else:
          tmissing.append('%s %s' % (b.kind, b.name or '(a value)'))
          if not pointed(flat, b.name): nopoint += 1
        continue
      elif b.kind == 'ML':
        # a theorem that the ML code of the source states itself
        # (val foo = Q.prove(`...`, tactic)) is a theorem of it;
        # of a HOL4 library theory the port has the definitions
        if p.kind == 'lib': continue
        for nm, _, _ in hol4.ml_theorems(b.text or ''):
          twant += 1
          if (bound(text, thy, nm) or
              re.search(r'\(\* %s[][\s*]' % re.escape(nm), raw)):
            thave += 1
          else:
            tmissing.append('ML %s' % nm)
            if not pointed(flat, nm): nopoint += 1
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
    tot[3] += twant; tot[4] += thave; tot[5] += len(tmissing)
    tot.append(0) if len(tot) < 7 else None
    tot[6] += nopoint
    rows.append((thy, want, have, missing, twant, thave, tmissing))
  print('%-28s %6s %6s %8s %6s' % ('theory', 'blocks', 'in',
                                   'theorems', 'in'))
  for thy, want, have, missing, twant, thave, tmissing in rows:
    if want != have or twant != thave or '-v' in sys.argv:
      print('%-28s %6d %6d %8d %6d' % (thy, want, have, twant, thave))
      for m in missing: print('        missing:', m)
      for m in tmissing[:4]: print('        not stated:', m)
      if len(tmissing) > 4:
        print('        not stated: and %d more' % (len(tmissing) - 4))
  print('%-28s %6d %6d %8d %6d  (%d blocks, %d theorems missing)'
        % ('TOTAL', tot[0], tot[1], tot[3], tot[4], tot[2], tot[5]))
  print('%d of the %d theorems that the port does not state have no '
        'pointer that names them' % (tot[6] if len(tot) > 6 else 0,
                                     tot[5]))


main()
