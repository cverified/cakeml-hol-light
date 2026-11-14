"""the attributes of a theorem of a source are in its port

  python3 -I tools/attrs.py [<theory>...]

A theorem of a HOL4 source can carry attributes ([simp],
[compute], [local], [allow_rebind]), which are part of what the
source says, so the port keeps them in the name that it gives the
statement (CLAUDE.md).  All but one are not load bearing -- phase
three does not replay HOL4's automation -- but a statement that
loses one does not read the same as the source any more.

The one that is load bearing is [simp]: the port has a simp set
of its own (tactics/simpset.ml), so a theorem that HOL4 puts in
it the port puts in it too, with a call after the theorem.  A
definition can carry it as well, and then it is the equations of
the definition that go in.

This says which statements of the port have other attributes than
the theorem of the source has, and which definitions of a source
that are in HOL4's simp set are not in the port's.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4, stmts

ML = T + '../ml/'


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  n = bad = own = 0
  nd = badd = 0
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml' or (want and thy not in want): continue
    try:
      text = open(ML + db.mlpath_of(thy)).read()
    except OSError:
      continue
    # a definition that HOL4 puts in its simp set: the port puts
    # the binding it gives the definition in its own, and that
    # binding is the name of the source or that name with the
    # theory in front of it (tools/port.py's bindname)
    sp = stmts.simped(text)
    for b in hol4.parse(path):
      if b.kind != 'Definition' or not b.name: continue
      if 'simp' not in (b.attrs or []): continue
      nd += 1
      if b.name in sp or '%s_%s' % (thy, b.name) in sp: continue
      # a definition that the port does not make has no binding
      # to put in the set
      if ('let %s =' % b.name not in text and
          'let %s,' % b.name not in text and
          'let %s_%s' % (thy, b.name) not in text): continue
      badd += 1
      if badd <= 20:
        print('%s$%s: the source has it in the simp set and the '
              'port has not' % (thy, b.name))
    # the attributes that the port gives every name it states,
    # out of the comment over the statement (tools/stmts.py); a
    # theorem that the source states as the value of another one
    # is a binding of that one, with its attributes over it
    got = {}
    for _, nm, at, _, _ in (stmts.theorems(text) +
                            stmts.aliases(text)):
      got.setdefault(nm, []).append(list(at))
    # the attributes that the source gives every name it binds (a
    # name that it binds more than once is in with each of them)
    src = {}
    for b in hol4.parse(path):
      # a theorem that the ML code of the source states itself has
      # no attributes (HOL4's val foo = Q.prove(`...`, tactic))
      if b.kind == 'ML':
        for nm, _, _ in hol4.ml_theorems(b.text or ''):
          src.setdefault(nm, []).append([])
        continue
      if b.kind not in ('Theorem', 'Triviality', 'ThmValue'): continue
      if not b.name: continue
      at = list(b.attrs or [])
      # HOL4's Triviality is a Theorem[local], which the port says
      # with the attribute itself
      if b.kind == 'Triviality' and 'local' not in at:
        at.append('local')
      src.setdefault(b.name, []).append(sorted(at))
    # a theorem that the port has as a pointer is not a statement
    # of it, so what it states has to be one of what the source
    # binds under that name, not the one in the same place
    for nm, mines in got.items():
      # a lemma of the port's own (one that an override table adds
      # before a proof that needs it) is no theorem of the source,
      # so there is nothing to compare its name with
      if nm not in src:
        own += len(mines)
        continue
      left = list(src.get(nm, []))
      for mine in mines:
        n += 1
        if sorted(mine) in left:
          left.remove(sorted(mine))
          continue
        bad += 1
        if bad <= 20:
          print('%s$%s: the port says %s and the source %s'
                % (thy, nm, sorted(mine) or 'none',
                   ' or '.join(str(a or 'none') for a in
                               src.get(nm, [])) or 'nothing'))
  print('%d statements of the port, %d with other attributes than '
        'the source gives the theorem' % (n, bad))
  print('%d lemmas of the port\'s own, which no theorem of a '
        'source names' % own)
  print('%d definitions of a source in HOL4\'s simp set, %d of '
        'them not in the port\'s' % (nd, badd))
  return bad + badd


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
