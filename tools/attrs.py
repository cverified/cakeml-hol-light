"""the attributes of a theorem of a source are in its port

  python3 -I tools/attrs.py [<theory>...]

A theorem of a HOL4 source can carry attributes ([simp],
[compute], [local], [allow_rebind]), which are part of what the
source says, so the port keeps them in the name that it gives the
statement (CLAUDE.md).  They are not load bearing -- phase three
does not replay HOL4's automation -- but a statement that loses
one does not read the same as the source any more.

This says which statements of the port have other attributes than
the theorem of the source has.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4

ML = T + '../ml/'

# the name of a statement of the port, with its attributes in it
STMT = re.compile(r'cake_(?:theorem|alias)\s*\n?\s*"([^"]+)"')


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  n = bad = 0
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml' or (want and thy not in want): continue
    try:
      text = open(ML + db.mlpath_of(thy)).read()
    except OSError:
      continue
    # the attributes that the port gives every name it states
    got = {}
    for m in STMT.finditer(text):
      s = m.group(1)
      k = s.find('[')
      nm = s[:k] if k >= 0 else s
      at = s[k+1:-1].split(',') if k >= 0 and s.endswith(']') else []
      got.setdefault(nm, []).append([a for a in at if a])
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
  return bad


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
