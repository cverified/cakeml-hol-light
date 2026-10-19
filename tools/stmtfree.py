"""a free variable of a statement whose name HOL4 has in its scope

  python3 -I tools/stmtfree.py

A statement of the port is read with the names that no theory of
the grammar of its source defines hidden (`cake_hide`), because
HOL4 reads those as variables of the statement.  A free variable
that is left whose name a theory of that grammar *does* define is
the other way round: HOL4 reads a constant there where the port
reads a variable, so the statement says something weaker than the
source does.

The free variables come out of `tmp/diag.out`, which
`tools/bin/diag` writes in a session that has the port loaded.  A
name that the port gives a record field is left out: a bare field
name is no constant of HOL4 either (the statements that read a
field through one all the same are what `tools/diag.py` reports).
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, thmcheck, overrides


def main():
  db = dbmod.Db()
  thy_of = {}
  for thy, path, kind in dbmod.load_order():
    thy_of[db.mlpath_of(thy)] = thy
  flds = db.field_tokens()
  hidden = {}
  rows = []
  for l in open(T + '../tmp/diag.out'):
    f = l.rstrip('\n').split('\t')
    if len(f) < 5 or f[0] != 'FREE': continue
    p = re.sub(r'^.*/ml/|^\.\./tmp/[a-z0-9]*/', '', f[1])
    thy = thy_of.get(p)
    if not thy: continue
    anc = db.gram_ancestors(thy)
    # a name that the file hides is a variable of the statement
    # because HOL4 hides it as well (a Parse.hide of the source,
    # or a constant that HOL4 cannot have at all)
    hid = set(hidden.setdefault(
      p, thmcheck.hidden(T + '../ml/' + p))) | overrides.HOL4_HIDDEN
    for v in f[4].split():
      n = v.split(':')[0]
      if n in flds or n in hid: continue
      ts = sorted({t for t, k in db.defs.get(n, [])
                   if k in ('def', 'con', 'rel') and t in anc})
      if ts: rows.append((thy, f[3], n, ts[0]))
  by = collections.Counter(r[2] for r in rows)
  for thy, nm, n, t in rows[:40]:
    print('%-26s %-34s %s of %s' % (thy, nm[:34], n, t))
  print('%d free variables of %d statements whose name a theory of '
        'the scope defines' % (len(rows), len({(r[0], r[1])
                                               for r in rows})))
  if by:
    print('the names: ' + ', '.join('%s (%d)' % (k, v)
                                    for k, v in by.most_common(12)))


if __name__ == '__main__':
  main()
