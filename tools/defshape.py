"""a definition of the port has the shape of the source's

  python3 -I tools/defshape.py [<theory>...]

The same as `tools/stmtshape.py` for the definitions of phase one:
it counts the connectives of the body of a `Definition` of a
source and of the quotations that the port has for it, and says
where they differ.  A conjunct or a hypothesis that fell away is a
difference of the count, and so is the `~0w` of HOL4 (the word of
all ones) read as the negation of a number.

A difference is not always a fault, and more often not than with a
statement: the port expands an `Overload` that it cannot declare,
writes HOL4's `case` as a `match` and a pattern that HOL4 writes
with a condition as a clause of its own, and a definition that
HOL4 makes with ML code is in the port as the port makes it.  The
definitions that a reading has found right are in
`tools/shapeok.txt` with the reason, as the statements are.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4, overrides, stmtshape

ML = T + '../ml/'

# the phrases of a ported file and the names they define
LET = re.compile(r"^let\s+([A-Za-z_][A-Za-z0-9_',\s]*?)\s*=", re.M)


def phrases(text):
  """the top level phrases of a ported file, as (names, text)"""
  out = []
  for m in LET.finditer(text):
    i = text.find(';;\n', m.end())
    j = text.find('\nlet ', m.end())
    end = len(text) if i < 0 else i
    if 0 <= j < end: end = j
    names = [n.strip() for n in m.group(1).split(',')]
    out.append((names, text[m.end():end]))
  return out


def quotations(text):
  """the terms of a phrase of the port, which is what to count"""
  return ' '.join(re.findall(r'`([^`]*)`', text))


def drop_and(counts):
  """the counts with the conjunctions zeroed out, and with the
     negations and the complements of a word counted together: the
     ~ of HOL4 is both, and which one it is depends on the type of
     what it is applied to"""
  ops = [o for o, _, _ in stmtshape.OPS]
  i, j = ops.index('/\\'), ops.index('~'), 
  k = ops.index('word_not')
  out = list(counts)
  out[i] = 0
  out[j] += out[k]
  out[k] = 0
  return tuple(out)


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  ok = stmtshape.reviewed()
  n = bad = 0
  rows = []
  for thy, path, kind in dbmod.load_order():
    if want and thy not in want: continue
    try:
      text = open(ML + db.mlpath_of(thy)).read()
    except (OSError, KeyError):
      continue
    # the quotations of the port, by the name that the phrase binds
    got = {}
    for names, body in phrases(text):
      for nm in names:
        got.setdefault(nm, quotations(body))
    for b in hol4.parse(path):
      if b.kind != 'Definition' or not b.name: continue
      mine = got.get(b.name)
      # a definition that the port has under another name, or that
      # it makes by hand, is not compared
      if not mine: continue
      src = stmtshape.LIT.sub(
        '', hol4.strip_comments(dbmod.strip_quote(b.body or '')))
      if '^' in src: continue
      src = re.sub(r'~\s*(?=(0x[0-9A-Fa-f]+|[0-9]+)w\b)',
                   ' word_not ', src)
      src = re.sub(r'~\s*(?=[&0-9])', '', src)
      mine = stmtshape.LIT.sub('', mine)
      n += 1
      # the clauses of a definition are one conjunction in HOL4 and
      # a quotation each in the port (cake_define_list), so the
      # conjunctions of a definition say nothing and are left out
      a = drop_and(stmtshape.shape(src, 0))
      z = drop_and(stmtshape.shape(mine, 1))
      if a != z:
        if '%s$%s' % (thy, b.name) in ok: continue
        bad += 1
        rows.append((thy, b.name,
                     [(o, x, y)
                      for (o, _, _), x, y in zip(stmtshape.OPS, a, z)
                      if x != y]))
  for thy, nm, diff in rows:
    print('%s$%s: %s' % (
      thy, nm,
      ', '.join('%s %d in the source and %d in the port'
                % (o, x, y) for o, x, y in diff)))
  print('%d definitions of the port, %d that count the connectives '
        'of the source differently and that tools/shapeok.txt does '
        'not account for' % (n, bad))
  return bad


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
