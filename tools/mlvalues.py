"""the theorems that HOL4 states as the value of an ML expression

  python3 -I tools/mlvalues.py [-v]

A HOL4 source may bind a theorem to what an ML expression computes
(`Theorem foo = bar |> SRULE [...]`, `val foo = theorem "foo_ind"`,
`LIST_CONJ (map ...)`), and the port cannot evaluate that: it puts
a pointer at the source in its place and the theorem is one of the
ones it does not state (tools/coverage.py).

This groups them by the shape of the expression, so that the ones
that are a binding of something the port already has are told from
the ones whose statement has to be worked out by hand.  With -v it
prints each one.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4

SHAPES = [
  (re.compile(r'^\s*(?:definition|theorem)\s*"'), 'a theorem or a '
   'definition of the same source, by its name'),
  (re.compile(r'^\s*[A-Za-z_][A-Za-z_0-9\']*\s*$'), 'another '
   'theorem, by its name'),
  (re.compile(r'\|>'), 'a theorem put through a rule (|>)'),
  (re.compile(r'\bLIST_CONJ\b'), 'a conjunction of a list of them'),
  (re.compile(r'\bCONJUNCTS?\b'), 'a conjunct of one'),
  (re.compile(r'\bSIMP_RULE\b|\bSRULE\b|\bREWRITE_RULE\b'),
   'a theorem rewritten'),
  (re.compile(r'\bmap\b|\bList\.'), 'a list that ML code builds'),
]


def shape(text):
  for r, name in SHAPES:
    if r.search(text): return name
  return 'something else'


def main():
  verbose = '-v' in sys.argv[1:]
  db = dbmod.Db()
  kinds = collections.Counter()
  rows = []
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml': continue
    for b in hol4.parse(path):
      if b.kind != 'ThmValue' or not b.name: continue
      txt = hol4.thmvalue_text(b.text) if hasattr(
        hol4, 'thmvalue_text') else (b.text or '')
      body = re.sub(r'^.*?=', '', txt, count=1, flags=re.S).strip()
      k = shape(body)
      kinds[k] += 1
      rows.append((thy, b.name, k, ' '.join(body.split())[:60]))
  n = sum(kinds.values())
  print('%d theorems that HOL4 states as the value of an ML '
        'expression' % n)
  for k, c in kinds.most_common():
    print('%5d  %s' % (c, k))
  if verbose:
    for thy, nm, k, body in rows:
      print('%-26s %-34s %s' % (thy, nm, body))


if __name__ == '__main__':
  main()
