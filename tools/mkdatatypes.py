"""turn the harvest of tools/harvest_datatypes.ml into the table
   that ml/lib/fast.ml reads

  python3 -I tools/mkdatatypes.py < tmp/datatypes.txt \
      > ml/lib/datatypes.txt

The harvest is one record to a block; the table is one record to a
line, in five fields that a tab separates: the specification with
its whitespace taken out (the key), the types with their arity,
the constructors with their type, the induction theorem and the
recursion theorem.  A term is written with its line breaks taken
out, which HOL Light's parser does not mind.
"""
import sys, re


def records(lines):
  i, n = 0, len(lines)
  while i < n:
    if lines[i] != 'SPEC':
      i += 1; continue
    i += 1
    spec = []
    while i < n and lines[i] != 'ENDSPEC':
      spec.append(lines[i]); i += 1
    i += 1
    tys, cons, ind, rec = [], [], '', ''
    while i < n and lines[i] != 'END':
      l = lines[i]
      if l.startswith('TYPE '):
        _, nm, ar = l.split()
        tys.append((nm, ar)); i += 1
      elif l.startswith('CON '):
        cons.append((l[4:], lines[i + 1])); i += 2
      elif l in ('INDUCT', 'RECURSION'):
        kind = l; i += 1
        body = []
        while i < n and lines[i] != 'ENDTHM':
          body.append(lines[i]); i += 1
        i += 1
        if kind == 'INDUCT': ind = ' '.join(body)
        else: rec = ' '.join(body)
      else:
        i += 1
    i += 1
    yield '\n'.join(spec), tys, cons, ind, rec


def main():
  lines = [l.rstrip('\n') for l in sys.stdin]
  n = 0
  seen = set()
  for spec, tys, cons, ind, rec in records(lines):
    key = re.sub(r'\s+', '', spec)
    if not key or not ind or not rec or key in seen: continue
    seen.add(key)
    flat = lambda s: ' '.join(s.split())
    print('\t'.join([key,
                     ','.join('%s:%s' % t for t in tys),
                     ';'.join('%s:%s' % (c, flat(t)) for c, t in cons),
                     flat(ind), flat(rec)]))
    n += 1
  print('%d datatypes' % n, file=sys.stderr)


main()
