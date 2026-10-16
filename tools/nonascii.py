"""the characters outside ASCII that the port writes in a term

     python3 -I tools/nonascii.py

   The comments of the port keep the HOL4 sources as they are, so
   they may have anything in them; a term may not, as HOL Light's
   lexer stops at a character it does not know ("Unparsed input"
   for bvi_tmcProof's hypothesis, which had a variable of HOL4's
   s'<superscript 3>' kind in it)."""
import os, collections

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + '/ml'


def strip_comments(s):
  out = []
  i = 0
  depth = 0
  n = len(s)
  while i < n:
    if s.startswith('(*', i): depth += 1; i += 2; continue
    if s.startswith('*)', i) and depth: depth -= 1; i += 2; continue
    if not depth: out.append(s[i])
    i += 1
  return ''.join(out)


bad = collections.Counter()
where = {}
for dp, dn, fn in os.walk(C):
  for f in sorted(fn):
    if not f.endswith('.ml'): continue
    p = os.path.join(dp, f)
    s = strip_comments(open(p, errors='replace').read())
    for ch in set(s):
      if ord(ch) > 127:
        bad[ch] += s.count(ch)
        where.setdefault(ch, p[len(C) + 1:])
for ch, c in bad.most_common():
  print('%6d U+%04X %r  %s' % (c, ord(ch), ch, where[ch]))
print('%d characters outside ASCII in the terms of the port'
      % sum(bad.values()))
