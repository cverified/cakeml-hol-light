"""mkabstr.py <file of the port> <out> : the file with CHEAT_TAC in
   the place of every tactic, for a load that only puts the
   statements of the file in a session.

     python3 -I tools/mkabstr.py <file> <out>

   The output goes in cakeml/tmp/ (which is not in the repo): it
   is a copy of a generated file and goes stale with it.  For
   data_to_word_memoryProof the abstract is 12250 lines of the
   65831 and loads in 134 seconds where the file itself takes
   1431 (both on top of hol-pfbase, which holds the closure).

   Only the tactic argument of a top level `let <name> = prove`
   goes: a definition (cake_define...) stays, because what a later
   file needs of a definition is its clauses.
"""
import re, sys


def scan(s, i, stop):
  """the index of the first character at bracket depth 0 that stop
     says yes to, from i, counting (), [] and skipping comments and
     quotations"""
  depth = 0
  cdepth = 0
  inq = False
  while i < len(s):
    c = s[i]
    if not inq and cdepth == 0 and c == '`':
      inq = True; i += 1; continue
    if inq:
      if c == '`': inq = False
      i += 1; continue
    if s[i:i+2] == '(*':
      cdepth += 1; i += 2; continue
    if s[i:i+2] == '*)' and cdepth:
      cdepth -= 1; i += 2; continue
    if cdepth:
      i += 1; continue
    if c in '([':
      depth += 1
    elif c in ')]':
      if depth == 0 and stop(c, depth): return i
      depth -= 1
    elif depth == 0 and stop(c, depth):
      return i
    i += 1
  return -1


def main(argv):
  s = open(argv[1]).read()
  out = []
  at = 0
  n = 0
  pat = r"(?m)^let [a-zA-Z_][A-Za-z0-9_']* = prove\b"
  for m in re.finditer(pat, s):
    if m.start() < at: continue
    # the opening bracket of the prove call
    i = s.index('(', m.end())
    # the comma that separates the statement from the tactic, and
    # the bracket that closes the call, both at depth 0 inside it
    comma = scan(s, i + 1, lambda c, d: c == ',')
    if comma < 0: continue
    close = scan(s, comma + 1, lambda c, d: c == ')')
    if close < 0: continue
    out.append(s[at:comma + 1])
    out.append('\n  CHEAT_TAC')
    at = close
    n += 1
  out.append(s[at:])
  open(argv[2], 'w').write(''.join(out))
  print('%d tactics cheated' % n)


main(sys.argv)
