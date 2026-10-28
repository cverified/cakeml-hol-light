# landblock.py <try file> <name> ... : the lemmas of a round as the
# text of a shared block.
#
# A round writes its lemmas as
#
#   let foo = btry "foo" `<statement>` (fun () -> <tactic>);;
#
# and a block of tools/overrides.py wants
#
#   let foo = prove
#    (`<statement>`,
#     <tactic>);;
#
# Doing that by hand cost three verifies in the round that landed
# gen_gc_partial_thm: the thunk left around the tactic (`prove`
# wants the tactic itself), the statement's own
# `cake_as_vars (fun () -> ...)` taken for the tactic's thunk, and
# the parenthesis of `prove` with nothing to close it.
import re, sys

def depth(txt):
  """the bracket depth of a piece of OCaml, comments, strings and
  HOL Light quotations skipped"""
  d = 0
  i = 0
  n = len(txt)
  while i < n:
    if txt.startswith('(*', i):
      j = txt.find('*)', i)
      i = j + 2 if j >= 0 else n
      continue
    if txt[i] in '`"':
      q = txt[i]
      j = txt.find(q, i + 1)
      i = j + 1 if j >= 0 else n
      continue
    if txt[i] == '(':
      d += 1
    elif txt[i] == ')':
      d -= 1
    i += 1
  return d

def one(s, name):
  pat = r'(?m)^let %s = btry "%s"$' % ((re.escape(name),) * 2)
  m = re.search(pat, s)
  if not m:
    sys.exit('landblock: %s is not an attempt of the file' % name)
  # the tactic's thunk is the one that starts a line: a statement
  # written with cake_as_vars has a thunk of its own, inside
  m2 = re.search(r'(?m)^ ?\(fun \(\) ->\n', s[m.start():])
  if not m2:
    sys.exit('landblock: %s has no tactic thunk' % name)
  cut = m.start() + m2.start()
  stmt = s[m.end():cut].rstrip()
  rest = s[m.start() + m2.end():]
  end = rest.index(';;\n')
  tac = rest[:end].rstrip()
  # the thunk's own closing parenthesis ends the tactic
  if tac.endswith(')'):
    tac = tac[:-1].rstrip()
  out = ('let %s = prove\n (%s,\n  %s);;\n'
         % (name, stmt.strip(), tac.strip()))
  d = depth(out[out.index('prove'):])
  if d > 0:
    j = out.rindex(';;')
    out = out[:j] + ')' * d + out[j:]
  elif d < 0:
    sys.exit('landblock: %s has %d bracket(s) too many' % (name, -d))
  return out

def main(argv):
  if len(argv) < 3:
    sys.exit('usage: landblock.py <try file> <name> ...')
  s = open(argv[1]).read()
  sys.stdout.write('\n'.join(one(s, n) for n in argv[2:]))

main(sys.argv)
