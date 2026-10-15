"""write the quotations of an ml file of the port as a file that
   parses them one by one, so that loading it in a session that has
   the file loaded says which quotation does not parse"""
import sys, re

src, out = sys.argv[1], sys.argv[2]
text = open(src).read()


def strip_comments(s):
  """blank out the ocaml comments, keeping the newlines, so that a
     backtick in a comment does not start a quotation"""
  res = []
  i = 0
  n = len(s)
  depth = 0
  while i < n:
    if s.startswith('(*', i):
      depth += 1; res.append('  '); i += 2; continue
    if depth and s.startswith('*)', i):
      depth -= 1; res.append('  '); i += 2; continue
    res.append(s[i] if (not depth or s[i] == '\n') else ' ')
    i += 1
  return ''.join(res)


text = strip_comments(text)
qs = []
for m in re.finditer(r'`([^`]*)`', text):
  if m.group(1).strip():
    qs.append((text[:m.start()].count('\n') + 1, m.group(1)))
res = ["""let cake_mark s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "/home/freek/claude/hol-light/cakeml/tmp/mark.txt" in
  output_string ch (s ^ "\\n"); close_out ch;;
"""]
for line, q in qs:
  res.append('(try ignore(`%s`) with Failure e ->\n'
             '   cake_mark ("line %d: " ^ e));;\n' % (q, line))
open(out, 'w').write('\n'.join(res))
print(len(qs))
