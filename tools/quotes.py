"""write the quotations of an ml file of the port as a file that
   parses them one by one, so that loading it in a session that has
   the file loaded says which quotation does not parse"""
import sys, re

src, out = sys.argv[1], sys.argv[2]
text = open(src).read()
# the quotations of the file, with the line they start on
qs = []
for m in re.finditer(r'`([^`]*)`', text):
  qs.append((text[:m.start()].count('\n') + 1, m.group(1)))
res = ["""let cake_mark s =
  let o = open_out_gen [Open_append; Open_creat] 0o644
            "/home/freek/claude/hol-light/cakeml/tmp/mark.txt" in
  output_string o (s ^ "\\n"); close_out o;;
"""]
for line, q in qs:
  res.append('(try ignore(`%s`) with Failure e ->\n'
             '   cake_mark ("line %d: " ^ e));;\n' % (q, line))
open(out, 'w').write('\n'.join(res))
print(len(qs))
