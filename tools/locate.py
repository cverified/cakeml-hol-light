"""write an ml file of the port with a marker before every phrase,
   so that tmp/mark.txt says which phrase fails"""
import sys, re

src, out = sys.argv[1], sys.argv[2]
text = open(src).read()
# the phrases of a file of the port end in ";;" at the end of a line
parts = re.split(r'(?<=;;)\n', text)
res = ["""let cake_mark s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "/home/freek/claude/hol-light/cakeml/tmp/mark.txt" in
  output_string ch (s ^ "\\n"); close_out ch;;
"""]
n = 0
for p in parts:
  if not p.strip():
    res.append(p); continue
  n += 1
  # the text of the mark is an OCaml string, so a backslash in it
  # (the \\ of a HOL4 tactic) is escaped; one at the end would
  # otherwise escape the quote that closes the string
  mark = p.strip().split('\n')[0][:60]
  mark = mark.replace('\\', '\\\\').replace('"', "'")
  res.append('cake_mark "%d: %s";;\n%s' % (n, mark, p))
open(out, 'w').write('\n'.join(res))
print(n)
