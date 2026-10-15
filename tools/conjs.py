"""write the clause lists of an ml file of the port as a file that
   tries cake_conj_list on each of them, so that loading it in a
   session that has the file loaded says which definition the port
   has to assume clause by clause"""
import sys, re

src, out = sys.argv[1], sys.argv[2]
text = open(src).read()
res = ["""let cake_mark s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "/home/freek/claude/hol-light/cakeml/tmp/mark.txt" in
  output_string ch (s ^ "\\n"); close_out ch;;
"""]
n = 0
for m in re.finditer(r'let (\w+) = cake_define_list\n(  \[.*?\]);;\n',
                     text, re.S):
  n += 1
  res.append('(try ignore(cake_conj_list %s) with Failure e ->\n'
             '   cake_mark ("%s: " ^ e));;\n' % (m.group(2), m.group(1)))
open(out, 'w').write('\n'.join(res))
print(n)
