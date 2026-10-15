"""write a file that parses the clauses of a definition of the port
   one by one and in growing prefixes, to find the ones that clash:

     python3 tools/bisect.py <ml file> <let name> > tmp/b.ml
"""
import re, sys

path, name = sys.argv[1], sys.argv[2]
t = open(path).read()
m = re.search(r"let %s = cake_define(?:_wf)?\n(  `[^`]*`\n)?  `([^`]*)`;;"
              % re.escape(name), t)
body = m.group(2)
cls = [c.strip().rstrip('/\\').strip()
       for c in re.split(r'/\\\n', body)]
out = ['print_thm_full := false;;\n']
for i, c in enumerate(cls):
  out.append('(try ignore(`%s`) with Failure e ->\n'
             '   print_string ("CL %d: " ^ e ^ "\\n"));;\n' % (c, i))
for k in range(2, len(cls) + 1):
  out.append('(try ignore(`%s`) with Failure e ->\n'
             '   print_string ("UPTO %d: " ^ e ^ "\\n"));;\n'
             % (' /\\\n'.join(cls[:k]), k))
sys.stdout.write(''.join(out))
