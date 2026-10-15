"""write an ml file of the port with a marker before every phrase,
   so that the output of loading it says which phrase fails"""
import sys, re

src, out = sys.argv[1], sys.argv[2]
text = open(src).read()
# the phrases of a file of the port end in ";;" at the end of a line
parts = re.split(r'(?<=;;)\n', text)
res = []
n = 0
for p in parts:
  if not p.strip():
    res.append(p); continue
  n += 1
  res.append('print_string "@@%d:%s@@\\n";;\n%s'
             % (n, p.strip().split('\n')[0][:60].replace('"', "'"), p))
open(out, 'w').write('\n'.join(res))
print(n)
