"""typecheck the statements of the port without loading it

  python3 -I tools/thmcheck.py [<file>...]

writes tmp/stmts.txt: every `cake_theorem` statement of the port
(or of the files named), with the file, the line and the name.
A session that has the port loaded reads that file (tmp/diag.ml)
and says of every statement whether it parses, whether it is a
formula, and what its free variables are, which is the fast way
to work on the statements of phase two: no run needed.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'

STR = re.compile(r'"((?:[^"\\]|\\.)*)"')


def statements(path):
  """the name, the line and the statement text of every theorem"""
  text = open(path).read()
  for m in re.finditer(r'\bcake_theorem\b', text):
    s = STR.search(text, m.end())
    if not s or text[m.end():s.start()].strip():
      continue
    i = text.find('`', s.end())
    if i < 0:
      continue
    j = text.find('`', i + 1)
    if j < 0:
      continue
    yield s.group(1), text[:m.start()].count('\n') + 1, text[i + 1:j]


def files():
  out = []
  for dp, _, fs in os.walk(ML):
    for f in sorted(fs):
      if f.endswith('.ml'):
        out.append(os.path.join(dp, f))
  return sorted(out)


HIDE = re.compile(r'^cake_hide \[(.*?)\];;', re.S | re.M)


def hidden(path):
  """the names that the file hides while it reads a statement"""
  m = HIDE.search(open(path).read())
  return re.findall(r'"([^"]+)"', m.group(1)) if m else []


def main():
  args = sys.argv[1:]
  paths = [os.path.abspath(a) for a in args] if args else files()
  n = 0
  with open(T + '../tmp/stmts.txt', 'w') as o:
    for p in paths:
      rel = os.path.relpath(p, ML)
      hid = hidden(p)
      if hid:
        o.write('@@@HIDE\t%s\n' % ' '.join(hid))
      for name, line, stmt in statements(p):
        o.write('@@@\t%s\t%d\t%s\n%s\n' % (rel, line, name, stmt))
        n += 1
  print('%d statements of %d files in tmp/stmts.txt' % (n, len(paths)))


if __name__ == '__main__':
  main()
