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
  """the name, the line and the statement text of every theorem of
     a file of the port"""
  return scan(open(path).read())


def strip_dslash(text):
  """the text without the comments of a term of the port, which
     stand after // and run to the end of the line (a comment of
     the source that is inside a block keeps its place that way).
     What follows such a comment on its line is the quotation
     closing around it, which stays: a comment of the port holds
     no backquote (one would end the quotation of OCaml, so the
     port writes such a comment outside it), and the one at the
     end of a term has the closing ` of it on its own line"""
  return re.sub(r'(?m)^(\s*`?)//[^`\n]*', r'\1', text)


def scan(text):
  """the same of the text of a ported file"""
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
    yield (s.group(1), text[:m.start()].count('\n') + 1,
           strip_dslash(text[i + 1:j]))


def files():
  out = []
  for dp, _, fs in os.walk(ML):
    for f in sorted(fs):
      if f.endswith('.ml'):
        out.append(os.path.join(dp, f))
  return sorted(out)


HIDE = re.compile(r'^cake_hide \[(.*?)\];;', re.S | re.M)


def hidden(path):
  """the names that the file hides while it reads a statement: the
     list at the head of it and the ones that a Parse.hide of the
     source adds further down (cake_hide_more), which this takes
     for the whole file -- the statements before such a line do
     not use the name, or the source could not hide it there"""
  txt = open(path).read()
  m = HIDE.search(txt)
  out = re.findall(r'"([^"]+)"', m.group(1)) if m else []
  for m in re.finditer(r'cake_hide_more \[([^]]*)\]', txt):
    out += re.findall(r'"([^"]+)"', m.group(1))
  return out


def hidden_consts(path):
  """the name and the constant of every pair that the file takes
     out of the interface (cake_hide_consts)"""
  out = []
  for m in re.finditer(r'cake_hide_consts\s*\n?\s*\[([^]]*)\]',
                       open(path).read()):
    out += re.findall(r'"([^"]+)"\s*,\s*"([^"]+)"', m.group(1))
  return out


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
      hc = hidden_consts(p)
      if hc:
        o.write('@@@HIDEC\t%s\n'
                % ' '.join('%s,%s' % x for x in hc))
      for name, line, stmt in statements(p):
        o.write('@@@\t%s\t%d\t%s\n%s\n' % (rel, line, name, stmt))
        n += 1
  print('%d statements of %d files in tmp/stmts.txt' % (n, len(paths)))


if __name__ == '__main__':
  main()
