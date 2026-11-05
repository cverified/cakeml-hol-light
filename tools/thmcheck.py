"""typecheck the statements of the port without loading it

  python3 -I tools/thmcheck.py [<file>...]

writes tmp/stmts.txt: every statement of the port
(or of the files named), with the file, the line and the name.
A session that has the port loaded reads that file (tmp/diag.ml)
and says of every statement whether it parses, whether it is a
formula, and what its free variables are, which is the fast way
to work on the statements of phase two: no run needed.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import stmts

ML = T + '../ml/'


def statements(path):
  """the name, the line and the statement text of every theorem of
     a file of the port"""
  return scan(open(path).read())


# the comments of a term of the port, which stand after // and run
# to the end of the line, are not part of the statement
strip_dslash = stmts.strip_dslash


def scan(text):
  """the same of the text of a ported file: the binding of every
     theorem (which is what names a phrase of the port and what a
     proof of the store names it by), its line and its statement"""
  for bind, _, _, line, stmt in stmts.theorems(text):
    yield bind, line, stmt


def files():
  out = []
  for dp, _, fs in os.walk(ML):
    for f in sorted(fs):
      if f.endswith('.ml'):
        out.append(os.path.join(dp, f))
  return sorted(out)


# a Parse.hide of the source, which the port writes as HOL Light's
# own hide_constant (tools/port.py): the list at the head of the
# file and the ones that a hide further down the source adds
HIDE = re.compile(r'^let _ = do_list hide_constant\s*\n?\s*'
                  r'\[(.*?)\];;', re.S | re.M)

# the pairs of a name and a constant that the file takes out of the
# interface, where it reads the name of a record field as a
# variable and needs the accessors of that field as well
HIDEC = re.compile(r'^let _ = hide_overloads\s*\n?\s*'
                   r'\[(.*?)\];;', re.S | re.M)


def hidden(path):
  """the names that the file hides while it reads a statement: the
     list at the head of it and the ones that a Parse.hide of the
     source adds further down, which this takes for the whole file
     -- the statements before such a line do not use the name, or
     the source could not hide it there"""
  out = []
  for m in HIDE.finditer(open(path).read()):
    out += re.findall(r'"([^"]+)"', m.group(1))
  return out


def hidden_consts(path):
  """the name and the constant of every pair that the file takes
     out of the interface (hide_overloads)"""
  out = []
  for m in HIDEC.finditer(open(path).read()):
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
