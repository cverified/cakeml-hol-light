"""split the statements that a session cannot read into their parts

  python3 -I tools/bisect.py <file> <name> [<name>...]
  python3 -I tools/bisect.py --unstated

writes tmp/stmts.txt with the parts of every statement named: the
whole statement, then its top level conjuncts, then the two sides
of every implication in them.  A session that reads every part but
not the whole (`tools/bin/diag <session>` after this) says that
two parts disagree about a name, which is what the message
"overload resolution" of HOL Light comes to.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import hterm, thmcheck

ML = T + '../ml/'


def parts(stmt):
  """the statement, its conjuncts and the sides of an implication"""
  out = [stmt]
  try:
    e = hterm.Parser(hterm.tokenize(stmt), hterm.Ctx()).parse()
  except Exception:
    return out

  def go(n, depth):
    while n.kind == 'paren': n = n.e
    if n.kind == 'quant':
      go(n.body, depth); return
    if n.kind == 'infix' and n.op in ('/\\', '==>', '<=>'):
      go(n.l, depth + 1); go(n.r, depth + 1); return
    if depth:
      out.append(hterm.Printer(hterm.Ctx()).pr(n, 0))

  go(e, 0)
  return out


def main():
  if not sys.argv[1:]:
    print(__doc__); return
  want = []
  if sys.argv[1] == '--unstated':
    names = set()
    for l in open(T + '../tmp/unstated.txt'):
      if '\t' in l: names.add(l.split('\t')[0])
    for dp, _, fs in os.walk(ML):
      for f in sorted(fs):
        if not f.endswith('.ml'): continue
        p = os.path.join(dp, f)
        for nm, line, stmt in thmcheck.statements(p):
          if re.sub(r'\[.*', '', nm) in names:
            want.append((os.path.relpath(p, ML), nm, stmt))
  else:
    p = ML + sys.argv[1]
    keep = set(sys.argv[2:])
    for nm, line, stmt in thmcheck.statements(p):
      if not keep or re.sub(r'\[.*', '', nm) in keep:
        want.append((sys.argv[1], nm, stmt))
  n = 0
  with open(T + '../tmp/stmts.txt', 'w') as o:
    for f, nm, stmt in want:
      hid = thmcheck.hidden(ML + f)
      if hid:
        o.write('@@@HIDE\t%s\n' % ' '.join(hid))
      for i, part in enumerate(parts(stmt)):
        o.write('@@@\t%s\t%d\t%s%s\n%s\n'
                % (f, i, nm, '' if i == 0 else '/part%d' % i, part))
        n += 1
  print('%d parts of %d statements in tmp/stmts.txt'
        % (n, len(want)))


if __name__ == '__main__':
  main()
