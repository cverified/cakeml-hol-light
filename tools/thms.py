"""the report of the theorems of the port

  python3 -I tools/thms.py [file of the port, relative to ml/]

A theorem of the port is a HOL Light `let foo = prove (`...`, tac)`,
so counting them is a count of the files: how many there are, how
many still have a cheat where HOL4 has a proof, and how many
statements the port cannot state at all (a comment points at the
source instead).
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'


def count(path):
  s = open(path, encoding='utf-8').read()
  thms = cheats = 0
  # a binding too long for its line puts the prove on the next one
  for m in re.finditer(r"^let ([A-Za-z_][A-Za-z_0-9']*) =\n?"
                       r"\s*prove$", s, re.M):
    thms += 1
    j = s.find('\nlet ', m.end())
    body = s[m.end():j if j > 0 else len(s)]
    if 'CHEAT_TAC' in body: cheats += 1
  unstated = len(re.findall(r'cannot state yet', s))
  return thms, cheats, unstated


def main():
  files = sys.argv[1:]
  if not files:
    files = []
    for d, _, fs in os.walk(ML):
      for f in fs:
        if f.endswith('.ml'):
          files.append(os.path.join(d, f)[len(ML):])
  tot = [0, 0, 0]
  rows = []
  for f in sorted(files):
    try: t, c, u = count(ML + f)
    except OSError: continue
    rows.append((t, c, u, f))
    tot = [tot[0] + t, tot[1] + c, tot[2] + u]
  for t, c, u, f in sorted(rows, key=lambda r: -r[1])[:20]:
    if c: print('%6d %6d %6d  %s' % (t, c, u, f))
  print('%6d %6d %6d  all of the port (theorems, cheats,'
        ' not stated)' % tuple(tot))
  return 0


if __name__ == '__main__':
  sys.exit(main())
