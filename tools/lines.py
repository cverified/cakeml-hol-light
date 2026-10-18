"""the lines of the port that are too long

  python3 -I tools/lines.py

A line of the port is at most 72 characters -- except inside a
comment that a HOL4 source has, which the port keeps unaltered
(`CLAUDE.md`), whatever the length of its lines.  So the lines
over 72 characters outside a comment are the ones to put right,
and the ones inside a comment are counted and are the sources'.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nohol4

ML = os.path.dirname(os.path.abspath(__file__)) + '/../ml/'


def main():
  bad = incomment = 0
  for root, _, fs in os.walk(ML):
    for f in sorted(fs):
      if not f.endswith('.ml'): continue
      p = os.path.join(root, f)
      rel = os.path.relpath(p, ML)
      text = open(p).read()
      bare = nohol4.code_free(text).split('\n')
      for i, l in enumerate(text.split('\n')):
        if len(l) <= 72: continue
        if bare[i].strip():
          bad += 1
          if bad <= 5:
            print('%s:%d: %d characters' % (rel, i + 1, len(l)))
        else:
          incomment += 1
  print('%d lines over 72 characters outside a comment, %d inside '
        'one (the sources’)' % (bad, incomment))
  return bad


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
