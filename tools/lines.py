"""the lines of the port that are too long

  python3 -I tools/lines.py

A line of the port is at most 72 characters -- except inside a
comment that a HOL4 source has, which the port keeps unaltered
(`CLAUDE.md`), whatever the length of its lines.  So the lines
over 72 characters outside a comment are the ones to put right,
and the ones inside a comment are counted and are the sources'.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nohol4

ML = (sys.argv[1] if sys.argv[1:] else
      os.path.dirname(os.path.abspath(__file__)) + "/../ml/")


def files():
  """the files to check: the one named, or every file under the
     directory named (ml/ by default)"""
  if os.path.isfile(ML): return [(ML, ML)]
  out = []
  for root, _, fs in os.walk(ML):
    for f in sorted(fs):
      if f.endswith('.ml'):
        p = os.path.join(root, f)
        out.append((p, os.path.relpath(p, ML)))
  return sorted(out)


def main():
  bad = incomment = 0
  if True:
    for p, rel in files():
      text = open(p).read()
      bare = nohol4.code_free(text).split('\n')
      for i, l in enumerate(text.split('\n')):
        if len(l) <= 72: continue
        # a comment of a source inside a term or a datatype
        # specification, which the port writes as the comment of
        # HOL Light (// and to the end of the line) and keeps
        # unaltered, whatever the length of its lines
        if re.match(r'\s*`?//', l):
          incomment += 1; continue
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
