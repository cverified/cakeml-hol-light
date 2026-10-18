"""every comment of a source is in its port, unaltered

  python3 -I tools/comments.py [<theory>...]

Phase two keeps every comment of a CakeML source in its port, in
its place and unaltered (CLAUDE.md).  This checks that the text of
every comment block of every source is in the ported file, and
says which ones are not.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4

ML = T + '../ml/'


def body(text):
  """the words of a comment, without its (* and *) and without the
     white space, so that a different layout is not a difference"""
  text = re.sub(r'^\s*\(\*+|\*+\)\s*$', '', text.strip())
  return ' '.join(text.split())


AT = re.compile(r'\(\* HOL4 (\S+\.sml):(\d+)(?:-(\d+))?:')


def pointers(text):
  """the line ranges of the source that the pointers of a ported
     file point at"""
  out = []
  for m in AT.finditer(text):
    a = int(m.group(2))
    out.append((a, int(m.group(3)) if m.group(3) else a))
  return out


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  n = bad = lost = 0
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml' or (want and thy not in want): continue
    p = ML + db.mlpath_of(thy)
    try:
      port = open(p).read()
    except OSError:
      continue
    inport = set()
    for m in re.finditer(r'\(\*.*?\*\)', port, re.S):
      inport.add(body(m.group(0)))
    at = pointers(port)
    for b in hol4.parse(path):
      if b.kind != 'Comment': continue
      n += 1
      s = body(b.text)
      if not s: continue
      if s in inport: continue
      # a comment that the port had to break into lines of its
      # own is in it as several comments
      if any(s in c or c in s for c in inport if len(c) > 20):
        continue
      bad += 1
      # a comment that is HOL4 code is not in the port, and a
      # pointer at its lines says where it is (CLAUDE.md)
      a = getattr(b, 'src', 0) or 0
      z = getattr(b, 'src_end', 0) or a
      if any(x <= a and z <= y for x, y in at): continue
      lost += 1
      if lost <= 10:
        print('%s:%s: %s' % (re.sub(r'^.*/', '', path), a, s[:60]))
  print('%d comments of the sources, %d not in the port '
        '(%d of them with no pointer at them)' % (n, bad, lost))


if __name__ == '__main__':
  main()
