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
     white space, so that a different layout is not a difference.
     A block of a source is whole lines, so a comment that has code
     after it on its line (the ML of word_bignum has (* Var *) let)
     is cut at the end of the comment itself"""
  text = text.strip()
  if text.startswith('(*'):
    depth = i = 0
    while i < len(text):
      if text.startswith('(*', i): depth += 1; i += 2; continue
      if text.startswith('*)', i):
        depth -= 1; i += 2
        if not depth: text = text[:i]; break
        continue
      i += 1
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
  n = bad = lost = inside = 0
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml' or (want and thy not in want): continue
    p = ML + db.mlpath_of(thy)
    try:
      port = open(p).read()
    except OSError:
      continue
    # the port writes a comment that stands inside a block as the
    # comment of a term of HOL Light (// and to the end of the
    # line), so one of several lines is several of those; the one
    # of a datatype stands in an OCaml string, where a quote and a
    # backslash of it are escaped (lexer_fun's symbol)
    lines = []
    for l in port.split('\n'):
      m = re.match(r'\s*(`?)//(.*)$', l)
      if m:
        l = m.group(1) + re.sub(r'\\(["\\])', r'\1', m.group(2))
      lines.append(l)
    flat = ' '.join('\n'.join(lines).split())
    inport = set()
    for m in re.finditer(r'\(\*.*?\*\)', port, re.S):
      inport.add(body(m.group(0)))
    at = pointers(port)
    for b in hol4.parse(path):
      # a comment inside a block (the constructors of a Datatype,
      # the body of a Definition, a statement) is no Comment block
      # of its own, and the port drops it: HOL Light reads a
      # comment of a quotation after // and to the end of the
      # line, and the clauses of a definition of the port are
      # quotations of their own, between which an OCaml comment
      # stands (PENDING.md says where that stands)
      if b.kind not in ('Comment', 'ML'):
        for m in re.finditer(r'\(\*.*?\*\)', b.body or '', re.S):
          t = ' '.join(m.group(0)[2:-2].split())
          if t and t in flat: continue
          inside += 1
      if b.kind != 'Comment': continue
      n += 1
      s = body(b.text)
      if not s: continue
      if s in inport: continue
      # a comment with an odd number of quotes in it gets one more
      # in the port, which OCaml would otherwise read as the start
      # of a string (compilerScript.sml's (*"*))
      if s + '"' in inport or s + ' "' in inport: continue
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
  print('%d comments inside a block of a source that the port '
        'has not' % inside)


if __name__ == '__main__':
  main()
