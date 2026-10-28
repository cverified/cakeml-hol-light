# landproof.py <try file> <statement> [<comment file>] : put the
# tactic of a proof attempt into the section of the proof store.
#
# A round of the loop writes its attempts into tmp/tryNNN.ml as
#
#   let <statement> = btry "<statement>" `...` (fun () -> <tactic>);;
#
# and what the store wants is the <tactic> alone, indented by two,
# in the section `### <statement>` of proofs/<...>/<theory>.prf.
# Doing that by hand is where a round loses its time (and a stray
# `;;` costs a twelve-minute verify, see PORTING-GUIDE.md).
#
# With a comment file the text of it goes above the tactic, as the
# comment of the section; without one the comment the section has
# is kept.
import os, re, sys

def section_of(path, name):
  s = open(path).read()
  m = re.search(r'(?m)^### %s$' % re.escape(name), s)
  if not m:
    return None
  start = m.start()
  n = re.search(r'(?m)^### ', s[m.end():])
  end = m.end() + n.start() if n else len(s)
  return s, start, end

def tactic_of(path, name):
  s = open(path).read()
  m = re.search(r'(?m)^let %s = btry\b' % re.escape(name), s)
  if not m:
    sys.exit('landproof: %s is not an attempt of %s' % (name, path))
  i = s.index('(fun () ->', m.start()) + len('(fun () ->')
  # the attempt ends at the first `);;` at the start of a line's
  # text, which is where btry's own paren closes
  j = s.index(');;', i)
  body = s[i:j]
  out = []
  for l in body.split('\n'):
    out.append('  ' + l[3:] if l.startswith('   ') else l)
  return '\n'.join(out).strip()

def main(argv):
  if len(argv) < 3:
    sys.exit('usage: landproof.py <try file> <statement> '
             '[<comment file>]')
  tryfile, name = argv[1], argv[2]
  comment = open(argv[3]).read().rstrip() if len(argv) > 3 else None
  tac = tactic_of(tryfile, name)
  hits = []
  for root, _, files in os.walk('proofs'):
    for f in files:
      if f.endswith('.prf'):
        p = os.path.join(root, f)
        r = section_of(p, name)
        if r:
          hits.append((p, r))
  if len(hits) != 1:
    sys.exit('landproof: %d section(s) named %s' % (len(hits), name))
  path, (s, start, end) = hits[0]
  old = s[start:end]
  if comment is None:
    # keep the comment the section has: what stands between the
    # header and the tactic, where it is a comment
    body = old.split('\n', 1)[1]
    m = re.match(r'(\s*\(\*.*?\*\)\n)', body, re.S)
    comment = m.group(1).rstrip() if m else ''
  new = '### %s\n%s%s  (%s)\n' % (
    name, comment, '\n' if comment else '', tac)
  open(path, 'w').write(s[:start] + new + s[end:])
  print('%s: section %s, %d lines of tactic' %
        (path, name, tac.count('\n') + 1))

main(sys.argv)
