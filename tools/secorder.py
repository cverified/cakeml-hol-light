"""the helpers of a section, each against the first line that names
   it.

     python3 -I tools/secorder.py <file of the port> ...

   A proof of phase three stands in the file as one expression,
   whose helpers are `let ... in` of it.  A helper that is named
   before its own `let` is an "Unbound value" when the file loads
   -- and the session the proof was written in cannot say so,
   because a scratch round of an earlier day left the name at its
   top level (PORTING-GUIDE.md entry 112).  tools/scope.py is the
   same check between the sections of a file; this one is inside
   one.

   It is for the generated files of ml/, where a section is one
   expression and every `  let` of it is a helper of that
   expression.  The hand written files of ml/lib have scopes of
   their own (a `let` inside a function, a name in the string of
   a failwith), so it reports those as well.
"""
import re, sys


def strip_comments(lines):
  """the lines with the comments and the quotations taken out, so
     that a name in prose is not a use of it"""
  depth, inq, out = 0, False, []
  for l in lines:
    o, i = '', 0
    while i < len(l):
      if not inq and l[i:i + 2] == '(*':
        depth += 1; i += 2; continue
      if not inq and l[i:i + 2] == '*)' and depth:
        depth -= 1; i += 2; continue
      if depth == 0 and l[i] == '`':
        inq = not inq; i += 1; continue
      if depth == 0 and not inq: o += l[i]
      i += 1
    out.append(o)
  return out


def sections(lines):
  """the top level blocks of the file, as (name, first line, lines)"""
  out, start, name = [], None, None
  for i, l in enumerate(lines):
    if re.match(r'let [a-zA-Z_]', l):
      if start is not None: out.append((name, start, lines[start:i]))
      m = re.match(r'let ([A-Za-z_][A-Za-z0-9_\']*)', l)
      name, start = m.group(1), i
  if start is not None: out.append((name, start, lines[start:]))
  return out


def main(argv):
  if len(argv) < 2:
    sys.exit('usage: secorder.py <file> ...')
  bad = 0
  for path in argv[1:]:
    lines = open(path).read().split('\n')
    for name, at, body in sections(lines):
      cl = strip_comments(body)
      defs = {}
      for i, l in enumerate(cl):
        m = re.match(r'  let (?:rec )?([a-zA-Z_][A-Za-z0-9_\']*) ', l)
        if m: defs.setdefault(m.group(1), i)
        # a let that binds a tuple binds each of its names, and a
        # later let of one of them is a shadowing and no use
        m = re.match(r'  let \(?([a-zA-Z_][A-Za-z0-9_\']*)\s*,'
                     r'\s*([a-zA-Z_][A-Za-z0-9_\']*)', l)
        if m:
          defs.setdefault(m.group(1), i); defs.setdefault(m.group(2), i)
      # a name of one or two letters is a variable of a step and
      # not a helper of the section, and the same name in another
      # scope says nothing
      for nm, di in sorted(defs.items(), key=lambda t: t[1]):
        if len(nm) < 3: continue
        pat = re.compile(r'\b%s\b' % re.escape(nm))
        for i in range(di):
          if pat.search(cl[i]):
            print('%s:%d: %s of %s is named before its let at %d'
                  % (path, at + i + 1, nm, name, at + di + 1))
            bad += 1
            break
  print('%d helper(s) named before their let' % bad)


main(sys.argv)
