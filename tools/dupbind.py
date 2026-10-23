"""the statements that bind one name twice in one quantifier chain

  python3 -I tools/dupbind.py [<file of ml/>...]

The port renames a variable whose name is a constant of the port
(`stack` to `stack'`), and where a source binds both `stack` and
`stack'` in one chain the two became one name, the second
shadowing the first (see ISSUES.md, "A statement whose two
variables became one name").  This reads the quoted terms of the
files of `ml/` and reports every `!` or `?` chain with a repeated
name, which is what that looks like.
"""
import sys, os, re

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

def chains(term):
  """the lists of names that the quantifiers of a term bind"""
  out, i, n = [], 0, len(term)
  while i < n:
    c = term[i]
    if c not in '!?':
      i += 1
      continue
    i += 1
    if i < n and term[i] == '!':        # ?! binds one name
      i += 1
    ns, ok = [], True
    while i < n:
      while i < n and term[i] in ' \n\t':
        i += 1
      if i >= n:
        ok = False
        break
      if term[i] == '.':
        i += 1
        break
      if term[i] == '(':               # (name:type)
        j = term.find(')', i)
        if j < 0:
          ok = False
          break
        m = IDENT.match(term[i+1:j].strip())
        if not m:
          ok = False
          break
        ns.append(m.group(0))
        i = j + 1
        continue
      m = IDENT.match(term, i)
      if not m:
        ok = False
        break
      ns.append(m.group(0))
      i = m.end()
    if ok and ns:
      out.append(ns)
  return out

def quoted(src):
  out, i = [], src.find('`')
  while i >= 0:
    j = src.find('`', i + 1)
    if j < 0:
      break
    out.append(src[i+1:j])
    i = src.find('`', j + 1)
  return out

def files(args):
  if args:
    return args
  out = []
  for d, _, fs in os.walk('ml'):
    out += [os.path.join(d, f) for f in fs if f.endswith('.ml')]
  return sorted(out)

n = 0
for p in files(sys.argv[1:]):
  for term in quoted(open(p).read()):
    for ns in chains(term):
      dups = sorted({x for x in ns if ns.count(x) > 1})
      if dups:
        n += 1
        print('%s: %s in `%s`' % (p, ','.join(dups), ' '.join(ns)))
print('%d chain(s) that bind one name twice' % n)
