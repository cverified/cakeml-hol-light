"""classify the definitions that the first pass assumes
   (ml/CHEATS.md) by their shape, so that a strategy can be aimed
   at a class of them:

     python3 -I tools/shapes.py            the counts per shape
     python3 -I tools/shapes.py <shape>    the definitions of one
                                           shape (with their text)

   The shapes are
     plain      a recursion that HOL Light should be able to make
     lambda     a recursive call under a lambda (the bind of a
                monad, which HOL4 handles with a congruence)
     nonrec     no recursive call at all (so the definition fails
                on something else: a constant that the port does
                not have, or the form of the clauses)
     mutual     more than one function in the block
     reconstr   a recursive call on a term that the clause builds
                (not a subterm of an argument)
"""
import sys, os, re

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def blocks(f):
  """the text of every definition of a file of the port, by the
     constant that it defines (which is not the name of the OCaml
     binding: that one is the name that HOL4 gives the theorem)"""
  src = open(C + '/ml/' + f).read()
  out = {}
  for m in re.finditer(r'^let .*?;;$', src, re.M | re.S):
    t = m.group(0)
    # a block defines the function of every clause of it (the
    # _sing and the _list of a pair are one block)
    for h in re.findall(r'`\(?([A-Za-z0-9_\']+)', t):
      out.setdefault(h, t)
  return out


def cheats():
  """the name, the file and the reason of every assumed
     definition, with the text that the port has for it"""
  out = []
  seen = {}
  for l in open(C + '/ml/CHEATS.md'):
    m = re.match(r'\| `([^`]*)` \| `([^`]*)` \| (.*?) *\|', l)
    if not m: continue
    name, f, why = m.groups()
    if not f: continue
    if f not in seen: seen[f] = blocks(f)
    out.append((name, f, why, seen[f].get(name)))
  return out


def heads(text):
  """the functions that the block defines: the first word of
     every clause of it"""
  return set(re.findall(r'`\(?([A-Za-z0-9_\']+)', text))


def shape(name, text):
  if text is None: return 'nofind'
  # the right hand sides are what follows the first = of a clause
  rhs = ''.join(re.split(r'\n', text)[0:])
  uses = len(re.findall(r'\b%s\b' % re.escape(name), text))
  if uses <= 1: return 'nonrec'
  for m in re.finditer(r'\(\\', text):
    if re.search(r'\b%s\b' % re.escape(name), text[m.end():]):
      return 'lambda'
  hs = heads(text) - {name}
  if any(h.startswith(name) or name.startswith(h) for h in hs):
    return 'mutual'
  # a recursive call whose argument is an application of a
  # constructor or of a function (not a variable)
  for m in re.finditer(r'\b%s\b\s+([A-Za-z0-9_\']+|\()'
                       % re.escape(name), text):
    if m.group(1) == '(': return 'reconstr'
  return 'plain'


if __name__ == '__main__':
  want = sys.argv[1] if len(sys.argv) > 1 else None
  import collections
  n = collections.Counter()
  nw = collections.Counter()
  for name, f, why, text in cheats():
    s = shape(name, text)
    n[s] += 1
    nw[(s, why)] += 1
    if want and s == want:
      print('=== %s (%s) %s' % (name, f, why))
      print(text)
  if not want:
    for s, k in n.most_common():
      print('%-10s %4d  %s' % (s, k, ', '.join(
        '%s %d' % (w or '?', v) for (s2, w), v in
        sorted(nw.items(), key=lambda x: -x[1]) if s2 == s)[:58]))
    print('%-10s %4d' % ('total', sum(n.values())))
