"""a name that a proof uses before the file defines it

  python3 -I tools/scope.py <file of the port>...

Every file of ml/ is loaded from the top, so a proof may only name
what stands **before** it: a `let` of the same file further down is
not in scope, and neither is a lemma of the shared block that the
generator emits lower.  A session cannot say so -- it has the whole
file loaded -- and only a run or a `verifyquick` finds it, twelve
minutes later.  This is the check that finds it in a second.

It reports, for every top level `let` of the file, the identifiers
of its body that the same file defines later.
"""
import re, sys

LET = re.compile(r"^let\s+(?:rec\s+)?([A-Za-z_][A-Za-z0-9_']*)")
LOCAL = re.compile(r"\blet\s+(?:rec\s+)?([A-Za-z_][A-Za-z0-9_']*)")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

def noquote(s):
  """the text without its HOL quotations, which are terms and not
     OCaml: a constant of a statement is not a binding"""
  out = []
  q = False
  for c in s:
    if c == '`':
      q = not q
    elif not q:
      out.append(c)
  return ''.join(out)

def nocomment(s):
  """the text without its comments, which name what a proof does
     not use (the source's own theorem that stands later, say)"""
  out = []
  depth = 0
  i = 0
  while i < len(s):
    if s.startswith('(*', i):
      depth += 1; i += 2
    elif s.startswith('*)', i) and depth > 0:
      depth -= 1; i += 2
    else:
      if depth == 0: out.append(s[i])
      i += 1
  return ''.join(out)

def spans(lines):
  """the top level lets of the file, as (name, first line, last line)"""
  out = []
  for i, l in enumerate(lines):
    m = LET.match(l)
    if m:
      out.append([m.group(1), i, len(lines) - 1])
  for k in range(len(out) - 1):
    out[k][2] = out[k + 1][1] - 1
  return [tuple(x) for x in out]

def check(path):
  lines = open(path).read().split('\n')
  sp = spans(lines)
  at = {}
  for name, i, _ in sp:
    at.setdefault(name, i)
  bad = []
  for name, i, j in sp:
    body = noquote(nocomment('\n'.join(lines[i:j + 1])))
    # the names that the body gives itself are its own
    own = set(LOCAL.findall(body))
    for id in set(IDENT.findall(body)):
      if id == name or id in own:
        continue
      k = at.get(id)
      if k is not None and k > i:
        bad.append((i + 1, name, id, k + 1))
  return bad

def paths():
  """the files to check: the ones named, or every file of ml/"""
  if sys.argv[1:]: return sys.argv[1:]
  import os
  ml = os.path.dirname(os.path.abspath(__file__)) + "/../ml/"
  out = []
  for root, _, fs in os.walk(ml):
    for f in sorted(fs):
      if f.endswith('.ml'): out.append(os.path.join(root, f))
  return sorted(out)


n = 0
for path in paths():
  for ln, name, id, k in sorted(check(path)):
    print('%s:%d: %s uses %s, which the file defines at %d'
          % (path, ln, name, id, k))
    n += 1
print('%d name(s) used before the file defines them' % n)

# Note: the span of a `let` reaches to the next one, so a line
# between two definitions (a `cake_cheat_budget :=`, say) counts as
# part of the first; and a name that a proof uses *is* reported when
# the file binds it later, whatever it is bound to.  Three hits of
# the whole port are of that kind (bvi_let, bvl_handle, bvl_inline:
# the OCaml name of a theorem about a definition, which the
# definition's own block mentions in its termination); the proof
# files of ml/compiler/backend/proofs are clean.
