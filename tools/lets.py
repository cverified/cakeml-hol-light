"""check that no let of the port binds a function without making
   an abstraction of its arguments

  python3 -I tools/lets.py

HOL Light takes the left hand side of a let binding for a pattern
and leaves the arguments of a function free, where HOL4 binds
them: "let f x = e in b" has to be "let f = (\\x. e) in b".  This
reads the quotations of ml/ and reports a binding that is not.
"""
import re, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nohol4

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BAD = re.compile(r"\blet\s+[A-Za-z_][A-Za-z0-9_']*"
                 r"(?:\s+[A-Za-z_][A-Za-z0-9_']*)+\s*=")
n = 0
for root, dirs, files in os.walk(C + '/ml'):
  for f in sorted(files):
    if not f.endswith('.ml'): continue
    p = os.path.join(root, f)
    # the comments go first: a backquote in the prose of one (the
    # port writes HOL Light's `bit i w` in a comment of
    # ml/lib/tactics.ml, and a source quotes with `find') would
    # pair with the quotation after it and make the code between
    # them a term
    src = nohol4.code_free(open(p).read())
    for m in re.finditer(r'`([^`]*)`', src, re.S):
      line = src[:m.start()].count('\n') + 1
      for mm in BAD.finditer(m.group(1)):
        n += 1
        print('%s:%d: %s' % (os.path.relpath(p, C), line,
                             mm.group(0)))
print(n, 'lets that bind a function without an abstraction')
