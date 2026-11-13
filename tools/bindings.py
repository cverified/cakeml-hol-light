"""names that a file of the port binds twice

     python3 -I tools/bindings.py [file...]

   A file that binds one name twice says two things with one
   name, and the second is what the rest of the port sees: the
   first is gone without a word.  That happens where a theorem of
   the source is called foo_ind and a definition of the same file
   gives its induction theorem that name as well, and where the
   port adds a lemma of its own under a name the source uses.

   With no arguments it reads every .ml file of ml/.
"""
import os, re, sys

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'

# the names a phrase binds: let a,b = ... and let a = ...  A
# phrase with an argument (let f x = ...) is a function of the
# port's own and not a theorem, and is not one of these.
BIND = re.compile(r"^let\s+([A-Za-z_][A-Za-z0-9_']*"
                  r"(?:\s*,\s*[A-Za-z_][A-Za-z0-9_']*)*)\s*=", re.M)

# the files that are the port's machinery and not a theory of
# CakeML: those bind a name again on purpose, to put a wrapper
# round what it was
MACHINERY = {'lib/define.ml', 'lib/definition.ml',
             'lib/induction.ml', 'lib/fast.ml', 'lib/preamble.ml',
             'lib/hol4.ml', 'lib/lemmas.ml'}


def names_of(text):
  out = []
  for m in BIND.finditer(text):
    for n in m.group(1).split(','):
      n = n.strip()
      if n and n != '_': out.append((n, text.count('\n', 0, m.start()) + 1))
  return out


def files():
  for root, dirs, fs in os.walk(ML):
    dirs.sort()
    for f in sorted(fs):
      if f.endswith('.ml'): yield os.path.join(root, f)


def main(argv):
  bad = 0
  for p in (argv or files()):
    rel = os.path.relpath(p, ML)
    if rel in MACHINERY: continue
    seen = {}
    for n, line in names_of(open(p).read()):
      if n in seen:
        bad += 1
        print('%s:%d: %s is bound again (first at %d)'
              % (rel, line, n, seen[n]))
      else:
        seen[n] = line
  print('%d names bound twice' % bad)
  return 1 if bad else 0


if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
