"""the theories that the source of a file of the port can see

  python3 -I tools/mkscope.py

writes tmp/scopes.txt: the theories that the port has a file of,
and then, of every file, the theories of its scope -- the theory
of its own source and the ones of the Ancestors blocks of that
source, as far as their grammar reaches (an
Ancestors[ignore_grammar] entry does not bring its names).

HOL4 reads a statement with the names of those theories and of no
others.  HOL Light reads one with every overload that every file
of the port has registered, and where nothing pins the type of an
overloaded name it takes the one that the interface happens to
have in front -- which is the one of the theory that registered it
last, so the load order decides what the statement says
(ISSUES.md: the evaluate of bvlProps).  tools/scope.ml reads every
statement with the interface cut down to the scope of its file,
which is what HOL4 does, and says which statements that changes.
"""
import os, sys, json
T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import defsites
C = T + '../'

d = json.load(open(T + 'deps.json'))
deps, nogram = d['deps'], d['nogram']

gram = {}


def scope(thy, path=()):
  """the theories whose names the grammar of this one has"""
  if thy in gram: return gram[thy]
  if thy in path: return set([thy])
  out = set([thy])
  ng = set(nogram.get(thy, []))
  for p in deps.get(thy, []):
    if p not in ng:
      out |= scope(p, path + (thy,))
  gram[thy] = out
  return out


def theories():
  """the theories that the port has a file of, by their name"""
  out = {}
  for dp, dn, fn in os.walk(C + 'ml'):
    if '/lib' in dp: continue
    for f in fn:
      if f.endswith('.ml'):
        out[f[:-3]] = os.path.relpath(os.path.join(dp, f), C + 'ml')
  return out


def constant_theories(thys=None):
  """the theory of every constant of the port: the file of ml/ that
     defines it (tools/defsites.py), which is not what the name of
     the constant says -- backend_common defines
     bvl_to_bvi_namespaces, and a guess by the name would give it
     to bvl_to_bvi and put it out of the scope of every file that
     the source lets name it.

     Only a theory of a CakeML source counts.  A constant of the
     library layer (ml/lib: the sptree, the bags and the strings of
     HOL4 as well as the port's own tactics) is in the scope of
     every file: HOL4 gives it to every source through its
     preamble, and the names of those theories are the ones that
     clash the least."""
  if thys is None: thys = theories()
  out = {}
  for c, (f, _) in defsites.sites().items():
    thy = os.path.basename(f)[:-3]
    if thy in thys: out[c] = thy
  return out


def main():
  thys = theories()
  with open(C + 'tmp/scopes.txt', 'w') as o:
    o.write('@@@THYS\t%s\n' % ' '.join(sorted(thys)))
    n = 0
    for thy in sorted(thys):
      s = scope(thy) & set(thys)
      o.write('@@@SCOPE\t%s\t%s\n' % (thys[thy], ' '.join(sorted(s))))
      n += len(s)
  cthy = constant_theories(thys)
  with open(C + 'tmp/cstthy.txt', 'w') as o:
    for c in sorted(cthy):
      o.write('%s\t%s\n' % (c, cthy[c]))
  print('%d files, %d theories in a scope, %.1f on average'
        % (len(thys), n, n / float(len(thys))))
  print('%d constants of the port, of %d theories, in tmp/cstthy.txt'
        % (len(cthy), len(set(cthy.values()))))


if __name__ == '__main__':
  main()
