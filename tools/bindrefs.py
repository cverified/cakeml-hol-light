"""a proof names a theorem or a definition by its binding

  python3 -I tools/bindrefs.py [--defs] [--dry]

The port binds every theorem and every definition of a source the
way HOL Light does (`let foo = prove (`...`, tac);;`), so a proof
names another one by that binding and not by a lookup under the
HOL4 name (`cake_thm "foo"`, `cake_def "<const>"`).

This rewrites the proof store accordingly, with the bindings that
tools/bin/dryport dumps:

  tmp/dry/emitted.txt   theory, HOL4 name, binding, in the order
                        of the statements of each file
  tmp/dry/thmbind.txt   theory, HOL4 name, binding, of the
                        theorems that each file binds
  tmp/dry/defbind.txt   theory, constant, binding, of the
                        definitions that each file makes

A name is resolved in the file that uses it: the binding is the
one of the last theory at or before that file which binds the
name, which is what the loading order gives it.  Without --defs
only the theorems are rewritten, and with --dry nothing is
written and the changes are counted.
"""
import sys, os, re, glob, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod


def table(path, order):
  """the bindings visible in each theory, from a dump of
     (theory, name, binding) lines"""
  byth = collections.defaultdict(dict)
  for l in open(path):
    thy, nm, b = l.split()
    byth[thy][nm] = b
  out, cur = {}, {}
  for t in order:
    cur = dict(cur)
    cur.update(byth[t])
    out[t] = cur
  return out, byth


def sequence(path):
  """the bindings of the statements of each theory, in order"""
  seq = collections.defaultdict(lambda: collections.defaultdict(list))
  for l in open(path):
    thy, nm, b = l.split()
    seq[thy][nm].append(b)
  return seq


def main():
  defs = '--defs' in sys.argv
  dry = '--dry' in sys.argv
  db = dbmod.Db()
  order = [t for t, _, _ in dbmod.load_order()]
  D = T + '../tmp/dry/'
  for f in ('thmbind.txt', 'emitted.txt', 'defbind.txt'):
    if not os.path.exists(D + f):
      print('no tmp/dry/%s: run tools/bin/dryport first' % f)
      return 1
  thms, _ = table(D + 'thmbind.txt', order)
  dfns, _ = table(D + 'defbind.txt', order)
  seq = sequence(D + 'emitted.txt')
  thy_of = {}
  for t in order:
    try: thy_of[db.mlpath_of(t)] = t
    except Exception: pass
  nthm = ndef = nsec = 0
  bad = []
  for p in sorted(glob.glob(T + '../proofs/**/*.prf', recursive=True)):
    rel = p[p.index('/proofs/') + 8:-4] + '.ml'
    thy = thy_of.get(rel)
    if thy is None:
      bad.append((p, 'no theory of that path'))
      continue
    s = old = open(p).read()

    def thm(m):
      nonlocal nthm
      nm = m.group(1)
      if nm not in thms[thy]:
        bad.append((p, 'unknown theorem ' + nm))
        return m.group(0)
      nthm += 1
      return thms[thy][nm]

    def dfn(m):
      nonlocal ndef
      nm = m.group(1)
      if nm not in dfns[thy]:
        bad.append((p, 'unknown constant ' + nm))
        return m.group(0)
      ndef += 1
      return dfns[thy][nm]

    # the brackets around the lookup stay: they may be the ones of
    # an application (GSYM(CONJUNCT2(cake_def "misc_word_list")))
    # and taking them away joins two names into one
    s = re.sub(r'cake_thm "([^"]+)"', thm, s)
    if defs:
      s = re.sub(r'cake_def "([^"]+)"', dfn, s)
    # a section names the theorem it proves by its binding as well
    out = []
    for l in s.split('\n'):
      if l.startswith('### '):
        nm = l[4:].strip()
        base, _, k = nm.partition('#')
        cands = seq[thy].get(base, [])
        k = int(k) if k else 1
        if len(cands) >= k:
          if cands[k - 1] != nm: nsec += 1
          l = '### ' + cands[k - 1]
        elif base not in [b for bs in seq[thy].values() for b in bs]:
          bad.append((p, 'no statement of ' + nm))
      out.append(l)
    s = '\n'.join(out)
    if s != old and not dry: open(p, 'w').write(s)
  print('%d theorem and %d definition references, %d sections'
        % (nthm, ndef, nsec))
  for p, why in bad:
    print('  %s: %s' % (p.split('/')[-1], why))
  return 1 if bad else 0


if __name__ == '__main__':
  sys.exit(main())
