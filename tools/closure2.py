"""the theories of the port: the scope of phases one and two

  python3 -I tools/closure2.py          say what would change
  python3 -I tools/closure2.py -w       write tools/closure2.txt

The scope is the dependency closure of two things:

- `compilerProof`, the theory of `compile_correct`, which is what
  the port is for (CLAUDE.md); and
- everything under `compiler/bootstrap/` and `cv_translator/`,
  which is what compiling in the logic needs.

Nothing is cut.  Until 2026-11-15 seven theories were -- basisProg,
panPtreeConversion, pan_to_target, panStatic, pan_passes,
CommandLineProof and ml_translator -- which made the scope of the
port smaller than the theorem it targets: compilerScript.sml names
five of them in its own Ancestors, because `compile` is defined in
a theory that needs the basis program and the whole Pancake
compiler.

A theory that HOL4 builds by *running* a generator (the proof
producing translator, `ml_prog_update`, `cv_compute`) is in the
scope all the same, and is ported block by block like any other:
what is left out is the run, not the file, because those files
also hold definitions and theorems written by hand (cfDiv has 23
definitions and 91 theorems against 6 runs).  The constants a run
would have introduced are declared instead (`cake_declare`), as
`basis` already is in ml/compiler/compiler.ml.  See PENDING.md.
"""
import json, os, collections, re, sys

T = os.path.dirname(os.path.abspath(__file__)) + '/'
R = T + '../cakeml-src/'
d = json.load(open(T + 'deps.json'))
thy2file = d['thy2file']; deps = d['deps']
ROOTS = ['compilerProof']
ROOT_DIRS = ('compiler/bootstrap/', 'cv_translator/')
starts = ROOTS + [t for t, f in thy2file.items()
                  if os.path.relpath(f, R).startswith(ROOT_DIRS)]
seen, ext, st = set(), set(), list(starts)
while st:
  t = st.pop()
  if t in seen: continue
  if t not in thy2file: ext.add(t); continue
  seen.add(t)
  st += deps.get(t, [])
rel = sorted(os.path.relpath(thy2file[t], R) for t in seen)
s = '\n'.join(rel) + '\n'
old = open(T + 'closure2.txt').read() if os.path.exists(
    T + 'closure2.txt') else ''
c = collections.Counter(os.path.dirname(r) for r in rel)
tot = defs = dats = 0
for r in rel:
  x = open(R + r, encoding='utf-8', errors='replace').read()
  tot += x.count('\n')
  defs += len(re.findall(r'^Definition\b', x, re.M))
  defs += len(re.findall(r'^val _ = Define', x, re.M))
  dats += len(re.findall(r'^Datatype\b', x, re.M))
for k, v in sorted(c.items()): print(v, k)
print('files', len(rel), 'lines', tot, 'Definitions', defs,
      'Datatypes', dats)
print('external (HOL4 library) theories:', len(ext))
was = set(l.strip() for l in old.split('\n') if l.strip())
print('%d added, %d dropped' % (len(set(rel) - was), len(was - set(rel))))
if '-w' in sys.argv:
  open(T + 'closure2.txt', 'w').write(s)
  open(T + 'ext2.txt', 'w').write('\n'.join(sorted(ext)) + '\n')
else:
  print('(dry run; -w writes closure2.txt and ext2.txt)')
