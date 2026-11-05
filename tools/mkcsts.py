"""the constants of every theorem of the port, out of a session

  python3 -I tools/mkcsts.py > tmp/csts.ml

writes an ML file that prints, of every theorem that the port
binds, the constants of its statement as the session read it, to
tmp/csts.txt (one line per theorem: the file, the binding and the
constants).  tools/thyscope.py then says which of those constants
come out of a theory that the source of the file cannot see, which
is what a statement reads wrongly when a name that several
theories overload is not pinned by a type (ISSUES.md: the
evaluate of bvlProps).

It is the theorem as the session has it, not a statement read
again: a re-read in a session that has the whole port loaded
resolves an overload with every file's overloads in place, which
is not what the file itself saw.
"""
import os, re, sys
T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import stmts

C = T + '../'
ML = C + 'ml/'

seen = {}
order = []
for dp, dn, fn in os.walk(ML):
  if '/lib' in dp: continue
  for f in sorted(fn):
    if not f.endswith('.ml'): continue
    p = os.path.join(dp, f)
    rel = p[len(ML):]
    text = open(p).read()
    for b, nm, at, ln, _ in stmts.theorems(text) + \
                            [(b, nm, at, ln, None)
                             for b, nm, at, ln, _ in stmts.aliases(text)]:
      seen.setdefault(b, []).append(rel)
      order.append((rel, b))

dup = set(b for b, fs in seen.items() if len(set(fs)) > 1)
out = ['let cstout = open_out "%stmp/csts.txt";;' % C,
       'let csts_dump f b th =',
       '  output_string cstout (f ^ "\\t" ^ b ^ "\\t" ^',
       '    String.concat " " (setify (map (fun t -> fst(dest_const t))',
       '      (find_terms is_const (concl th)))) ^ "\\n");;']
n = 0
for rel, b in order:
  if b in dup: continue
  out.append('csts_dump "%s" "%s" %s;;' % (rel, b, b))
  n += 1
out.append('close_out cstout;;')
out.append('print_string "CSTS DONE\\n";;')
print('\n'.join(out))
sys.stderr.write('%d theorems, %d bindings that more than one file '
                 'has (left out)\n' % (n, len(dup)))
