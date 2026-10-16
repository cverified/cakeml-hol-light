"""write a test that parses every definition of the port that the
   first pass assumes (ml/CHEATS.md) and prints the free variables
   of it: those are the constants that the port does not have, and
   the reason why cake_define could not make the definition.

     python3 -I tools/freevars.py <out>
   and then load <out> in a session that has the whole port.
"""
import sys, os, re

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
out = sys.argv[1]

cheats = []
for l in open(C + '/ml/CHEATS.md'):
  m = re.match(r'\| `([^`]+)` \| `([^`]*)` \|', l)
  if m and m.group(2): cheats.append((m.group(1), m.group(2)))

tests = ["""(* the free variables of a clause that its own
   arguments do not bind: those are the constants that the port
   does not have *)
let cake_free tm =
  let l,r = dest_eq(snd(strip_forall tm)) in
  let _,args = strip_comb l in
  let bound = itlist (fun a s -> union (frees a) s) args [] in
  filter (fun v -> not (mem v bound) &&
                   not (can get_const_type (fst(dest_var v))))
         (frees r);;
let cake_show nm tm =
  let vs = try cake_free tm with Failure _ -> [] in
  if vs <> [] then
    print_string (nm ^ ": " ^
      end_itlist (fun a b -> a ^ " " ^ b)
                 (map (fst o dest_var) vs) ^ "\\n");;"""]
n = 0
for nm, f in cheats:
  try:
    text = open(C + '/ml/' + f).read()
  except Exception:
    continue
  ph = [p for p in re.split(r'(?<=;;)\n', text)
        if re.search(r'`\s*\(?\s*%s\b' % re.escape(nm), p)]
  if not ph: continue
  q = re.sub(r'\(\*.*?\*\)', '', ph[0], flags=re.S)
  qs = [x for x in re.findall(r'`([^`]*)`', q, re.S) if x.strip()]
  if 'cake_define_wf' in q or 'cake_define_list_wf' in q:
    qs = qs[1:]
  for x in qs:
    tests.append('(try cake_show "%s" `%s`\n'
                 ' with Failure _ -> ());;' % (nm, x))
  n += 1
open(out, 'w').write('\n'.join(tests) + '\n')
print(n, 'definitions')
