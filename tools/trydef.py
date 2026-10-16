"""write a test that makes the definitions named on the command
   line again, with the constants renamed, so that a session that
   has the whole port loaded (hol-seq, after a run) can try a
   change to the strategies of ml/lib/define.ml on a definition
   that the first pass assumes.

     python3 -I tools/trydef.py <out> <name>...

   A name is the one of a definition of ml/CHEATS.md, or
   <file>:<constant> for one that is not assumed.
"""
import re, sys, os

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
out = sys.argv[1]
names = sys.argv[2:]

# where every assumed definition is
where = {}
for l in open(C + '/ml/CHEATS.md'):
  m = re.match(r'\| `([^`]*)` \| `([^`]*)` \|', l)
  if m and m.group(2): where[m.group(1)] = m.group(2)


def block(f, name):
  """the phrase of the port that defines a constant"""
  src = open(C + '/ml/' + f).read()
  for m in re.finditer(r'^let .*?;;$', src, re.M | re.S):
    t = m.group(0)
    if name in re.findall(r"`\(?([A-Za-z0-9_']+)", t): return t
  return None


def heads(qs):
  """the functions that the quotations define: the first word of
     every clause (of the conclusion of a rule of an inductive)"""
  hs = set()
  for q in qs:
    for cl in re.split(r'/\\\s*\n', q):
      cl = cl.strip().lstrip('(').lstrip()
      cl = re.sub(r'^!\s*[^.]*\.\s*', '', cl)
      cl = cl.split('==>')[-1].strip().lstrip('(').lstrip()
      m = re.match(r"([A-Za-z_][A-Za-z0-9_']*)", cl)
      if m: hs.add(m.group(1))
  return hs


tests = ["""(* the definitions of the port, with the constants
   renamed, so that this session can make them again *)
let cake_try name f =
  let n0 = length(cake_cheats()) in
  let t0 = Sys.time() in
  let r = try (let _ = f () in "made")
          with Failure e -> "FAILED " ^ e in
  let t = Sys.time() -. t0 in
  let w = if length(cake_cheats()) > n0
          then snd(hd(rev(cake_cheat_why()))) else "-" in
  print_string (Printf.sprintf "TRYDEF %-28s %-10s %6.2fs %s\\n"
                  name r t w);
  flush stdout;;"""]

for nm in names:
  if ':' in nm:
    f, name = nm.rsplit(':', 1)
  else:
    name, f = nm, where.get(nm)
  if not f:
    print('not an assumed definition:', nm); continue
  t = block(f, name)
  if t is None:
    print('cannot find:', nm); continue
  # the comments may hold HOL4 ML code with quotations of its own
  t = re.sub(r'\(\*.*?\*\)', '', t, flags=re.S)
  qs = [x for x in re.findall(r'`([^`]*)`', t, re.S) if x.strip()]
  wf = 'cake_define_wf' in t or 'cake_define_list_wf' in t
  rel = qs[0] if wf else None
  if wf: qs = qs[1:]
  hs = heads(qs) - set(['T', 'F', 'let', 'match', 'if'])
  def ren(s):
    for h in sorted(hs):
      s = re.sub(r'\b%s\b' % re.escape(h), h + '_zz', s)
    return s
  qs = [ren(q) for q in qs]
  lst = 'cake_define_list' in t
  if lst and wf:
    call = ('cake_define_list_wf `%s`\n  [`%s`]'
            % (rel, '`;\n   `'.join(qs)))
  elif lst:
    call = 'cake_define_list\n  [`%s`]' % '`;\n   `'.join(qs)
  elif wf:
    call = 'cake_define_wf `%s`\n  `%s`' % (rel, qs[0])
  else:
    call = 'cake_define\n  `%s`' % qs[0]
  tests.append('cake_try "%s" (fun () ->\n  %s);;' % (name, call))

open(out, 'w').write('\n\n'.join(tests) + '\n')
print(len(tests) - 1, 'definitions to try')
