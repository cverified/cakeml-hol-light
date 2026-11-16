import os, re, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import overrides
root = '/home/freek/claude/hol-light/cakeml/cakeml-src'
files = []
for dp, dn, fn in os.walk(root):
  if '/.git' in dp: continue
  for f in fn:
    if f.endswith('Script.sml'): files.append(os.path.join(dp,f))
thy2file = {}
cands = {}
deps = {}
nogram = {}
for path in files:
  src = open(path, encoding='utf-8', errors='replace').read()
  # a Theory line may carry an attribute (ag32ProgScript.sml says
  # "Theory ag32Prog[no_sig_docs]"), which is not part of the name:
  # an Ancestors entry of it is the bare name, so a key that kept
  # the attribute made the theory look external to the closure
  m = re.search(r'^Theory\s+([^\s\[]+)', src, re.M)
  if m: thy = m.group(1)
  else:
    thy = os.path.basename(path)[:-10]
  cands.setdefault(thy, []).append(path)
  thy2file[thy] = path
  anc = []
  # a source may have more than one Ancestors block (the second one
  # of clos_to_bvlProof is Ancestors[ignore_grammar], and it is the
  # one that has clos_knownProof in it)
  for m in re.finditer(r'^Ancestors\b(.*?)(?=^\S|\Z)', src, re.M|re.S):
    body = m.group(1)
    body = re.sub(r'\[[^\]]*\]', '', body)
    # a comment in the list is not an ancestor (dataSem has
    # "data_to_word (* TODO: immoral, semantics shouldn't depend
    # on compiler *)", whose words would be theories)
    body = re.sub(r'\(\*.*?\*\)', '', body, flags=re.S)
    anc += body.split()
  # a Libs entry brings the grammar of the theory of that name as
  # well (misc has ASCIInumbersLib in its Libs and uses the
  # num_to_hex_string of ASCIInumbersTheory, which is in no
  # Ancestors block of it)
  for m in re.finditer(r'^Libs\b(.*?)(?=^\S|\Z)', src, re.M|re.S):
    body = re.sub(r'\[[^\]]*\]', '', m.group(1))
    body = re.sub(r'\(\*.*?\*\)', '', body, flags=re.S)
    for w in body.split():
      if w.endswith('Lib'): anc.append(w[:-3])
  # old style opens
  for mm in re.finditer(r'^\s*(?:val _ = )?open\s+([^;]*);', src, re.M):
    for w in mm.group(1).split():
      if w.endswith('Theory'): anc.append(w[:-6])
  deps[thy] = sorted(set(anc))
  # an Ancestors[ignore_grammar] block is an ancestor whose names
  # the parser of the theory does not have: a statement that means
  # one of them writes the theory in front of it, and a bare name
  # of that spelling is a variable of its own
  # (clos_to_bvlProof$do_build_const_thm has a variable parts and
  # clos_constantProof, which has a constant of that name, is one
  # of its ignore_grammar ancestors)
  ng = []
  for m in re.finditer(r'^Ancestors\[([^\]]*)\](.*?)(?=^\S|\Z)',
                       src, re.M | re.S):
    if 'ignore_grammar' not in m.group(1): continue
    body = re.sub(r'\[[^\]]*\]', '', m.group(2))
    body = re.sub(r'\(\*.*?\*\)', '', body, flags=re.S)
    ng += body.split()
  nogram[thy] = sorted(set(ng))
# a theory name that more than one source declares: HOL4 resolves
# it the way Holmake does, which is the source in the directory of
# the theory that needs it.  Where that says nothing,
# overrides.THY_FILE does, and what neither settles is reported --
# os.walk's order is no answer
for thy, cs in sorted(cands.items()):
  if len(cs) < 2: continue
  want = overrides.THY_FILE.get(thy)
  if want:
    hit = [c for c in cs if os.path.relpath(c, root) == want]
    if not hit:
      print('THY_FILE names no source of %s: %s' % (thy, want))
    else:
      thy2file[thy] = hit[0]
      continue
  # a source of a directory that THY_DIR_LAST names is the one
  # not to take while another one is there
  left = [c for c in cs
          if not any(os.path.relpath(c, root).startswith(d)
                     for d in overrides.THY_DIR_LAST)]
  if len(left) == 1:
    thy2file[thy] = left[0]
    continue
  cs = left or cs
  # the directories that hold a theory needing this name: a
  # source of one of them is the one Holmake would resolve to
  users = {os.path.dirname(thy2file[t]) for t, a in deps.items()
           if thy in a}
  own = {c for c in cs if os.path.dirname(c) in users}
  if len(own) == 1:
    thy2file[thy] = own.pop()
  else:
    print('%s is declared by %d sources and nothing says which: %s'
          % (thy, len(cs),
             ' '.join(os.path.relpath(c, root) for c in cs)))

json.dump({'thy2file': thy2file, 'deps': deps, 'nogram': nogram},
          open('/home/freek/claude/hol-light/cakeml/tools/deps.json',
               'w'), indent=1)
print(len(thy2file), 'theories')
