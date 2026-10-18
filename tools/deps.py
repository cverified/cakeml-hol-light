import os, re, sys, json
root = '/home/freek/claude/hol-light/cakeml/cakeml-src'
files = []
for dp, dn, fn in os.walk(root):
  if '/.git' in dp: continue
  for f in fn:
    if f.endswith('Script.sml'): files.append(os.path.join(dp,f))
thy2file = {}
deps = {}
nogram = {}
for path in files:
  src = open(path, encoding='utf-8', errors='replace').read()
  m = re.search(r'^Theory\s+(\S+)', src, re.M)
  if m: thy = m.group(1)
  else:
    thy = os.path.basename(path)[:-10]
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
json.dump({'thy2file': thy2file, 'deps': deps, 'nogram': nogram},
          open('/home/freek/claude/hol-light/cakeml/tools/deps.json',
               'w'), indent=1)
print(len(thy2file), 'theories')
