import os, re, sys, json
root = '/home/freek/claude/hol-light/cakeml/cakeml-src'
files = []
for dp, dn, fn in os.walk(root):
  if '/.git' in dp: continue
  for f in fn:
    if f.endswith('Script.sml'): files.append(os.path.join(dp,f))
thy2file = {}
deps = {}
for path in files:
  src = open(path, encoding='utf-8', errors='replace').read()
  m = re.search(r'^Theory\s+(\S+)', src, re.M)
  if m: thy = m.group(1)
  else:
    thy = os.path.basename(path)[:-10]
  thy2file[thy] = path
  anc = []
  m = re.search(r'^Ancestors\b(.*?)(^\S|\Z)', src, re.M|re.S)
  if m:
    body = m.group(1)
    body = re.sub(r'\[[^\]]*\]', '', body)
    anc += body.split()
  # old style opens
  for mm in re.finditer(r'^\s*(?:val _ = )?open\s+([^;]*);', src, re.M):
    for w in mm.group(1).split():
      if w.endswith('Theory'): anc.append(w[:-6])
  deps[thy] = sorted(set(anc))
json.dump({'thy2file': thy2file, 'deps': deps}, open('/home/freek/claude/hol-light/cakeml/tools/deps.json','w'), indent=1)
print(len(thy2file), 'theories')
