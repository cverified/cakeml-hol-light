"""check the measures that the port writes against HOL4's

     python3 -I tools/measures.py

   For every cake_define_wf of the port it finds the WF_REL_TAC of
   the HOL4 source of the same theory and compares the names in
   them: a name `foo_size` of HOL4 has to become a size function
   of the port whose type belongs to the theory itself or to one
   that the measure names.  It prints the ones where the theory
   that the port chose is not the one of the file (the measure of
   bvlSem's evaluate said flatLang_exp_size where HOL4 means
   bvl's exp_size).  A prefix that is a theory the file loads is
   the port's own qualification and says nothing, so what is left
   is short: of the four that it prints, bvlSem's evaluate and
   closProps' contains_App_SOME were wrong and the two others
   (word_depth, stackProps) are right."""
import os, re, sys

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = C + '/cakeml-src'

# the HOL4 file of every theory
hol4 = {}
for dp, dn, fn in os.walk(SRC):
  for f in fn:
    if f.endswith('Script.sml'):
      hol4[f[:-len('Script.sml')]] = os.path.join(dp, f)

def needs_of(path):
  """the theories that a file of the port loads"""
  return set(re.findall(r'^needs "(?:.*/)?(\w+)\.ml";;', open(path).read(),
                        re.M))


def measures_of(path):
  """the (name, measure) of every definition of a port file"""
  src = open(path).read()
  out = []
  for m in re.finditer(r'^let (\w+) = cake_define(?:_list)?_wf\n'
                       r'\s*`([^`]*)`', src, re.M):
    out.append((m.group(1), ' '.join(m.group(2).split())))
  return out

def hol4_measures(thy):
  p = hol4.get(thy)
  if not p: return {}
  src = open(p, errors='replace').read()
  out = {}
  for m in re.finditer(r'^Definition (\w+)(?:\[[^\]]*\])?:(.*?)^End',
                       src, re.M | re.S):
    body = m.group(2)
    k = re.search(r'^Termination', body, re.M)
    if not k: continue
    t = re.search(r'(?:WF_REL_TAC|wf_rel_tac)\s*[`\u2018]+([^`\u2019]*)',
                  body[k.end():])
    if t: out[m.group(1)] = ' '.join(t.group(1).split())
  return out

bad = 0
for dp, dn, fn in os.walk(C + '/ml'):
  for f in sorted(fn):
    if not f.endswith('.ml'): continue
    thy = f[:-3]
    ms = measures_of(os.path.join(dp, f))
    if not ms: continue
    ns = needs_of(os.path.join(dp, f)) | set([thy])
    h4 = hol4_measures(thy)
    for name, mes in ms:
      src = h4.get(name) or h4.get(name.replace('_def', '')) or \
            h4.get(name + '_def')
      if src is None: continue
      # the size functions that each of them names
      a = set(re.findall(r"([A-Za-z0-9_']+)_size\b", mes))
      b = set(re.findall(r"([A-Za-z0-9_']+)_size\b", src))
      for nm in sorted(a):
        if nm in b or nm in ('list', 'pair', 'option', 'num'): continue
        # the port qualified the name: the theory it chose
        q = nm.rsplit('_', 1)[0] if '_' in nm else nm
        if any(x.startswith(q) or q.startswith(x) for x in b): continue
        if thy.startswith(q) or q.startswith(thy[:4]): continue
        # a prefix that is a theory the file loads is the port's
        # own qualification and says nothing
        if q in ns: continue
        print('%-44s %s' % (f + ':' + name, mes))
        print('%-44s HOL4: %s' % ('', src))
        bad += 1
        break
print('%d measures to look at' % bad)
