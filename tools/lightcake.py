"""what LightCake has that the port can take

     python3 -I tools/lightcake.py names [<theory>]
     python3 -I tools/lightcake.py report

LightCake (`lightcake-src/`, see README.md) is the other port of
CakeML to HOL Light: narrow and deep where this one is wide and
shallow.  Its HOL4 library layer is proved -- 3014 theorems of
listTheory, finite_mapTheory, sptreeTheory and the rest -- and of
those theories this port has only the definitions that CakeML
needs.  So they are what it has to give.

Both ports keep HOL4's name for the **binding** of a definition
(`lookup_def`) and for a theorem, and both rename the **constant**
where a name would clash: this port writes `sptree_lookup` where
LightCake writes `lookup`.  So the two vocabularies line up
binding for binding, and the map from its constants to this
port's falls out of the definitions of a file without any table.

`names` prints that map for a theory (or the count for every
theory); `report` says, for every file both ports have, how many
theorems are shared, how many of this port's cheats LightCake
proves, and how many of its proofs use a tactic of its own HOL4
kit rather than HOL Light's.
"""
import os, re, sys, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'
LC = T + '../lightcake-src/'

# a definition block of either port: the binding, then the first
# quotation, whose first name is the constant.  This port writes
# the relation of a define_wf in a quotation of its own, so the
# constant is the first name of the quotation that holds a clause
# -- which is the one that is a list, or the last one.
BIND = re.compile(r"^let ([A-Za-z0-9_']+)(?:,[A-Za-z0-9_']+)? = "
                  r"(cake_def|cake_def_wf|cake_defn|new_definition|"
                  r"define_[a-z_0-9]+|assume_definition[a-z_]*)\b",
                  re.M)
HEAD = re.compile(r"`\s*(?:!\s*[^.]*?\.\s*)?\(*\s*"
                  r"([A-Za-z_][A-Za-z0-9_']*)")


def block_end(s, i):
  """the index past the ;; that ends the block that starts at i,
     counting quotations so that a ;; inside one does not end it"""
  q = False
  while i < len(s) - 1:
    if s[i] == '`': q = not q
    elif not q and s[i] == ';' and s[i + 1] == ';': return i + 2
    i += 1
  return len(s)


def constant_of(body, how):
  """the constant a definition block defines: the first name of
     the quotation that holds the clauses, which is the one in
     brackets where there is one and otherwise the last"""
  qs = []
  i = 0
  while True:
    a = body.find('`', i)
    if a < 0: break
    b = body.find('`', a + 1)
    if b < 0: break
    qs.append((a, body[a:b + 1]))
    i = b + 1
  if not qs: return None
  pick = None
  for a, q in qs:
    if body[:a].rstrip().endswith('['): pick = q; break
  if pick is None: pick = qs[-1][1]
  m = HEAD.search(pick)
  return m.group(1) if m else None


def definitions(path):
  """binding -> constant, for a file of either port"""
  try: s = open(path).read()
  except OSError: return {}
  out = {}
  for m in BIND.finditer(s):
    body = s[m.end():block_end(s, m.end())]
    c = constant_of(body, m.group(2))
    if c: out.setdefault(m.group(1), c)
  return out


def theirs_of(name):
  """where LightCake keeps the file this port calls <name>.ml"""
  for d in ('src/hol4/', 'src/misc/', 'src/semantics/',
            'src/basis/pure/', 'src/compiler/backend/',
            'src/compiler/backend/semantics/',
            'src/compiler/backend/gc/',
            'src/compiler/backend/reg_alloc/',
            'src/compiler/backend/pattern_matching/',
            'src/semantics/proofs/'):
    p = LC + d + name + '.ml'
    if os.path.exists(p): return p
  return None


def ours_of(name):
  for root, _, fs in os.walk(ML):
    if name + '.ml' in fs: return os.path.join(root, name + '.ml')
  return None


def rename_map(name):
  """the map from LightCake's constants to this port's, for the
     theory both call <name>, with the bindings that only one of
     them has"""
  a, b = ours_of(name), theirs_of(name)
  if not a or not b: return None, None, None
  ours, theirs = definitions(a), definitions(b)
  both = {theirs[k]: ours[k] for k in theirs if k in ours}
  only_theirs = sorted(k for k in theirs if k not in ours)
  only_ours = sorted(k for k in ours if k not in theirs)
  return both, only_theirs, only_ours


def names(argv):
  if argv:
    m, ot, oo = rename_map(argv[0])
    if m is None: print('no such pair of files'); return 1
    for k in sorted(m):
      print('  %-28s -> %s' % (k, m[k]))
    print('%d shared bindings; %d only LightCake has, %d only this'
          % (len(m), len(ot), len(oo)))
    if ot: print('  LightCake only:', ot[:14])
    if oo: print('  this port only:', oo[:14])
    return 0
  tot = same = diff = 0
  for root, _, fs in os.walk(LC + 'src'):
    if '/kit' in root: continue
    for f in sorted(fs):
      if not f.endswith('.ml'): continue
      nm = f[:-3]
      if not ours_of(nm): continue
      m, ot, oo = rename_map(nm)
      if m is None: continue
      d = sum(1 for k in m if k != m[k])
      tot += len(m); same += len(m) - d; diff += d
      print('%-24s shared %4d (renamed %3d)  only theirs %3d'
            % (nm, len(m), d, len(ot)))
  print('\n%d shared definitions, %d with the same name, %d renamed'
        % (tot, same, diff))
  return 0


# the tactics of LightCake's own kit, which follow HOL4's proofs
# step by step.  A proof that uses none of them is a HOL Light
# proof and can be taken as it stands.
KIT = ['SIMP', 'FS', 'GVS', 'RW', 'CASES_ON', 'TOP_CASE_TAC',
       'CASE_TAC', 'EVERY_CASE_TAC', 'INDUCT_ON', 'DRULE', 'DXRULE',
       'DRULE_ALL', 'IRULE', 'IMP_RES_TAC', 'PAIRARG_TAC',
       'RVEQ_TAC', 'COND_CASE_EQ', 'all_case_eqs', 'RES_TAC',
       'SPOSE_NOT_THEN', 'cake_ind', 'case_eq', 'cake_add_simps']
KITRE = re.compile(r'\b(%s)\b' % '|'.join(map(re.escape, KIT)))


def theorems(path):
  """name -> the text of its block, for a file of either port"""
  try: s = open(path).read()
  except OSError: return {}
  out = {}
  ms = list(re.finditer(r"^let ([A-Za-z0-9_']+) = prove", s, re.M))
  for i, m in enumerate(ms):
    e = ms[i + 1].start() if i + 1 < len(ms) else len(s)
    out[m.group(1)] = s[m.start():e]
  return out


def report(argv):
  rows = []
  tot = cheat = pure = new = 0
  for root, _, fs in os.walk(LC + 'src'):
    if '/kit' in root: continue
    for f in sorted(fs):
      if not f.endswith('.ml'): continue
      nm = f[:-3]
      a = ours_of(nm)
      if not a: continue
      T_, O = theorems(os.path.join(root, f)), theorems(a)
      if not T_: continue
      shared = [n for n in T_ if n in O]
      ch = [n for n in shared if 'CHEAT_TAC' in O[n]]
      pu = [n for n in ch if not KITRE.search(T_[n])]
      nw = [n for n in T_ if n not in O]
      tot += len(T_); cheat += len(ch); pure += len(pu); new += len(nw)
      rows.append((nm, len(T_), len(shared), len(ch), len(pu), len(nw)))
  print('%-22s %6s %6s %6s %6s %6s'
        % ('', 'theirs', 'shared', 'cheat', 'pure', 'new'))
  for r in rows:
    print('%-22s %6d %6d %6d %6d %6d' % r)
  print('\n%d theorems of LightCake in files this port has:' % tot)
  print('  %d stand where this port cheats, %d of those with no'
        ' tactic of its kit' % (cheat, pure))
  print('  %d are theorems this port does not state at all'
        ' (the library layer)' % new)
  return 0


def lc_bindings():
  """every name that LightCake itself binds, by file: a name in a
     proof that is not one of these is HOL Light's own and this
     port has it too"""
  out = {}
  for root, _, fs in os.walk(LC + 'src'):
    for f in fs:
      if not f.endswith('.ml'): continue
      p = os.path.join(root, f)
      for m in re.finditer(r"^let ([A-Za-z0-9_']+)"
                           r"(?:,([A-Za-z0-9_']+))?\s*=", open(p).read(),
                           re.M):
        for g in m.groups():
          if g: out[g] = os.path.basename(p)[:-3]
  return out


def ours_bindings():
  """every name a file of this port binds"""
  out = {}
  for root, _, fs in os.walk(ML):
    for f in fs:
      if not f.endswith('.ml'): continue
      p = os.path.join(root, f)
      for m in re.finditer(r"^let ([A-Za-z0-9_']+)"
                           r"(?:,([A-Za-z0-9_']+))?\s*=", open(p).read(),
                           re.M):
        for g in m.groups():
          if g: out.setdefault(g, f[:-3])
  return out


def deps(argv):
  """which files of LightCake the proofs of one of its files name,
     and how much of that this port already has"""
  if not argv: print('deps <theory>'); return 1
  nm = argv[0]
  p = theirs_of(nm)
  if not p: print('LightCake has no %s.ml' % nm); return 1
  lb, ob = lc_bindings(), ours_bindings()
  thms = theorems(p)
  byfile = collections.Counter()
  here = ours = free = 0
  for n, body in thms.items():
    for w in set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", body)):
      if w not in lb: continue
      if lb[w] == nm: here += 1
      elif w in ob: ours += 1
      else: byfile[lb[w]] += 1; free += 1
  print('%d theorems of %s; the names their proofs use that'
        ' LightCake binds:' % (len(thms), nm))
  print('  %4d in this same file' % here)
  print('  %4d in a file of this port too, by the same name' % ours)
  print('  %4d only LightCake has, from:' % free)
  for f, k in byfile.most_common(12):
    print('       %4d  %s' % (k, f))
  return 0


def file_head(nm, src):
  """the comment that says where the file comes from, in a box
     that the port's own files keep to"""
  body = [
    'The theorems of %sTheory that LightCake proves and this' % nm,
    'port needs, taken from its %s.' % src,
    '',
    'LightCake is the other HOL Light port of CakeML',
    '(hol-light-family/LightCake, BSD 3-Clause); its HOL4 library',
    'layer is proved, and of these theories this port has only',
    'the definitions that CakeML needs.  tools/lightcake.py',
    'writes this file: the statements and the proofs are',
    "LightCake's, with its constants under the names this port",
    'gives them.  What it could not take, and why, is at the end.']
  bar = '(* ' + '=' * 64 + ' *)'
  return '\n'.join([bar] +
                   ['(*  %-62s*)' % l for l in body] + [bar]) + '\n'




def wrap72(text):
  """LightCake writes wider lines than this port allows, so a
     line over 72 characters is broken at a space.  A break
     inside a quotation is harmless (a term is the same term
     whatever its whitespace); one inside a string of OCaml is
     not, so those spans are left alone."""
  def spans(l):
    """the stretches of the line that are an OCaml string"""
    out, i = [], 0
    while True:
      a = l.find('"', i)
      if a < 0: return out
      b = a + 1
      while b < len(l) and (l[b] != '"' or l[b - 1] == '\\'): b += 1
      out.append((a, b)); i = b + 1
  out = []
  for line in text.split('\n'):
    ind = len(line) - len(line.lstrip())
    cont = ' ' * (ind + 2)
    while len(line) > 72:
      sp = spans(line)
      cut = -1
      for i in range(min(72, len(line) - 1), ind, -1):
        if line[i] == ' ' and not any(a < i < b for a, b in sp):
          cut = i; break
      if cut < 0: break
      out.append(line[:cut].rstrip())
      line = cont + line[cut + 1:]
      ind = len(cont)
    out.append(line)
  return '\n'.join(out)


def rename(text, m):
  """LightCake's constants under this port's names.  A name is
     only renamed where it stands on its own: lookup_def is the
     binding of the definition and keeps its name in both."""
  for k in sorted(m, key=len, reverse=True):
    if k == m[k]: continue
    text = re.sub(r"\b%s\b" % re.escape(k), m[k], text)
  return text


def emit(argv):
  """tools/lightcake/<theory>.ml, which the port appends to its
     own file of that theory"""
  if not argv: print('import <theory>'); return 1
  nm = argv[0]
  a, b = ours_of(nm), theirs_of(nm)
  if not a or not b:
    print('no pair of files for %s' % nm); return 1
  m, _, _ = rename_map(nm)
  lb, ob = lc_bindings(), ours_bindings()
  theirs, ours = theorems(b), theorems(a)
  take, left = [], []
  for n, body in theirs.items():
    if n in ours: continue
    # every name of LightCake's that the block uses has to be one
    # this port has, one the block before it brings, or a
    # constant that is renamed
    need = [w for w in sorted(set(re.findall(
              r"[A-Za-z_][A-Za-z0-9_']*", body)))
            if w in lb and w not in ob and w not in m
            and w not in theirs and w != n]
    if need: left.append((n, need))
    else: take.append((n, body))
  out = [file_head(nm, os.path.relpath(b, LC + 'src')[:-3])]
  for n, body in take:
    out.append(wrap72(rename(body.rstrip(), m)))
  if left:
    out.append("(* What this port cannot take from LightCake's "
               "%s yet, with the names of its own that "
               "each proof uses:" % nm)
    out.append('\n'.join('     %-32s %s' % (n, ' '.join(need[:6]))
                          for n, need in left))
    out.append('*)')
  d = T + 'lightcake'
  if not os.path.isdir(d): os.mkdir(d)
  open(d + '/' + nm + '.ml', 'w').write('\n\n'.join(out) + '\n')
  print('%s: %d theorems taken, %d left (tools/lightcake/%s.ml)'
        % (nm, len(take), len(left), nm))
  return 0


def main(argv):
  if not argv: print(__doc__); return 0
  if argv[0] == 'import': return emit(argv[1:])
  if argv[0] == 'names': return names(argv[1:])
  if argv[0] == 'report': return report(argv[1:])
  if argv[0] == 'deps': return deps(argv[1:])
  print(__doc__); return 1


if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
