"""what LightCake has that the port can take

     python3 -I tools/lightcake.py names [<theory>]
     python3 -I tools/lightcake.py report
     python3 -I tools/lightcake.py deps <theory>
     python3 -I tools/lightcake.py import <theory>
     python3 -I tools/lightcake.py fill <theory>
     python3 -I tools/lightcake.py drop <theory> <name>...
     python3 -I tools/lightcake.py where <theory>

LightCake (`lightcake-src/`, see README.md) is the other port of
CakeML to HOL Light: narrow and deep where this one is wide and
shallow.  Its HOL4 library layer is proved -- 3014 theorems of
listTheory, finite_mapTheory, sptreeTheory and the rest -- and of
those theories this port has only the definitions that CakeML
needs.  So they are what it has to give.

What joins the two vocabularies is the HOL4 name, because both
ports name after HOL4: LightCake's `doc/names.tsv` and
`doc/library_renames.tsv` say what it calls each thing of the
closure, and this port's own renaming says what this port calls
it.  Where both ports have the file of a theory, the pair of
files says it more precisely still, binding for binding.

`import` writes `tools/lightcake/<theory>.ml`, which a re-port
appends to this port's own file of that theory.  A block is
taken only when every name it uses is one this port has **at
that point in the load order**, and a name of LightCake's proof
kit is never one of those: that is what keeps HOL4-style tactics
out, and `tools/extra/<theory>.ml` is where HOL Light's own way
of doing what such a name does is written.  What a check of the
blocks found does not go through
(`tools/bin/lightcake-check`, which writes
`tools/lightcake/<theory>.bad`) is left out with the reason.

`fill` writes the proofs LightCake has for the theorems this
port states and cheats into `proofs/<path>.prf`, which a re-port
splices into the file; `drop` takes a proof of the store out
again, under either name it goes by.  `tools/bin/lightcake-take`
and `tools/bin/lightcake-fill` are the two loops that do it with
the check in them, and nothing of either reaches `ml/` until
every block of it has been run.

`names` prints the map of a theory (or the count for every
theory); `report` says, for every file both ports have, how many
theorems are shared, how many of this port's cheats LightCake
proves, and how many of its proofs use a tactic of its own HOL4
kit rather than HOL Light's; `deps` says what a theory of it
would need.
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
MAKER = (r"cake_def|cake_def_wf|cake_defn|new_definition|"
         r"new_recursive_definition|new_specification|"
         r"define_[a-z_0-9]+|assume_definition[a-z_]*")
BIND = re.compile(r"^let ([A-Za-z0-9_']+)(?:,[A-Za-z0-9_']+)? = "
                  r"(" + MAKER + r")\b", re.M)
# LightCake makes the definition in a let of the block and then
# proves the form it uses, so the maker is not on the line of
# the binding: that block is a definition all the same
INNER = re.compile(r"^let ([A-Za-z0-9_']+)(?:,[A-Za-z0-9_']+)? ="
                   r"\s+let [A-Za-z0-9_']+ = (" + MAKER + r")\b",
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


def definitions(path, upto=None):
  """binding -> constant, for a file of either port.  A file of
     this port is read up to the block an import appended to it,
     or the import would be read back as what this port says"""
  try: s = open(path).read()
  except OSError: return {}
  if upto and upto in s: s = s[:s.index(upto)]
  out = {}
  for r in (BIND, INNER):
    for m in r.finditer(s):
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
  ours, theirs = definitions(a, CUT), definitions(b)
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


def theorems(path, upto=None):
  """name -> the text of its block, for a file of either port"""
  try: s = open(path).read()
  except OSError: return {}
  if upto and upto in s: s = s[:s.index(upto)]
  out = {}
  # a block ends at its own ;;, so the comments that stand
  # between it and the next one are no part of it
  for m in re.finditer(r"^let ([A-Za-z0-9_']+) = prove", s, re.M):
    out[m.group(1)] = s[m.start():block_end(s, m.end())]
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


LET = re.compile(r"^let\s+(?:rec\s+)?([A-Za-z0-9_']+)"
                 r"((?:\s*,\s*[A-Za-z0-9_']+)*)", re.M)

# where HOL Light itself is, for the names it binds
HLDIR = os.environ.get(
  'HOLLIGHT', '/home/freek/.opam/hol-light/lib/hol_light') + '/'

BINDER = re.compile(r"^(?:let|and)\s+(?:rec\s+)?([^=]*)=", re.M)


OCAML = set("""let in fun function match with if then else try
  and rec of begin end true false type val module open exception
  assert lazy new object struct sig when as do done to for while
  mod lor land lsl lsr asr or not
  fst snd compare min max abs succ pred ignore incr decr ref
  string_of_int int_of_string print_string print_newline
  invalid_arg raise Printf Format List String Array Char Bool
  Int Hashtbl Sys Stdlib Option Result Either Seq Buffer
  Not_found Failure Invalid_argument Exit Some None""".split())

_holnames = []


def HOLNAMES():
  """the names HOL Light binds, read once"""
  if not _holnames: _holnames.append(hol_bindings())
  return _holnames[0]


def hol_bindings():
  """every name HOL Light itself binds, in its core and in the
     one library this port loads.  A proof of LightCake's may
     use any of them, and a name it uses that is neither one of
     these nor one of this port's is a name this port has not
     got: its RTC_INDUCT_R is of Library/rstc.ml, which this
     port does not load"""
  out, seen = set(), set()
  fs = ['hol_lib.ml', 'hol.ml', 'help.ml', 'database.ml',
        'Library/words.ml']
  while fs:
    f = fs.pop()
    if f in seen: continue
    seen.add(f)
    try: s = open(HLDIR + f, errors='replace').read()
    except OSError: continue
    fs += re.findall(r'loads?\s+"([^"]+)"', s)
    fs += re.findall(r'needs\s+"([^"]+)"', s)
    for m in BINDER.finditer(s):
      out |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", m.group(1)))
    # the kernel is a module, and what it gives is the val lines
    # of its signature (concl, frees, type_of, ...), which no
    # let at the start of a line declares
    out |= set(re.findall(r"^\s*val\s+\(?\s*([A-Za-z_][A-Za-z0-9_']*)",
                          s, re.M))
  return out


def bindings(path, upto=None):
  """what a file binds at the top level, in the order of the
     file: the names of each binding and the text of its block.
     A binding that takes arguments (a tactic of LightCake's is
     usually one) binds its name and no other"""
  try: s = open(path).read()
  except OSError: return []
  if upto and upto in s: s = s[:s.index(upto)]
  out = []
  for m in LET.finditer(s):
    ns = [m.group(1)] + re.findall(r"[A-Za-z0-9_']+", m.group(2))
    out.append((ns, s[m.start():block_end(s, m.end())]))
  return out


def lc_bindings():
  """every name that LightCake itself binds, by file, and the
     ones its proof kit binds.  A name of the kit is a thing this
     port does not have whatever it binds the word to -- its
     size_def is the size function of sptree and the kit's is the
     one that makes such a function -- so a kit name counts as
     missing until tools/extra/ writes this port's own"""
  out, kit = {}, set()
  for root, _, fs in os.walk(LC + 'src'):
    for f in fs:
      if not f.endswith('.ml'): continue
      for ns, _ in bindings(os.path.join(root, f)):
        for n in ns:
          out[n] = f[:-3]
          if '/kit' in root: kit.add(n)
  return out, kit


def ours_files(nm, rank):
  """the files of this port that a file of <nm> can rely on:
     the ones that load before it, and its own.  A name this
     port binds in a file that loads after this one is no name
     this file can use -- its spt_closure has is_adjacent_def,
     and sptree loads first"""
  out = []
  for root, _, fs in os.walk(ML):
    for f in fs:
      if not f.endswith('.ml'): continue
      t = f[:-3]
      if t == nm or t not in rank or rank[t] < rank.get(nm, 0):
        out.append(os.path.join(root, f))
  return out


def ours_bindings(nm, rank):
  """every name such a file of this port binds, and the ones
     that tools/extra/ adds to the file of <nm>: a bridge for a
     name of LightCake's is written there, and a port writes it
     into the file before anything of an import"""
  out, bridge = {}, set()
  for p in ours_files(nm, rank):
    for ns, _ in bindings(p, CUT):
      for n in ns: out.setdefault(n, os.path.basename(p)[:-3])
  for f in sorted(os.listdir(T + 'extra')):
    if f[:-3] != nm: continue
    for ns, _ in bindings(T + 'extra/' + f, CUT):
      for n in ns:
        out.setdefault(n, f[:-3]); bridge.add(n)
  return out, bridge


def ours_terms(nm, rank):
  """every name such a file of this port writes inside a term:
     what it has, as against what a theory it ports would have
     in HOL4 (of a library theory it has only the part CakeML
     needs)"""
  out = set()
  for p in ours_files(nm, rank):
    s = open(p).read()
    if CUT in s: s = s[:s.index(CUT)]
    for q in re.findall(r"`[^`]*`", s):
      out |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", q))
  return out


def lc_names(d, thy0=None):
  """LightCake's name for every constant, constructor, field and
     type of the closure, mapped to this port's name for it, or
     to None where this port has no theory for it.  Both ports
     name after HOL4, so the HOL4 name is what joins them:
     LightCake's doc/names.tsv says what it calls each one, and
     this port's own renaming says what this port calls it.

     One name can stand in several theories -- LightCake's size
     is sptree's and this port's sptree_size -- so the theory
     being imported is read first, and a theory this port does
     not have never puts out one it does"""
  out = {}
  for f in ('doc/names.tsv', 'doc/library_renames.tsv'):
    for l in open(LC + f):
      fs = l.rstrip('\n').split('\t')
      if len(fs) < 5 or fs[2] in ('kind', 'theorem'): continue
      thy, h4, lc = fs[1], fs[3], fs[4]
      v = d.rename.get((thy, h4), h4) \
          if thy in d.thy_of_file else None
      if thy == thy0 or lc not in out or (out[lc] is None and v):
        out[lc] = v
  return out


def deps(argv):
  """which files of LightCake the proofs of one of its files name,
     and how much of that this port already has"""
  if not argv: print('deps <theory>'); return 1
  nm = argv[0]
  p = theirs_of(nm)
  if not p: print('LightCake has no %s.ml' % nm); return 1
  (lb, _), (ob, _) = lc_bindings(), ours_bindings(nm, {})
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


MARK = 'The theorems of %sTheory that LightCake proves'
# what a file of this port has of its own ends where the block
# that an import appended to it starts: an import reads the port
# as the port is written, not as an import before it left it
CUT = 'Theory that LightCake proves'


def file_head(nm, src):
  """the comment that says where the file comes from, in a box
     that the port's own files keep to"""
  body = [
    (MARK % nm) + ' and this',
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




def wrap72(text, wide=72):
  """LightCake writes wider lines than this port allows, so a
     line over 72 characters is broken at a space.  A break
     inside a quotation is harmless (a term is the same term
     whatever its whitespace); one inside a string of OCaml is
     not, so those spans are left alone.  A proof of the store
     is written with three characters after it (the bracket and
     the ;; that the port puts there), so it asks for less"""
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
    while len(line) > wide:
      sp = spans(line)
      cut = -1
      for i in range(min(wide, len(line) - 1), ind, -1):
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


def subber(m, skip):
  """one pass that renames every name of a map at once"""
  ks = [k for k in m if k != m[k] and k not in skip]
  if not ks: return lambda s: s
  rx = re.compile(r"(?<![A-Za-z0-9_'])(" +
                  '|'.join(sorted(map(re.escape, ks),
                                  key=len, reverse=True)) +
                  r")(?![A-Za-z0-9_'])")
  return lambda s: rx.sub(lambda mo: m[mo.group(1)], s)


def rename_terms(text, m, skip):
  """the same, but only inside a quotation and never for a name
     the block binds as a variable.  A name of the closure can be
     a word of HOL Light or of OCaml as well -- LightCake's term
     is this port's pattern_semantics_term, and a tactic of
     LightCake's writes (t:term) for a term of HOL Light -- so a
     map read off the names of the whole closure is only safe
     where a name is the name of a thing"""
  f = subber(m, skip)
  return re.sub(r"`[^`]*`", lambda mo: f(mo.group(0)), text)


def port_db():
  """this port's own reading of the HOL4 sources, which says what
     name it gives each thing and in what order its files load"""
  sys.path.insert(0, T)
  import db
  return db.Db()


def port_names(thy, d):
  """every name of this port that is in the scope of its file of
     <thy>, with the theory it comes from: a name LightCake
     writes for a variable and this port for a constant or a type
     cannot stand in an imported statement -- where it is a
     constant it would not parse, and where it is a type it would
     make this file need the theory that has it.  Only a theory
     that loads before this one counts, which is the rule the
     needs of a file are computed by"""
  rank = dict((t, i) for i, (t, _, _) in enumerate(d.order))
  out = {}
  for nm, ts in d.defs.items():
    for t, _ in ts:
      if t in d.thy_of_file and d.rename.get((t, nm), nm) == nm \
         and rank.get(t, 0) < rank.get(thy, 0):
        out.setdefault(nm, t)
  return out


WORD = r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])"
VAR = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def bound_names(text):
  """the names a block binds as a variable: the ones a !, a ?, a
     lambda or a @ has in front of its dot.  A name that is not
     one of these is a constant, whoever defines it"""
  out, i, n = set(), 0, len(text)
  while i < n:
    if text[i] not in '!?\\@': i += 1; continue
    j, names = i + 1, []
    while j < n:
      if text[j] in ' \t\n(),': j += 1; continue
      if text[j] == ':':
        # the type of the variable, which is no name of a variable
        d = 0
        j += 1
        while j < n:
          if text[j] == '(': d += 1
          elif text[j] == ')':
            if not d: break
            d -= 1
          elif text[j] == '.' and not d: break
          j += 1
        continue
      m = VAR.match(text, j)
      if not m: break
      names.append(m.group()); j = m.end()
    if j < n and text[j] == '.': out |= set(names)
    i = max(j, i + 1)
  return out


def unclash(text, thy, known, port):
  """the variables of a block that this port uses for a name of
     its own, primed until they are nobody's"""
  done = []
  for w in sorted(bound_names(text)):
    if w in known or w not in port or port[w] == thy: continue
    v = w + "'"
    while re.search(WORD % re.escape(v), text): v += "'"
    text = re.sub(WORD % re.escape(w), v, text)
    done.append((w, v, port[w]))
  return text, done


class Ctx:
  """what both an import and a fill have to know about a theory:
     the two files, the map from LightCake's names to this
     port's, and what this port has at the point its file of the
     theory stands at"""

  def __init__(self, nm):
    self.nm = nm
    self.a, self.b = ours_of(nm), theirs_of(nm)
    if not self.a or not self.b: return
    d = self.d = port_db()
    m, _, _ = rename_map(nm)
    self.rank = dict((t, i) for i, (t, _, _) in enumerate(d.order))
    self.lcn = lc_names(d, nm)
    # the port's own file of the theory is what says how the
    # port names the theory's constants, and it says it more
    # precisely than the HOL4 name does: this port's
    # tailrec_TAILREC is HOL4's tailrec$TAILREC under the name
    # LightCake gives it too, while TAILREC is While's, which
    # is another constant of this port altogether
    for k in set(definitions(self.a, CUT).values()):
      if self.lcn.get(k) not in (None, k): self.lcn[k] = k
    self.ot = ours_terms(nm, self.rank)
    # LightCake's name for a thing of the closure, under this
    # port's name for it; the pair of files of this theory says
    # it more precisely than the HOL4 names do, so that map wins
    gm = dict((k, v) for k, v in self.lcn.items() if v)
    gm.update(m)
    self.lb, self.kit = lc_bindings()
    self.ob, self.bridge = ours_bindings(nm, self.rank)
    # what this port has of its own, which is its file without
    # the block that an import before this one appended to it
    self.ours = theorems(self.a, MARK % nm)
    self.defs = set(definitions(self.b))
    # the name each port binds the definition of a constant to:
    # LightCake's sptree_size_def is this port's size_def, and a
    # proof that rewrites with it has to say the name this port
    # uses.  The induction theorem of a definition goes by the
    # same name with _ind, in both
    obyc = {}
    for k, v in definitions(self.a, CUT).items():
      obyc.setdefault(v, k)
    # LightCake keeps the HOL4 name of a library constant unless
    # it had to change it (doc/library_renames.tsv), and this
    # port has its own renaming of the same HOL4 name: that is
    # the join for a theory doc/names.tsv does not cover
    ourname = lambda c: self.lcn.get(c) or d.rename.get((nm, c), c)
    for k, v in definitions(self.b).items():
      o = m.get(v) or ourname(v)
      if not o: continue
      if o != v and o in self.ot: m.setdefault(v, o)
      if o in obyc and k != obyc[o]:
        m[k] = obyc[o]
        if k.endswith('_def') and obyc[o].endswith('_def'):
          m[k[:-4] + '_ind'] = obyc[o][:-4] + '_ind'
    self.m, self.gm = m, gm
    # a name of LightCake's is there to be used once this port
    # has the thing it names: a block before it in the file, a
    # binding of this port, or a constant this port writes
    self.have = ((set(self.ob) - (self.kit - self.bridge)) |
                 set(k for k in self.defs
                     if k in self.ob or k in m))
    self.known = set(gm.values()) | set(self.lb)
    self.port = port_names(nm, d)
    # the map of the whole closure, less what the pair of files
    # of this theory already says
    self.rest = dict((k, v) for k, v in gm.items() if k not in m)
    self.bad = {}
    try:
      for l in open(T + 'lightcake/' + nm + '.bad'):
        k, _, v = l.rstrip('\n').partition('\t')
        self.bad[k] = v
    except OSError: pass

  def missing(self, ns, body):
    """the names of LightCake's that this port has not got"""
    need, bnd = [], bound_names(body)
    # what stands outside a quotation is OCaml, so it is a name
    # of HOL Light's or of this port's and not a variable of a
    # term; what the block binds itself is nobody else's
    code = set(re.findall(
      r"[A-Za-z_][A-Za-z0-9_']*",
      re.sub(r'\(\*.*?\*\)', ' ',
             re.sub(r'"[^"]*"', ' ',
                    re.sub(r"`[^`]*`", ' ', body)), flags=re.S)))
    mine = set(re.findall(r"\b(?:let|fun)\s+([A-Za-z_][A-Za-z0-9_']*)",
                          body))
    for w in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*",
                                   body))):
      if w in ns or w in bnd or w in mine: continue
      if w in self.lb and w not in self.have: need.append(w)
      elif w in self.lcn and \
           self.gm.get(w, self.lcn[w]) not in self.ot:
        need.append(w)
      elif w in code and w not in HOLNAMES() and \
           w not in self.have and w not in OCAML:
        need.append(w)
    return need

  def ported(self, body):
    """a block of LightCake's in this port's vocabulary"""
    t = rename_terms(rename(body.rstrip(), self.m), self.rest,
                     bound_names(body))
    return unclash(t, self.nm, self.known, self.port)


def emit(argv):
  """tools/lightcake/<theory>.ml, which the port appends to its
     own file of that theory"""
  if not argv: print('import <theory>'); return 1
  nm = argv[0]
  c = Ctx(nm)
  if not c.a or not c.b:
    print('no pair of files for %s' % nm); return 1
  m, ob = c.m, c.ob
  ours, defs, bad, have = c.ours, c.defs, c.bad, c.have
  take, left = [], []
  for ns, body in bindings(c.b):
    if [n for n in ns
        if n in defs or n in ours
        or (n != '_' and n in ob and n not in c.bridge)]:
      # a definition of LightCake's that this port makes its own
      # way, or a name this port binds itself: what it binds is
      # there only where this port binds it too.  Taking such a
      # block would shadow this port's binding of the name, and
      # every later file reads the name as this port writes it
      have |= set(n for n in ns
                  if n in ob or n in m or n in ours)
      continue
    if ns[0] in bad:
      left.append((ns[0], ['--'] + bad[ns[0]].split())); continue
    need = c.missing(ns, body)
    if need: left.append((ns[0], need)); continue
    take.append((ns[0], body)); have |= set(ns)
  out = [file_head(nm, os.path.relpath(c.b, LC + 'src')[:-3])]
  clash = {}
  for n, body in take:
    t, done = c.ported(body)
    for w, v, t2 in done: clash[w] = (v, t2)
    out.append(wrap72(t))
  if left:
    out.append("(* What this port cannot take from LightCake's %s\n"
               "   yet, with the names of its own that each proof\n"
               "   uses:" % nm)
    rows = []
    for n, need in left:
      line = '     %-32s' % n
      col = min(len(line), 38)
      for w in need:
        if len(line) + 1 + len(w) > 72 and line.strip():
          rows.append(line.rstrip()); line = ' ' * col
        line += ' ' + w
      rows.append(line.rstrip())
    out.append('\n'.join(rows))
    out.append('*)')
  dd = T + 'lightcake'
  if not os.path.isdir(dd): os.mkdir(dd)
  open(dd + '/' + nm + '.ml', 'w').write('\n\n'.join(out) + '\n')
  print('%s: %d blocks taken, %d left (tools/lightcake/%s.ml)'
        % (nm, len(take), len(left), nm))
  for w in sorted(clash):
    print('   the variable %s is primed: %s has it'
          % (w, clash[w][1]))
  return 0


def tactic_of(body):
  """the tactic of a prove block: what stands after the
     statement, without the parentheses of the call"""
  i = body.index('prove')
  j = body.index('(', i)
  d, q, st, k = 0, False, False, j
  while k < len(body):
    ch = body[k]
    if st:
      if ch == '\\': k += 2; continue
      if ch == '"': st = False
    elif q:
      if ch == '`': q = False
    elif ch == '`': q = True
    elif ch == '"': st = True
    elif ch == '(': d += 1
    elif ch == ')':
      d -= 1
      if not d: break
    k += 1
  inner = body[j + 1:k]
  a = inner.index('`')
  b = inner.index('`', a + 1)
  rest = inner[b + 1:].lstrip()
  if rest.startswith(','): rest = rest[1:]
  return rest.strip()


def reindent(tac):
  """the tactic as the proof store writes it: in brackets of its
     own, the first line two spaces in and the rest three, which
     is where the bracket leaves them"""
  ls = [l for l in tac.split('\n')]
  pad = min((len(l) - len(l.lstrip()) for l in ls[1:] if l.strip()),
            default=0)
  out = ['  (' + ls[0].strip()]
  for l in ls[1:]:
    out.append('   ' + l[pad:].rstrip() if l.strip() else '')
  return '\n'.join(out).rstrip() + ')'


def lc_thm_names():
  """LightCake's name for a theorem of the closure, under the
     HOL4 name that both ports call it by"""
  out = {}
  for f in ('doc/names.tsv', 'doc/library_renames.tsv'):
    for l in open(LC + f):
      fs = l.rstrip('\n').split('\t')
      if len(fs) < 5 or fs[2] != 'theorem': continue
      out[fs[4]] = fs[3]
  return out


CHEATED = re.compile(r"(?:^\(\* ([A-Za-z0-9_']+)(?:\[[^\]]*\])? \*\)\n)?"
                     r"^let ([A-Za-z0-9_']+) = prove", re.M)


def our_thms(path, cheats=False):
  """the theorems this port states, by the HOL4 name that the
     proof store calls them by, mapped to the name this port
     binds them under: the port writes the HOL4 name in a
     comment where the two are not the same.  With <cheats> only
     the ones this port states and does not prove"""
  s = open(path).read()
  if CUT in s: s = s[:s.index(CUT)]
  out = {}
  for mo in CHEATED.finditer(s):
    body = s[mo.start():block_end(s, mo.end())]
    if cheats and 'CHEAT_TAC' not in body: continue
    out[mo.group(1) or mo.group(2)] = mo.group(2)
  return out


def our_cheats(path):
  return our_thms(path, True)


def fill(argv):
  """the proofs of LightCake's that this port can use for a
     theorem it states and cheats, into proofs/<path>.prf"""
  if not argv: print('fill <theory>'); return 1
  nm = argv[0]
  c = Ctx(nm)
  if not c.a or not c.b:
    print('no pair of files for %s' % nm); return 1
  sys.path.insert(0, T)
  import proofstore
  mlrel = re.sub(r'^.*/ml/', '', c.a)
  pp = proofstore.path_of(mlrel)
  there = set(proofstore.load(mlrel))
  h4 = lc_thm_names()
  theirs = {}
  for ns, body in bindings(c.b):
    if ' = prove' not in body.split('\n')[0]: continue
    theirs[h4.get(ns[0], ns[0])] = (ns[0], body)
  took, left = [], []
  for n, bind in sorted(our_cheats(c.a).items()):
    if n in there or n not in theirs: continue
    k, body = theirs[n]
    need = c.missing([k], body)
    if need: left.append((n, need)); continue
    t, _ = c.ported(tactic_of(body))
    took.append((n, wrap72(reindent(t), 69)))
  if took:
    os.makedirs(os.path.dirname(pp), exist_ok=True)
    old = open(pp).read().rstrip('\n') + '\n\n' \
          if os.path.exists(pp) else ''
    open(pp, 'w').write(
      old + '\n\n'.join('### %s\n%s' % (n, t) for n, t in took)
      + '\n')
  print('%s: %d proofs of %d cheats LightCake has, %d of them '
        'with a name this port has not got'
        % (nm, len(took), len(took) + len(left), len(left)))
  return 0


def drop(argv):
  """the sections of a proof store that a check says do not go
     through, taken out again"""
  if len(argv) < 2: print('drop <theory> <name>...'); return 1
  nm = argv[0]
  a = ours_of(nm)
  if not a: print('no file for %s' % nm); return 1
  # a check names a theorem as this port binds it and the store
  # names it as HOL4 does, so either name takes it out
  byb = dict((b, n) for n, b in our_thms(a).items())
  names = set(byb.get(n, n) for n in argv[1:])
  sys.path.insert(0, T)
  import proofstore
  pp = proofstore.path_of(re.sub(r'^.*/ml/', '', a))
  if not os.path.exists(pp): print('no store for %s' % nm); return 1
  out, keep, gone = [], True, []
  for l in open(pp).read().split('\n'):
    m = re.match(r'^###[ \t]+(\S+)[ \t]*$', l)
    if m:
      keep = m.group(1) not in names
      if not keep: gone.append(m.group(1))
    if keep: out.append(l)
  open(pp, 'w').write('\n'.join(out).strip('\n') + '\n')
  print('%s: %d sections taken out%s'
        % (nm, len(gone), (': ' + ' '.join(gone)) if gone else ''))
  return 0


def where(argv):
  """the file of this port that holds a theory, as the port
     names it: what tools/bin/tryfile takes"""
  if not argv: print('where <theory>'); return 1
  a = ours_of(argv[0])
  if not a: print('no file for %s' % argv[0], file=sys.stderr); return 1
  print(os.path.relpath(a, ML))
  return 0


def main(argv):
  if not argv: print(__doc__); return 0
  if argv[0] == 'where': return where(argv[1:])
  if argv[0] == 'import': return emit(argv[1:])
  if argv[0] == 'names': return names(argv[1:])
  if argv[0] == 'report': return report(argv[1:])
  if argv[0] == 'deps': return deps(argv[1:])
  if argv[0] == 'fill': return fill(argv[1:])
  if argv[0] == 'drop': return drop(argv[1:])
  print(__doc__); return 1


if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
