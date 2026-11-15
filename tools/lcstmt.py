"""LightCake's statement of a theorem, in this port's names

  python3 -I tools/lcstmt.py <theory> [<name>...]
  python3 -I tools/lcstmt.py -u [<file-of-unstated>]

The statements that HOL Light rejects are nearly all one shape: a
proof that relates two languages, where HOL4 resolves a shared
name by the type and this port has to be told which one.
LightCake (`lightcake-src/`, see README.md) has written the same
statement in HOL Light already, with the resolution done, so
there is no need to work it out from the HOL4 source: this prints
what it says, with its constants renamed to this port's (the HOL4
name joins the two vocabularies, as `tools/lightcake.py` does it).

With -u it reads a run's `tmp/unstated.txt` and prints, for every
statement in it that LightCake has, this port's version and
LightCake's one after the other.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
DELTA = [False]
sys.path.insert(0, T)
import db as dbmod, lightcake


def lc_statement(thy, name, m, d):
  """LightCake's statement of a theorem of this theory, renamed"""
  p = lightcake.theirs_of(thy)
  if not p: return None
  # LightCake splits a big file into <theory>_p1.ml and the rest
  paths = [p] + sorted(q for q in lightcake.lc_files()
                       if re.match(r'^%s_p\d+\.ml$' % re.escape(thy),
                                   os.path.basename(q)))
  for q in paths:
    thms = lightcake.theorems(q)
    for key in (name, thy + '_' + name):
      if key in thms:
        body = thms[key]
        # the statement is the quotation, without the tactic
        mm = re.search(r'`(.*?)`', body, re.S)
        if not mm: return None
        return lightcake.rename_terms(
          lightcake.rename(mm.group(1), m), {}, set())
  return None


def ours_statement(thy, name, d):
  try:
    text = open(T + '../ml/' + d.mlpath_of(thy)).read()
  except OSError:
    return None
  for key in (name, thy + '_' + name):
    mm = re.search(r"^let %s =\s*\n?\s*(?:try )?prove\b" % re.escape(key),
                   text, re.M)
    if not mm: continue
    # the statement is the first quotation of the block
    q = re.search(r'`(.*?)`', text[mm.end():], re.S)
    if q: return q.group(1).rstrip()
  return None


PREF = re.compile(r"^([A-Za-z][A-Za-z0-9]*?)_([A-Za-z_][A-Za-z0-9_\']*)$")


_CONSTS = set()


def constants():
  """every constant of the port, as tools/bin/intargs dumps them:
     a name LightCake writes that this port has no constant of is
     LightCake spelling its own prefix (wl_state_locals_fupd for
     wordSem_state_locals_fupd) and not a resolution this port
     got wrong"""
  if not _CONSTS:
    try:
      for l in open(T + 'constants.txt'):
        if l.strip(): _CONSTS.add(l.split()[0])
    except OSError: pass
  return _CONSTS


def deltas(ours, lc):
  """the names the two ports resolve differently: a token of the
     one whose tail another token of the other has with another
     head (wordSem_pop_env here, dataSem_pop_env there).  The
     tails that both write the same way are left out"""
  def toks(t):
    return [w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_\']*", t)]
  a, b = toks(ours), toks(lc)
  sa, sb = set(a), set(b)
  out = []
  for w in a:
    if w in sb: continue
    m = PREF.match(w)
    if not m: continue
    for v in sb:
      m2 = PREF.match(v)
      if m2 and m2.group(2) == m.group(2) and m2.group(1) != m.group(1):
        if v not in constants(): continue
        if (w, v) not in out: out.append((w, v))
  return out


def main(argv):
  if not argv: print(__doc__); return 0
  d = dbmod.Db()
  if argv[0] == '-d':
    argv = argv[1:] or ['-u']
    DELTA[0] = True
  if argv[0] == '-u':
    path = argv[1] if argv[1:] else T + '../tmp/unstated.txt'
    rows = []
    for l in open(path):
      fs = l.split('\t')
      if len(fs) < 2: continue
      thy = os.path.basename(fs[0])[:-3]
      rows.append((thy, fs[1]))
  else:
    thy = argv[0]
    rows = [(thy, n) for n in argv[1:]]
    if not argv[1:]:
      print('lcstmt <theory> <name>...'); return 1
  seen, got, lost = None, 0, 0
  for thy, name in rows:
    if thy != seen:
      seen = thy
      m = lightcake.lc_names(d, thy)
      m = {k: v for k, v in m.items() if v}
    lc = lc_statement(thy, name, m, d)
    if lc is None:
      lost += 1
      print('=== %s %s\n    LightCake has no such theorem' % (thy, name))
      continue
    got += 1
    ours = ours_statement(thy, name, d)
    if DELTA[0]:
      ds = deltas(ours or '', lc)
      if ds:
        print('%-26s %-40s %s' % (thy, name,
              '  '.join('%s -> %s' % x for x in ds)))
      continue
    print('=== %s %s' % (thy, name))
    print('--- this port')
    print(ours if ours else '    (not stated)')
    print('--- LightCake, in this port' + chr(39) + 's names')
    print(lc.rstrip())
  print('\n%d statements LightCake has, %d it has not' % (got, lost))
  return 0


if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
