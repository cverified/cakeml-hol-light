"""the names of HOL4's libraries that the port has not

  python3 -I tools/libnames.py

The statements of phase two use names of HOL4's core theories
that the definitions of phase one never met (`TotOrd` of toto,
`transitive` of relation, `BAG_IMAGE` of bag, ...).  A name that
no theory of the port defines, that HOL Light does not have and
that the hand written library layer does not provide is a free
variable of the statement that uses it, which makes that
statement say something else than the source does.

This says which names those are and which HOL4 theory of
`hol4-src/src` defines them, so that the library layer can gain
them (or `tools/libs.txt` the theory).  A short lower case name
is left out: it is a variable of the statement, not a constant.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4

# the definitions of HOL4's own sources, which the index below is
# built from once and kept in tmp/hol4defs.txt
DEFPAT = [
  re.compile(r'^Definition\s+([A-Za-z0-9_\']+)', re.M),
  re.compile(r'^(?:val|Theorem)\s+([A-Za-z0-9_\']+)\s*=\s*'
             r'(?:new_definition|new_recursive_definition|'
             r'new_specification|Define|TotalDefn)', re.M),
  re.compile(r'new_definition\s*\(\s*"([A-Za-z0-9_\']+)"', re.M),
  re.compile(r'^Inductive\s+([A-Za-z0-9_\']+)', re.M),
]


def build_index(root, cache):
  """name -> the theories of HOL4 that define it"""
  if not os.path.exists(cache):
    with open(cache, 'w') as o:
      for dp, _, fs in os.walk(root):
        for f in fs:
          if not f.endswith('Script.sml'): continue
          p = os.path.join(dp, f)
          try:
            text = open(p, errors='replace').read()
          except OSError:
            continue
          names = set()
          for r in DEFPAT:
            for m in r.finditer(text):
              n = m.group(1)
              names.add(n)
              names.add(re.sub(r'_def$|_DEF$|_rules$', '', n))
          for n in sorted(names):
            o.write('%s\t%s\t%s\n' % (n, f[:-10], p))
  out = collections.defaultdict(set)
  for l in open(cache):
    n, thy, p = l.rstrip('\n').split('\t')
    if '/src/' in p: out[n].add(thy)
  return out


def lib_names():
  """the constants that the files of ml/lib define: the library
     layer of the port, which a ported library theory is part of
     (ASCIInumbers has the w2s of HOL4's words theory, because the
     hand written words layer is loaded before it)"""
  names = set()
  for f in sorted(os.listdir(T + '../ml/lib')):
    if not f.endswith('.ml'): continue
    text = open(T + '../ml/lib/' + f).read()
    for m in re.finditer(r'(?:cake_define\w*|new_(?:recursive_)?'
                         r'definition)[^`]*`\s*\(?\s*'
                         r"([A-Za-z_][A-Za-z0-9_']*)", text):
      names.add(m.group(1))
    for m in re.finditer(r"let ([A-Za-z_][A-Za-z0-9_']*)_def\s*=",
                         text):
      names.add(m.group(1))
  return names


def main():
  db = dbmod.Db()
  idx = build_index(T + '../hol4-src', T + '../tmp/hol4defs.txt')
  import overrides
  have = (set(db.defs) | set(db.hl) | set(db.provided) |
          set(db.rename.values()) | set(overrides.NAME_MAP) |
          set(overrides.TYPE_MAP) | lib_names())
  cnt = collections.Counter()
  where = collections.defaultdict(set)
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml': continue
    for b in hol4.parse(path):
      if b.kind not in ('Theorem', 'Triviality'): continue
      body = hol4.strip_comments(b.body or '')
      # a name after a dot is a field of a record and no constant
      # (lab_to_targetProof's c'.labels), and a name that the
      # statement itself binds is a variable of it (bvi_to_data
      # quantifies over tail, and path has a constant of that name)
      bound = set()
      for m in re.finditer(u'[\u2200\u2203\u03bb!?\\\\]'
                           u"((?:\\s*[A-Za-z][A-Za-z0-9_']*)+)",
                           body):
        bound |= set(m.group(1).split())
      body = re.sub(r"\.\s*[A-Za-z][A-Za-z0-9_']*", '', body)
      for n in set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", body)):
        if n in have or n not in idx or n in bound: continue
        # a short lower case name is a variable of the statement
        if len(n) <= 3 and n.islower(): continue
        cnt[n] += 1
        where[n] |= idx[n]
  print('%d names of HOL4 libraries that the statements use and '
        'the port has not' % len(cnt))
  for n, c in cnt.most_common(40):
    print('%5d  %-22s %s' % (c, n, ' '.join(sorted(where[n]))[:40]))


if __name__ == '__main__':
  main()
