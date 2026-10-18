"""check that no name of a HOL4 definition is missing from its port

  python3 -I tools/fidelity.py [theory...]

For every definition block of a HOL4 source, this takes the names
of the constants that its term mentions, maps them through the
naming of the port, and reports the ones that do not occur in the
file of the port.  A missing name means that the port dropped a
part of the definition (a clause of a pattern match, say).
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, port as portmod, overrides

KINDS = ('Definition', 'Inductive', 'CoInductive')


def arities(text):
  """constructor -> number of arguments, from a datatype
     specification of HOL Light (a backslash at the end of a line
     is the continuation of the string)"""
  out = {}
  for part in text.replace('\\\n', ' ').split(';'):
    if '=' not in part: continue
    for alt in part.split('=', 1)[1].split('|'):
      alt = alt.strip()
      if not alt: continue
      m = re.match(r"([A-Za-z_][A-Za-z0-9_']*)(.*)$", alt, re.S)
      if not m: continue
      # every argument is one parenthesised group, and a type in
      # it may have parentheses of its own
      n = d = 0
      for ch in m.group(2):
        if ch == '(':
          if d == 0: n += 1
          d += 1
        elif ch == ')':
          d -= 1
      out[m.group(1)] = n
  return out

db = dbmod.Db()
thys = sys.argv[1:] or [t for t, _, _ in dbmod.load_order()]
tot = bad = 0
for thy in thys:
  path = db.thy_of_file.get(thy)
  if not path: continue
  p = portmod.Porter(db, thy)
  try:
    text = open(portmod.ML + db.mlpath_of(thy)).read()
  except Exception:
    continue
  db.base_grammar(thy)
  words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text))
  anc = db.ancestors(thy) | {thy}
  for b in hol4.parse(path):
    if b.kind == 'ML':
      for tok, prec, ass, _ in hol4.fixities(b.text):
        hterm.add_infix(tok, prec, ass)
      continue
    if b.kind == 'Datatype' and p.wanted(b):
      # the constructors of the port have the arguments of HOL4's
      spec = ''
      for m in re.finditer(r'define_datatype\s*\n?\s*'
                           r'("(?:[^"\\]|\\.)*")', text, re.S):
        spec += m.group(1)[1:-1] + ';'
      got = arities(spec)
      for ty, cons, flds in hol4.datatype_names(b.body):
        pass
      for part in hol4.split_top(hol4.strip_comments(b.body), ';'):
        if '=' not in part: continue
        rhs = part.split('=', 1)[1]
        if rhs.strip().startswith('<|'): continue
        for alt in hol4.split_top(rhs, '|'):
          alt = alt.strip()
          if not alt: continue
          w = alt.split()
          c = w[0]
          try:
            n = len(hterm.dtarg_texts(alt))
          except Exception:
            continue
          for nm in (p.nm_defined(c), c, p.const_name(c)):
            if nm in got:
              if got[nm] != n:
                print('%-22s %-20s %s: %d arguments, not %d'
                      % (thy, b.name or ty, nm, got[nm], n))
              break
      continue
    if b.kind not in KINDS or not p.wanted(b): continue
    # a definition that the port does not have (PENDING.md says
    # why) has none of its names
    if (thy, b.name) in overrides.NOT_YET: continue
    body = hol4.strip_comments(b.body)
    # the theory that a source writes before a constant
    # (stack_alloc$stub_names) is not a name to look for: it is
    # the name of a constant of another theory often enough
    body = re.sub(r"\b[A-Za-z][A-Za-z0-9_']*\$", ' ', body)
    # HOL4 writes a case expression that need not be exhaustive as
    # "pmatch <term> of ...", where pmatch is syntax and not the
    # constant of that name (infer's constrain_op)
    body = re.sub(r'\bpmatch\b(?=[^\n]*\bof\b)', ' ', body)
    miss = []
    for nm in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", body))):
      kinds = [k for t, k in db.defs.get(nm, [])
               if t in anc and k in ('con', 'def', 'rel')]
      if not kinds: continue
      # the port may write the name with the prefix of the theory
      # that defines the constant, or of a record type, and it
      # renames a bound variable of that name with a prime
      if any(w == nm or w == nm + "'" or w.endswith('_' + nm)
             for w in words):
        continue
      # an overload of HOL4 that the port expands is gone on purpose
      if any((t, nm) in db.overloads for t in anc): continue
      miss.append(nm)
    tot += 1
    if miss:
      bad += 1
      print('%-22s %-28s %s' % (thy, b.name, ' '.join(miss[:8])))
print('%d definitions, %d with a name missing' % (tot, bad))

# the records of the port have the fields of the HOL4 ones
port = {}
for dp, dn, fn in os.walk(portmod.ML):
  for f in fn:
    if not f.endswith('.ml'): continue
    src = open(os.path.join(dp, f)).read()
    for m in re.finditer(r'define_record "(\w+)"(.*?);;', src, re.S):
      port[m.group(1)] = re.findall(r'"([A-Za-z_][A-Za-z0-9_\']*)","',
                                    m.group(2))
nrec = rbad = 0
for (thy, ty), flds in sorted(db.recs.items()):
  if thys != [t for t, _, _ in dbmod.load_order()] and thy not in thys:
    continue
  nm = db.rename.get((thy, ty), ty)
  if nm not in port and thy + '_' + ty in port: nm = thy + '_' + ty
  nrec += 1
  if nm not in port:
    print('%-22s %-20s record not in the port' % (ty, thy)); rbad += 1
  elif sorted(port[nm]) != sorted(flds):
    print('%-22s %-20s fields %s' % (ty, thy,
                                     set(flds) ^ set(port[nm])))
    rbad += 1
print('%d records, %d that differ' % (nrec, rbad))
