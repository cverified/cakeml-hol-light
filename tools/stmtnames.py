"""every constant of a statement of a source is in its port

  python3 -I tools/stmtnames.py [<theory>...]

Phase two states every theorem of a CakeML source.  A statement
that lost a constant on the way says something else than the
source's does -- a free variable where HOL4 has a constant is the
silent deviation to look for (`exp1_size` was one, and the names
of HOL4 libraries that `tools/libnames.py` reports are others).

For every theorem whose statement the port has, this takes the
names of the constants of the HOL4 statement, maps them through
the naming of the port, and reports the ones that its statement
does not mention.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import hol4, hterm, db as dbmod, port as portmod, overrides

STR = re.compile(r'"((?:[^"\\]|\\.)*)"')


def statements(text):
  """name -> the statements that the port has for it (a source may
     state a theorem of the same name twice, which HOL4 allows
     with allow_rebind)"""
  out = {}
  for m in re.finditer(r'\bcake_theorem\b', text):
    s = STR.search(text, m.end())
    if not s or text[m.end():s.start()].strip(): continue
    i = text.find('`', s.end())
    j = text.find('`', i + 1) if i >= 0 else -1
    if j < 0: continue
    out.setdefault(re.sub(r'\[.*', '', s.group(1)),
                   []).append(text[i + 1:j])
  return out


def main():
  db = dbmod.Db()
  want = set(sys.argv[1:])
  tot = bad = 0
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml' or (want and thy not in want): continue
    p = portmod.Porter(db, thy)
    try:
      text = open(portmod.ML + db.mlpath_of(thy)).read()
    except OSError:
      continue
    db.base_grammar(thy)
    stmts = statements(text)
    anc = db.ancestors(thy) | {thy}
    for b in hol4.parse(path):
      if b.kind == 'ML':
        for tok, prec, ass, _ in hol4.fixities(b.text):
          hterm.add_infix(tok, prec, ass)
        continue
      if b.kind not in ('Theorem', 'Triviality') or not b.name:
        continue
      got = stmts.get(b.name)
      if not got: continue          # a pointer says where it is
      tot += 1
      body = hol4.strip_comments(b.body or '')
      body = re.sub(r"\b[A-Za-z][A-Za-z0-9_']*\$", ' ', body)
      body = re.sub(r'\bpmatch\b(?=[^\n]*\bof\b)', ' ', body)
      words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*",
                             ' '.join(got)))
      miss = []
      for nm in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*",
                                      body))):
        kinds = [k for t, k in db.defs.get(nm, [])
                 if t in anc and k in ('con', 'def', 'rel')]
        if not kinds: continue
        # the port may write the name with the prefix of the
        # theory or of a record type in front of it, the accessor
        # of a field as an update (state_stack_size_fupd), and a
        # bound variable of that name with a prime
        pat = re.compile(r"(^|_)%s('|_fupd)?$" % re.escape(nm))
        if any(pat.search(w) for w in words):
          continue
        # an overload of HOL4 that the port expands is gone on
        # purpose, and so is a name that the port writes as the
        # term of an overload of its own
        if any((t, nm) in db.overloads for t in anc): continue
        # a record literal of a source names its fields and the
        # port writes the values in the order of the record, so
        # the name of a field is not in its statement
        if ('mk_' in got[0] and
            any(nm in flds for (t, ty), flds in db.recs.items()
                if t in anc)):
          continue
        miss.append(nm)
      if miss:
        bad += 1
        if bad <= 15:
          print('%-22s %-28s %s' % (thy, b.name, ' '.join(miss[:6])))
  print('%d statements, %d that lost a constant of the source'
        % (tot, bad))


if __name__ == '__main__':
  main()
