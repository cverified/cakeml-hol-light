"""the summary of tmp/diag.out (tools/bin/diag writes it)

  python3 -I tools/diag.py

says how many statements of the port a session cannot read, by
the reason that HOL Light gives, and which files they are in.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import thmcheck


def kind(msg):
  msg = re.sub(r'\?[0-9]+', '?', msg)
  if 'overload resolution' in msg:
    return 'a name that resolves to more than one constant'
  if msg.startswith('Unparsed'):
    return 'the statement does not parse'
  m = re.match(r'typechecking error[^:]*:\s*(.*)', msg)
  if m:
    return 'types: ' + re.sub(r'\s+', ' ', m.group(1))[:56]
  return msg[:56]


def hidden_names():
  """the names that the files of the port hide, per file"""
  out = {}
  cur = None
  for l in open(T + '../tmp/stmts.txt'):
    if l.startswith('@@@HIDE\t'):
      cur = l.split('\t')[1].split()
    elif l.startswith('@@@HIDEC'):
      pass
    elif l.startswith('@@@'):
      out[l.split('\t')[1]] = cur or []
    elif cur is not None and not l.startswith('@@@'):
      pass
  return out


def field_overloads():
  """the names that overload the accessors of a record field"""
  try:
    return set(l.split('\t')[0].strip()
               for l in open(T + '../tmp/fieldovl.txt') if l.strip())
  except OSError:
    return set()


def reads_field(name, f, nm):
  """does the HOL4 source of this statement read the field of that
     name (s.name) or set it (with name := ...)?  Where it does
     not, the name is a variable of the source as well and no
     finding (the oracle of stack_allocProof's make_init_semantics
     is a variable that the statement applies to a number)"""
  import db as dbmod, hol4
  global _DB, _SRC
  try:
    _DB
  except NameError:
    _DB = dbmod.Db(); _SRC = {}
  thy = None
  for t, path, kind in dbmod.load_order():
    if _DB.mlpath_of(t) == f: thy = t; break
  if thy is None: return True
  if thy not in _SRC:
    out = {}
    for b in hol4.parse(_DB.thy_of_file[thy]):
      if b.kind in ('Theorem', 'Triviality', 'ThmValue') and b.name:
        out[b.name] = b.body or b.text or ''
    _SRC[thy] = out
  body = _SRC[thy].get(re.sub(r'\[.*', '', nm))
  if body is None: return True
  return bool(re.search(r'\.\s*' + re.escape(name) + r'\b', body) or
              re.search(r'\b' + re.escape(name) + r'\s*:=', body))


def applied_rows():
  """the variables that a statement applies to an argument, per
     statement (the APPLIED lines that tools/diag.ml writes)"""
  out = {}
  try:
    for l in open(T + '../tmp/diag.out'):
      f = l.rstrip('\n').split('\t')
      if len(f) >= 5 and f[0] == 'APPLIED':
        out[(f[1], f[3])] = set(f[4].split())
  except OSError:
    pass
  return out


def applied_hidden(rows_free, hid):
  """a free variable of a statement that the statement applies to
     an argument and whose name overloads the accessors of a
     record field, which cake_as_vars takes away where the
     statement uses the name of a field for a variable of its own:
     the statement reads a field through a name that the port made
     a variable, so it says something else than the source does.

     A name that the file hides is no finding: the port hides what
     no theory in the scope of the source defines and what the
     source hides itself (Parse.hide), and HOL4 reads a variable
     there as well (word_elimProof hides mem, and its
     FINITE_mdom_mem is about a variable mem of its own)."""
  out = []
  flds = field_overloads()
  app = applied_rows()
  for f, nm, vs in rows_free:
    for v in vs.split():
      n, _, ty = v.partition(':')
      if '->' not in ty: continue
      if n in hid.get(f, []) or n not in flds: continue
      if n not in app.get((f, nm), ()): continue
      if not reads_field(n, f, nm): continue
      out.append((f, nm, n, 'a field'))
  return out


def main():
  rows = []
  for l in open(T + '../tmp/diag.out'):
    f = l.rstrip('\n').split('\t')
    if len(f) >= 5 and f[0] in ('FAIL', 'BADTYPE'):
      rows.append((f[1], f[3], f[4]))
  print('%d statements that the session cannot read' % len(rows))
  for k, n in collections.Counter(kind(m) for _, _, m
                                  in rows).most_common(15):
    print('%6d  %s' % (n, k))
  free = []
  for l in open(T + '../tmp/diag.out'):
    f = l.rstrip('\n').split('\t')
    if len(f) >= 5 and f[0] == 'FREE':
      free.append((f[1], f[3], f[4]))
  bad = applied_hidden(free, hidden_names())
  print('%d statements that apply a name the port made a variable'
        % len(bad))
  for f, nm, n, why in bad[:10]:
    print('        %s %s: %s (%s)' % (f, nm, n, why))
  print('the files:')
  for f, n in collections.Counter(f for f, _, _
                                  in rows).most_common(10):
    print('%6d  %s' % (n, f))


if __name__ == '__main__':
  main()
