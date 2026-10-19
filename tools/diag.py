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
    if l.startswith('@@@HIDE'):
      cur = l.split('\t')[1].split()
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


def applied(name, f, nm):
  """does the statement nm of the file f apply this name to an
     argument?  A field of a record is a function, so a statement
     that has one for a variable of its own (wordProps' alloc of a
     state with clock := k has a variable compile_oracle) leaves a
     free variable of a function type behind that is no error"""
  try:
    sts = thmcheck.statements(T + '../ml/' + f)
  except OSError:
    try:
      sts = thmcheck.statements(f)
    except OSError:
      return True
  pat = re.compile(r'\b' + re.escape(name) + r'\s*[A-Za-z0-9_(]')
  for n2, line, stmt in sts:
    if n2 == nm: return bool(pat.search(stmt))
  return True


def applied_hidden(rows_free, hid):
  """a free variable of a statement that has a function type, that
     the statement applies to an argument, and that has a name the
     port hid (the hide list of the file, or the overloads of the
     record fields that cake_as_vars takes away): the statement
     applies a constant that the port made a variable, so it says
     something else than the source does"""
  out = []
  flds = field_overloads()
  for f, nm, vs in rows_free:
    for v in vs.split():
      n, _, ty = v.partition(':')
      if '->' not in ty: continue
      if n not in flds and n not in hid.get(f, []): continue
      if not applied(n, f, nm): continue
      out.append((f, nm, n, 'hidden' if n in hid.get(f, [])
                            else 'a field'))
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
