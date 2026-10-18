"""the summary of tmp/diag.out (tools/bin/diag writes it)

  python3 -I tools/diag.py

says how many statements of the port a session cannot read, by
the reason that HOL Light gives, and which files they are in.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'


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


def applied_hidden(rows_free, hid):
  """a free variable of a statement that has a function type and a
     name that the port hid (the hide list of the file, or the
     overloads of the record fields that cake_as_vars takes away):
     the statement applies a constant that the port made a
     variable, so it says something else than the source does"""
  out = []
  flds = field_overloads()
  for f, nm, vs in rows_free:
    for v in vs.split():
      n, _, ty = v.partition(':')
      if '->' not in ty: continue
      if n in hid.get(f, []):
        out.append((f, nm, n, 'hidden'))
      elif n in flds:
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
