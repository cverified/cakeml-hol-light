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
  print('the files:')
  for f, n in collections.Counter(f for f, _, _
                                  in rows).most_common(10):
    print('%6d  %s' % (n, f))


if __name__ == '__main__':
  main()
