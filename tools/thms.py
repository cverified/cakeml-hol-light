"""the report of the theorems of phase two

  python3 -I tools/thms.py

reads tmp/unstated.txt (which tools/bin/thms writes from a session
of a run) and says how many theorems of the sources the port
states, and of the ones it does not, what the reason is.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'


def kind(msg):
  """the kind of a statement that the port cannot state"""
  if 'overload resolution' in msg:
    return 'a name that resolves to more than one constant'
  if msg.startswith('Unparsed'):
    return 'the port does not parse the statement'
  if 'not a formula' in msg:
    return 'the statement is not a formula (a name is missing)'
  m = re.match(r'typechecking error[^:]*:\s*(.*)', msg)
  if m:
    s = m.group(1)
    s = re.sub(r'\s+', ' ', s)
    return 'types: ' + s[:60]
  return msg[:60]


def main():
  rows = []
  try:
    for l in open(T + '../tmp/unstated.txt'):
      if '\t' in l:
        nm, msg = l.rstrip('\n').split('\t', 1)
        rows.append((nm, msg))
  except IOError:
    print('no tmp/unstated.txt: run tools/bin/thms first')
    return
  cnt = collections.Counter(kind(m) for _, m in rows)
  print('%d statements that the port cannot state yet' % len(rows))
  for k, n in cnt.most_common(20):
    print('%6d  %s' % (n, k))


if __name__ == '__main__':
  main()
