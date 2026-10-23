"""check a proof file against the file of the port it is about

A section of proofs/<path>.prf is the tactic of a theorem of
ml/<path>.ml, and it may use what stands before that theorem in the
file and nothing after it (the port loads a file from the top).
This says which sections name a theorem the file does not have and
which use a binding of the file that comes later than they do.

  python3 tools/prfcheck.py <path of the port, relative to ml/>
"""

import re
import sys

T = __file__.rsplit('/', 1)[0] + '/'


def check(mlrel):
  ml = open(T + '../ml/' + mlrel, encoding='utf-8').read()
  prf = open(T + '../proofs/' + re.sub(r'\.ml$', '.prf', mlrel),
             encoding='utf-8').read()
  # the bindings of the file, in the order they are made
  at = {}
  for m in re.finditer(r'^let ([A-Za-z_][A-Za-z_0-9\']*)'
                       r'(?:,\s*\n?\s*([A-Za-z_][A-Za-z_0-9\']*))?'
                       r'\s*(?:,\s*\n?\s*'
                       r'([A-Za-z_][A-Za-z_0-9\']*))?\s*=',
                       ml, re.M):
    for g in m.groups():
      # a wildcard is no binding (the file has let _ = size_thms ...)
      if g and g != '_' and g not in at: at[g] = m.start()
  # and where each theorem of a name is stated
  thm = {}
  for m in re.finditer(r'cake_theorem[\s\n]*"([^"\[]*)(\[[^"]*\])?"',
                       ml):
    thm.setdefault(m.group(1), []).append(m.start())
  bad = 0
  name = None
  body = []

  def finish(name, body):
    out = 0
    if name is None: return 0
    m = re.match(r'^(.*?)(?:#(\d+))?$', name)
    nm, k = m.group(1), int(m.group(2) or 1)
    if nm not in thm:
      print('%s: no theorem of that name' % name); return 1
    if k > len(thm[nm]):
      print('%s: the file states it %d time(s)'
            % (name, len(thm[nm]))); return 1
    pos = thm[nm][k - 1]
    for w in sorted(set(re.findall(r'[A-Za-z_][A-Za-z_0-9\']*',
                                   '\n'.join(body)))):
      if w in at and at[w] > pos:
        print('%s: uses %s, which the file binds later' % (name, w))
        out += 1
    return out

  for line in prf.split('\n'):
    m = re.match(r'^###[ \t]+(\S+)[ \t]*$', line)
    if m:
      bad += finish(name, body)
      name, body = m.group(1), []
    elif name is not None:
      body.append(line)
  bad += finish(name, body)
  print('%s: %d section(s), %d problem(s)'
        % (mlrel, len(re.findall(r'^### ', prf, re.M)), bad))
  return bad


if __name__ == '__main__':
  sys.exit(1 if check(sys.argv[1]) else 0)
