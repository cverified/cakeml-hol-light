"""check a proof file against the file of the port it is about

A section of proofs/<path>.prf is the tactic of a theorem of
ml/<path>.ml, and it may use what stands before that theorem in the
file and nothing after it (the port loads a file from the top).
This says which sections name a theorem the file does not have and
which use a binding of the file that comes later than they do.

  python3 tools/prfcheck.py [<path of the port, relative to ml/>]

With no path it checks every file of the store, which is what
tools/bin/checks does after a re-port.
"""

import re
import sys

T = __file__.rsplit('/', 1)[0] + '/'
sys.path.insert(0, T.rstrip('/') or '.')
import proofstore


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
  # the port puts the prove on the next line where the binding is
  # too long for one (tools/port.py: prove_head, tools/stmts.py)
  for m in re.finditer(r"^let ([A-Za-z_][A-Za-z_0-9']*) =\n?"
                       r"[ ]*prove$", ml, re.M):
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
    # the body stands where an argument stands (tools/landproof.py
    # wraps it in brackets of its own), so a tactic of several
    # steps has to be parenthesised: without the brackets
    # `a THEN b` reads as `(prove (`...`, a)) THEN b`
    # (PORTING-GUIDE.md, entry 30)
    text = re.sub(r'\(\*.*?\*\)', '', '\n'.join(body), flags=re.S)
    text = text.strip()
    if re.search(r'\bTHEN[L]?\b', text) and not (
        text.startswith('(') and text.endswith(')')):
      print('%s: the tactic needs brackets round it' % name)
      out += 1
    # the names the section binds itself (its helpers stand in a
    # `let ... in` of its own), which say nothing about what the
    # file binds; and the scan is over the text without the
    # comments, where a name may stand for what it says and not
    # for what the tactic uses
    mine = set()
    for m in re.finditer(r'\blet\s+(?:rec\s+)?\(?\s*'
                         r'([A-Za-z_][A-Za-z_0-9\']*'
                         r'(?:\s*,\s*[A-Za-z_][A-Za-z_0-9\']*)*)',
                         text):
      for w in m.group(1).split(','): mine.add(w.strip())
    for w in sorted(set(re.findall(r'[A-Za-z_][A-Za-z_0-9\']*',
                                   text))):
      if w in mine: continue
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
  paths = sys.argv[1:] or [proofstore.mlrel_of(f)
                           for f in proofstore.files()]
  sys.exit(1 if sum(check(p) for p in paths) else 0)
