"""the proofs of phase three, which the port splices in

The port generates ml/, so a proof that is written into a file
there is thrown away by the next re-port.  A proof lives in
proofs/ instead, in the file that mirrors the one of the port:
the proofs of ml/<path>.ml are the sections of
proofs/<path>.prf, where a line

  ### <name>

names a theorem of the HOL4 source and the lines under it are the
tactic, as the port is to write it (indented by two spaces, with
no `;;` at the end).  A name that the file does not have keeps
its CHEAT_TAC, so a proof can be added one at a time.
"""

import os
import re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
PROOFS = T + '../proofs/'


def path_of(mlrel):
  """the file that holds the proofs of a file of the port"""
  return PROOFS + re.sub(r'\.ml$', '.prf', mlrel)


def load(mlrel):
  """the proofs of a file of the port, by the name that HOL4 gives
     the theorem"""
  p = path_of(mlrel)
  if not os.path.exists(p): return {}
  out = {}
  name = None
  body = []
  for line in open(p, encoding='utf-8').read().split('\n'):
    m = re.match(r'^###[ \t]+(\S+)[ \t]*$', line)
    if m:
      if name is not None: out[name] = '\n'.join(body).strip('\n')
      name = m.group(1)
      body = []
    elif name is not None:
      body.append(line)
  if name is not None: out[name] = '\n'.join(body).strip('\n')
  return {k: v for k, v in out.items() if v.strip()}


def files():
  """the proof files there are, as paths relative to proofs/"""
  out = []
  for dp, ds, fs in os.walk(PROOFS):
    for f in fs:
      if f.endswith('.prf'):
        out.append(os.path.relpath(os.path.join(dp, f), PROOFS))
  return sorted(out)


def mlrel_of(prfrel):
  """the file of the port that a proof file is about"""
  return re.sub(r'\.prf$', '.ml', prfrel)
