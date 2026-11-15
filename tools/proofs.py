"""the proofs of phase three: what there is and whether it fits

Every section of a file of proofs/ has to name a theorem that the
port of the file it is about states, and no line of a proof may be
longer than 72 characters (the rule of ml/, which is where the
proof ends up).  The check is the one that a re-port cannot make:
a proof of a theorem that the source no longer has is dropped
without a word.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proofstore, stmts

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'


def stated(mlrel):
  """the bindings of the theorems that a file of the port states,
     which is what a section of the proof store names one by, and
     the other bindings of the file: a name that the file binds to
     the value of an expression (tools/derive.py computes what
     HOL4 states as the value of one) has nowhere for a tactic to
     go, which is no error of the store"""
  p = ML + mlrel
  if not os.path.exists(p): return None
  s = open(p, encoding='utf-8').read()
  thms = set(b for b, _, _, _, _ in stmts.theorems(s))
  other = set(re.findall(r"(?m)^let ([A-Za-z_][A-Za-z_0-9']*)\s*=",
                         s)) - thms
  return thms, other


def main():
  files = proofstore.files()
  n = 0
  bad = []
  derived = []
  long = []
  nofile = []
  for f in files:
    ml = proofstore.mlrel_of(f)
    pr = proofstore.load(ml)
    n += len(pr)
    got = stated(ml)
    if got is None:
      nofile.append(f)
      continue
    have, other = got
    for nm, tac in sorted(pr.items()):
      # a section may name the k-th theorem of a name, where the
      # source states two of one name (HOL4's allow_rebind)
      base = nm.split('#')[0]
      if base not in have:
        (derived if base in other else bad).append('%s: %s' % (f, nm))
      for i, l in enumerate(tac.split('\n')):
        if len(l) > 72: long.append('%s: %s line %d' % (f, nm, i + 1))
  for x in nofile: print('no file of the port for %s' % x)
  for x in derived:
    print('the file derives it, so the section is unused: %s' % x)
  for x in bad: print('names no theorem that the port states: %s' % x)
  for x in long: print('line over 72 characters: %s' % x)
  print('%d proofs in %d files of proofs/' % (n, len(files)))
  print('%d that name no theorem of the port, %d lines over 72'
        % (len(bad), len(long)))


if __name__ == '__main__':
  main()
