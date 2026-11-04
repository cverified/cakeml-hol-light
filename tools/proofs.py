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
     which is what a section of the proof store names one by"""
  p = ML + mlrel
  if not os.path.exists(p): return None
  s = open(p, encoding='utf-8').read()
  return set(b for b, _, _, _, _ in stmts.theorems(s))


def main():
  files = proofstore.files()
  n = 0
  bad = []
  long = []
  nofile = []
  for f in files:
    ml = proofstore.mlrel_of(f)
    pr = proofstore.load(ml)
    n += len(pr)
    have = stated(ml)
    if have is None:
      nofile.append(f)
      continue
    for nm, tac in sorted(pr.items()):
      if nm not in have: bad.append('%s: %s' % (f, nm))
      for i, l in enumerate(tac.split('\n')):
        if len(l) > 72: long.append('%s: %s line %d' % (f, nm, i + 1))
  for x in nofile: print('no file of the port for %s' % x)
  for x in bad: print('names no theorem that the port states: %s' % x)
  for x in long: print('line over 72 characters: %s' % x)
  print('%d proofs in %d files of proofs/' % (n, len(files)))
  print('%d that name no theorem of the port, %d lines over 72'
        % (len(bad), len(long)))


if __name__ == '__main__':
  main()
