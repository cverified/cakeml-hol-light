"""write the part of a changed ml/lib/define.ml that has to be
   loaded over the one of a session to try the change: everything
   from the top level phrase in which the first difference is to
   the end of the file (the strategies take the functions before
   them as they were when they were made, so the part that is
   loaded has to reach the end).

     python3 -I tools/tailpatch.py <changed define.ml> <out>
"""
import sys, os
C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
new = open(sys.argv[1]).read().split('\n')
old = open(C + '/ml/lib/define.ml').read().split('\n')
i = 0
while i < len(old) and i < len(new) and old[i] == new[i]: i += 1
if i >= len(new):
  print('no difference'); sys.exit(1)
j = i
while j > 0 and not (new[j].startswith('let ') or
                     new[j].startswith('(* ')):
  j -= 1
open(sys.argv[2], 'w').write('\n'.join(new[j:]) + '\n')
print('from line %d (the difference is at %d), %d lines'
      % (j + 1, i + 1, len(new) - j))
