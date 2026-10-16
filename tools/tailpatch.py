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
tail = new[j:]
# a table that the session has filled (the recursion theorems and the
# size functions of the types that are loaded) may not be made anew:
# the part that is loaded would reset it, and everything that uses it
# (a definition by cases, a measure) would then fail
for k,l in enumerate(tail):
  if l.startswith('let the_rec_thms = ref') or \
     l.startswith('let the_size_fns = ref'):
    tail[k] = '(* %s stays as it is *)' % l.split()[1]
open(sys.argv[2], 'w').write('\n'.join(tail) + '\n')
print('from line %d (the difference is at %d), %d lines'
      % (j + 1, i + 1, len(new) - j))
