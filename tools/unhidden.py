"""the constants a file of the port hides from the parser

A file that reads a name of its own as a variable hides the
constant of that name while it loads and unhides it at the end
(`do_list hide_constant [...]`).  A file that dies never reaches
that end, so the name stays hidden and every file after it reads
it as a variable too -- which is how one broken file turns into
several.  A run undoes it, and this says what to undo: HOL Light
keeps no list of what is hidden, but the file says what it hid.
"""
import re, sys

ns = []
for p in sys.argv[1:]:
  try: s = open(p, encoding='utf-8').read()
  except OSError: continue
  for m in re.finditer(r'hide_constant\s*\[([^]]*)\]', s):
    ns += re.findall(r'"([^"]+)"', m.group(1))
if ns:
  print('do_list unhide_constant [%s];;'
        % '; '.join('"%s"' % n for n in sorted(set(ns))))
