"""the first error of the output of loading one file of the port:
   the toplevel prints the exception and then one line
   'Error in included file F' for every file of the chain, innermost
   first, so an error whose innermost file is not this one belongs to
   a file that this one needs and was reported when that file was
   checked"""
import sys, re

path = sys.argv[1]
lines = sys.stdin.read().split('\n')
start = re.compile(r'^(cake_define [A-Za-z_0-9]* failed|Exception|'
                   r'Error|Warning [0-9])')
i = 0
n = len(lines)
while i < n:
  if start.match(lines[i]):
    msg = [lines[i]]
    # the toplevel may break a long exception over lines
    j = i + 1
    while j < n and lines[j].startswith(' ') and lines[j].strip():
      msg.append(lines[j].strip()); j += 1
    # the first 'Error in included file' after it says which file
    k = j
    inner = None
    while k < n and not start.match(lines[k]):
      m = re.match(r'Error in included file (.*)$', lines[k])
      if m:
        inner = m.group(1).strip(); break
      k += 1
    if inner is None or inner == path:
      print(' '.join(msg))
      sys.exit(0)
    i = j
  else:
    i += 1
