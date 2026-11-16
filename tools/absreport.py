"""the report of an abstract that loaded the whole port in one go

  python3 -I tools/absreport.py <the output of the session>

tools/bin/abstract loads the files one at a time and reads the
first error of each out of the pane (tools/cserr.py).  A driver
(tools/mkdriver.py) loads them all in one `loadt', which is a
quarter faster, and says which file it is starting (CAKEFILE).
This reads the same report out of that: one line per file that
failed, as `<file>: <the message>'.

The toplevel breaks a long exception over the lines of the pane,
so the continuation lines are joined as cserr.py joins them.  Only
the first failure of a file is reported, because the phrases after
a failing one do not load.
"""
import sys, re

START = re.compile(r'^(cake_define [A-Za-z_0-9]* failed|Exception|'
                   r'Error in included file|Error|Warning [0-9])')


def main():
  src = open(sys.argv[1], encoding='utf-8', errors='replace') \
        if sys.argv[1:] else sys.stdin
  lines = [l.rstrip('\n') for l in src]
  n = len(lines)
  cur = None
  done = set()
  i = 0
  while i < n:
    m = re.match(r'CAKEFILE (.*)$', lines[i])
    if m:
      cur = m.group(1).strip(); i += 1; continue
    if START.match(lines[i]) and cur and cur not in done:
      # 'Error in included file' alone is the toplevel saying that
      # the file stopped; the exception before it is the message
      if lines[i].startswith('Error in included file'):
        i += 1; continue
      msg = [lines[i]]
      j = i + 1
      while (j < n and lines[j].strip() and j - i < 6
             and not START.match(lines[j])
             and not lines[j].startswith('CAKEFILE')):
        msg.append(lines[j].strip()); j += 1
      print('%s: %s' % (cur, ' '.join(msg)))
      done.add(cur)
      i = j; continue
    i += 1
  return 0


if __name__ == '__main__':
  sys.exit(main())
