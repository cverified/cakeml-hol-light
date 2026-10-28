#!/usr/bin/env python3
"""tools/parens.py [<file.prf>|<file.ml> ...]: the parenthesis
balance of every section of a proof store, or of every top-level
unit of a file of the port.

A section of proofs/<path>.prf is a tactic *expression*, which the
generator writes into `prove(<statement>, <section>);;`.  A section
that is one bracket short therefore makes a file that does not parse,
and what says so is a verify twelve minutes later.  This says it in a
second.

Comments and HOL quotations are stripped before counting, and a
string of OCaml is read as such, so a bracket inside one does not
count.  With no argument it checks every store of proofs/.

A file of ml/ is checked unit by unit instead: `let foo = ...;;`
up to the next one that starts a line.  That is what catches a
block of tools/overrides.py whose brackets the hand-editing of a
round got wrong -- the three checks all passed on such a block and
only a verify said `This expression has type term`."""

import re
import sys
import os

def strip(text):
  """the text with comments, quotations and strings taken out"""
  out = []
  i = 0
  n = len(text)
  depth = 0            # comment depth
  while i < n:
    if text.startswith('(*', i):
      depth += 1
      i += 2
    elif text.startswith('*)', i) and depth:
      depth -= 1
      i += 2
    elif depth:
      i += 1
    elif text[i] == '`':
      j = text.find('`', i + 1)
      i = n if j < 0 else j + 1
    elif text[i] == '"':
      j = i + 1
      while j < n and text[j] != '"':
        j += 2 if text[j] == '\\' else 1
      i = j + 1
    else:
      out.append(text[i])
      i += 1
  return ''.join(out)

def check(path):
  """the sections of one store that are not balanced"""
  bad = []
  name = None
  start = 0
  body = []
  lines = open(path).read().split('\n')
  def finish():
    if name is None:
      return
    t = strip('\n'.join(body))
    for (o, c, what) in [('(', ')', 'round'), ('[', ']', 'square')]:
      d = t.count(o) - t.count(c)
      if d:
        bad.append((start, name, what, d))
  for (k, line) in enumerate(lines, 1):
    if line.startswith('### '):
      finish()
      name = line[4:].strip()
      start = k
      body = []
    elif name is not None:
      body.append(line)
  finish()
  return bad

def check_ml(path):
  """the top-level units of a file of the port that are not
  balanced"""
  bad = []
  name = None
  start = 0
  body = []
  lines = open(path).read().split('\n')
  def finish():
    if name is None:
      return
    t = strip('\n'.join(body))
    for (o, c, what) in [('(', ')', 'round'), ('[', ']', 'square')]:
      d = t.count(o) - t.count(c)
      if d:
        bad.append((start, name, what, d))
  for (k, line) in enumerate(lines, 1):
    m = re.match(r'let (\w+)', line)
    if m:
      finish()
      name = m.group(1)
      start = k
      body = [line]
    elif name is not None:
      body.append(line)
  finish()
  return bad

def main(argv):
  files = argv[1:]
  if not files:
    for (root, _, names) in os.walk('proofs'):
      for nm in sorted(names):
        if nm.endswith('.prf'):
          files.append(os.path.join(root, nm))
  total = 0
  for path in sorted(files):
    these = check_ml(path) if path.endswith('.ml') else check(path)
    for (line, name, what, d) in these:
      sign = '+' if d > 0 else '-'
      print('%s:%d: %s: %s%d %s bracket(s)' %
            (path, line, name, sign, abs(d), what))
      total += 1
  print('%d section(s) out of balance' % total)
  return 1 if total else 0

if __name__ == '__main__':
  sys.exit(main(sys.argv))
