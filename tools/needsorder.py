"""the closure of the needs of a file, in the order of the load order

  python3 -I tools/needsorder.py <file of the port, relative to ml/>

A session that loads the files one after the other in this order has
them in the order a run has them, which is what the resolution of an
overloaded name depends on: a name that several theories of the port
define means in a file what the files before it have overloaded it
with, so a closure that `needs` builds by recursion -- which visits
the needs of a file in the order they stand in it, and so puts a
file of the order after one that stands before it -- reads a clause
of the port differently from a run.  The load order (tools/load.txt,
which tools/loadorder.py writes) is the one a run has; the closure
of a file in that order is a subsequence of it, and every file of it
has its own needs before it, so `needs` never recurses.

The file itself is not in the output: a test bed holds the closure
and the file is loaded into a clone of it.
"""
import os
import re
import sys

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'


def needs_of(rel):
  """the needs lines of a file of the port"""
  return re.findall(r'needs "([^"]*)";;', open(ML + rel).read())


def closure(rel):
  """every file that loading rel loads, rel itself left out"""
  seen = set()
  todo = list(needs_of(rel))
  while todo:
    f = todo.pop()
    if f in seen: continue
    seen.add(f)
    todo += needs_of(f)
  return seen


def positions(cl):
  """the place of every file of the closure in the load order

     A file that the load order does not name (lib/mc_tailrec.ml,
     which only lib/mc_multiword.ml needs) takes the place of the
     first file that needs it, a little before it."""
  order = [l.strip() for l in open(T + 'load.txt') if l.strip()]
  pos = dict((f, float(i)) for i, f in enumerate(order))
  rest = [f for f in cl if f not in pos]
  while rest:
    left = []
    for f in rest:
      users = [pos[g] for g in cl if f in needs_of(g) and g in pos]
      if users: pos[f] = min(users) - 0.5
      else: left.append(f)
    if len(left) == len(rest):
      for f in left: pos[f] = len(order) + 1.0
      break
    rest = left
  return pos


def main():
  rel = sys.argv[1]
  if rel.startswith(ML): rel = rel[len(ML):]
  cl = closure(rel)
  pos = positions(cl)
  for f in sorted(cl, key=lambda f: pos[f]):
    print('needs "%s";;' % f)


if __name__ == '__main__':
  main()
