"""merge what a session says into a table of tools/

  python3 -I tools/mergetable.py <name> ...

`tools/bin/recargs` writes `tmp/<name>.new` out of a session that
has the port loaded.  A session in which a file did not load is
missing the constants of that file, so the new table is not the
whole of it: an entry that the session has wins, an entry that it
does not have stays as it was.  A refresh can then only put a
table right and never take from it.
"""
import sys, os

T = os.path.dirname(os.path.abspath(__file__)) + '/'


def main():
  for name in sys.argv[1:]:
    new = T + '../tmp/%s.new' % name
    old = T + '%s.txt' % name
    if not os.path.exists(new):
      print('%-10s no %s' % (name, new)); continue
    rows = {}
    for f in (old, new):
      if not os.path.exists(f): continue
      for l in open(f):
        if not l.strip(): continue
        rows[l.split('\t')[0]] = l.rstrip('\n')
    was = sum(1 for _ in open(old)) if os.path.exists(old) else 0
    with open(old, 'w') as f:
      for k in sorted(rows):
        f.write(rows[k] + '\n')
    print('%-10s %d -> %d' % (name, was, len(rows)))


if __name__ == '__main__':
  main()
