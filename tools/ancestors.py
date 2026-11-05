"""every file of the port says which theories its source can see

  python3 -I tools/ancestors.py

A file of the port reads its statements with the overloads of the
theories out of the scope of its source taken out of the interface
(ml/lib/theorem.ml, hol4_ancestors; ISSUES.md "A statement that
means another theory's constant").  The line that says which those
are is written by tools/port.py out of the Ancestors blocks of the
source, and the one that puts the interface back stands at the end
of the file.  This says of every file of ml/ whether both are there
and whether the list is the one the source gives.
"""
import os, re, sys
T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod
C = T + '../'

ANC = re.compile(r'(?m)^let _ = hol4_ancestors "([A-Za-z0-9_\']+)"'
                 r'\s*(\[[^]]*\]);;')
BACK = re.compile(r'(?m)^let _ = unhide_overloads \(\);;')


def main():
  db = dbmod.Db()
  db.scan()
  bad = n = 0
  for thy, path, kind in dbmod.load_order():
    p = C + 'ml/' + db.mlpath_of(thy)
    if kind == 'lib':
      continue
    n += 1
    text = open(p).read()
    ms = ANC.findall(text)
    want = db.announce(thy)
    if len(ms) != 1:
      print('%s: %d hol4_ancestors lines' % (thy, len(ms)))
      bad += 1
      continue
    got_thy, lst = ms[0]
    got = re.findall(r'"([^"]+)"', lst)
    if got_thy != thy:
      print('%s: the line says "%s"' % (thy, got_thy))
      bad += 1
    elif got != want:
      print('%s: the line says %s and the source %s'
            % (thy, sorted(set(got) - set(want))[:4],
               sorted(set(want) - set(got))[:4]))
      bad += 1
    elif not BACK.search(text):
      print('%s: no unhide_overloads at the end of it' % thy)
      bad += 1
  print('%d files of CakeML sources, %d that do not say which '
        'theories their source can see' % (n, bad))


if __name__ == '__main__':
  main()
