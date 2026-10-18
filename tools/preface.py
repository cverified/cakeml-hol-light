"""write the preface of every file of the port

  python3 -I tools/preface.py

The preface is the comment at the head of a ported file: what the
file is and how it relates to the other files of the port.  It is
at most eight lines, the empty line after it counted, and it says

  - the theory and the HOL4 source it is ported from
  - whether it is a definition theory of CakeML, a proof theory
    (and of which file), or a HOL4 library theory of which the
    port has what CakeML needs
  - how many definitions, datatypes and theorems the source has
  - which files of the port need it, or how many

It is written after the port, because which files need a file is
only known when every file has its `needs` lines.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod, hol4, port as portmod

BANNER = '(* ======================================================== *)'


def needed_by(db):
  """for every file of the port, the files whose needs name it"""
  out = {}
  for thy, _, _ in dbmod.load_order():
    p = portmod.ML + db.mlpath_of(thy)
    try:
      text = open(p).read()
    except IOError:
      continue
    for m in re.finditer(r'needs "([^"]+)"', text):
      out.setdefault(m.group(1), set()).add(db.mlpath_of(thy))
  return out


def n_of(n, what):
  return '%s %s%s' % (n or 'no', what, '' if n == 1 else 's')


def base(path):
  return re.sub(r'^.*/', '', path)


def what_it_is(db, thy, kind, blocks):
  """the sentence that says what the file is"""
  if kind == 'lib':
    return ('A HOL4 library theory, of which the port has the '
            'definitions that CakeML needs.')
  cnt = {}
  for b in blocks:
    cnt[b.kind] = cnt.get(b.kind, 0) + 1
  defs = sum(cnt.get(k, 0)
             for k in ('Definition', 'Inductive', 'CoInductive'))
  thms = sum(cnt.get(k, 0)
             for k in ('Theorem', 'Triviality', 'ThmValue'))
  tys = cnt.get('Datatype', 0)
  about = re.sub(r'(Proof|Props)$', '', thy)
  out = ('A proof theory' if thy in portmod.PROOFTHYS
         else 'A definition theory')
  if (thy in portmod.PROOFTHYS and about != thy
      and about in db.thy_of_file):
    out += ' about ' + base(db.mlpath_of(about))
  cs = [n_of(defs, 'definition')]
  if tys: cs.append(n_of(tys, 'datatype'))
  cs.append(n_of(thms, 'theorem'))
  return out + ', with ' + ', '.join(cs[:-1]) + ' and ' + cs[-1] + '.'


def who_needs_it(dep):
  """the ways to say which files need it, the fullest first"""
  dep = sorted(base(d) for d in dep)
  if not dep:
    return ['No file of the port needs it.']
  if len(dep) == 1:
    return ['Needed by ' + dep[0] + '.']
  return ['Needed by ' + ', '.join(dep[:-1]) + ' and ' + dep[-1] + '.',
          'Needed by %s of the port.' % n_of(len(dep), 'file')]


def preface(db, thy, kind, path, blocks, dep):
  """the lines of the preface, the empty line after it included"""
  name = "(*  %s: ported from HOL4's" % thy
  src = re.sub(r'^.*/(cakeml-src|hol4-src)/', '', path)
  srclines = portmod.fill('    ' + src, [], 70) \
             if len('    ' + src) <= 70 else None
  if srclines is None:
    # a path too long for one line is broken at a directory
    srclines = []
    cur = '    '
    for part in src.split('/'):
      part += '' if part.endswith('.sml') else '/'
      if len(cur) + len(part) > 70 and cur.strip():
        srclines.append(cur); cur = '      '
      cur += part
    srclines.append(cur)
  what = what_it_is(db, thy, kind, blocks)
  room = 8 - 4 - len(srclines)
  for tail in who_needs_it(dep) + ['']:
    body = portmod.lay('    ', (what + ' ' + tail).split(), 68)
    if len(body) <= room:
      break
  return ([BANNER, name] + srclines + body[:-1] + [body[-1] + '  *)',
          BANNER, ''])


def main():
  db = dbmod.Db()
  rev = needed_by(db)
  n = long = 0
  for thy, path, kind in dbmod.load_order():
    p = portmod.ML + db.mlpath_of(thy)
    try:
      lines = open(p).read().split('\n')
    except IOError:
      continue
    # the head of the file is the two banners and what is between
    # them, and the empty line after it
    if lines[0] != BANNER:
      print('%s: no preface to replace' % base(p)); continue
    end = lines.index(BANNER, 1)
    while end + 1 < len(lines) and not lines[end + 1].strip():
      end += 1
    new = preface(db, thy, kind, path,
                  hol4.parse(path), rev.get(db.mlpath_of(thy), []))
    if len(new) > 8:
      print('%s: a preface of %d lines' % (base(p), len(new)))
    long += sum(1 for l in new if len(l) > 72)
    out = '\n'.join(new + lines[end + 1:])
    if out != '\n'.join(lines):
      open(p, 'w').write(out)
      n += 1
  print('%d prefaces written, %d lines over 72 characters' % (n, long))


if __name__ == '__main__':
  main()
