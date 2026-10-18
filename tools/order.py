"""the blocks of a source and of its port are in the same order

  python3 -I tools/order.py [<theory>...]

The test of phase two is to read a HOL4 source and its port next
to each other: the same blocks in the same order (CLAUDE.md).
`tools/coverage.py` says which blocks are there; this says that
the ones that are there are in the order of the source.

Every item of a ported file says which line of the source it
comes from: a statement by its name (the Theorem of that name),
and a pointer by the lines that it points at.  Those lines have
to go up as the file goes on; a line that goes back is a block
that the port has in another place than the source has it.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4

ML = T + '../ml/'

# the blocks that the port has in another place than the source
# has them, and why.  The ML code of a source that the port has in
# OCaml takes the place of the whole run of blocks that it covers
# (overrides.ML_PORTED), so a block of the source inside that run
# that is not ML comes after it in the port.
MOVED = {
  # the ML of word_bignum that builds the deep embedding runs from
  # Skip_tm to mc_use_fac_def, and HOL4 states all_code_defs in the
  # middle of it (the port has a pointer at it after the OCaml)
  ('word_bignum', 403): 'inside the ML that the port has in OCaml',
  ('word_bignum', 414): 'inside the ML that the port has in OCaml',
}

# a statement of the port, and a pointer at the lines of a source
STMT = re.compile(r'cake_(?:theorem|alias)\s*\n?\s*"([^"\[]+)')
AT = re.compile(r'\(\* HOL4 (\S+\.sml):(\d+)')
COMMENT = re.compile(r'\(\*(?!\s*HOL4 \S+\.sml:)(.*?)\*\)', re.S)


def body(text):
  """the words of a comment, without its (* and *) and without the
     white space (as tools/comments.py reads one)"""
  return ' '.join(re.sub(r'^\s*\(\*+|\*+\)\s*$', '',
                         text.strip()).split())


def items(text):
  """what a ported file holds, in its order: the name of every
     statement, the line that every pointer points at and the body
     of every comment of its own"""
  out = []
  for m in re.finditer(r'%s|%s|%s'
                       % (STMT.pattern, AT.pattern, COMMENT.pattern),
                       text):
    if m.group(1) is not None:
      out.append(('name', m.group(1), m.start()))
    elif m.group(2) is not None:
      out.append(('line', int(m.group(3)), m.start()))
    else:
      out.append(('comment', body(m.group(4)), m.start()))
  return out


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  files = bad = 0
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml' or (want and thy not in want): continue
    try:
      text = open(ML + db.mlpath_of(thy)).read()
    except OSError:
      continue
    files += 1
    # the line of the source that every theorem of it is at (a
    # name that the source binds twice is at both, in order)
    at = {}
    cat = {}
    for b in hol4.parse(path):
      if b.kind in ('Theorem', 'Triviality', 'ThmValue') and b.name:
        at.setdefault(b.name, []).append(b.src or 0)
      elif b.kind == 'ML':
        for nm, _, _ in hol4.ml_theorems(b.text or ''):
          at.setdefault(nm, []).append(b.src or 0)
      elif b.kind == 'Comment':
        # a comment of the source is in the port in its place as
        # well, so it says which line the port is at too
        cat.setdefault(body(b.text), []).append(b.src or 0)
    used = {}
    last = 0
    first = None
    back = 0
    for kind2, v, pos in items(text):
      if kind2 in ('name', 'comment'):
        tab = at if kind2 == 'name' else cat
        k = used.get((kind2, v), 0)
        lines = tab.get(v)
        # a comment that the port writes itself is in no source
        if not lines: continue
        line = lines[min(k, len(lines) - 1)]
        used[(kind2, v)] = k + 1
      else:
        line = v
      if line < last:
        if (thy, line) in MOVED: continue
        back += 1
        if first is None:
          first = (v, line, last)
      last = max(last, line)
    if back:
      bad += 1
      print('%-34s %3d blocks before the one in front of them, '
            'first %s (line %d after line %d)'
            % (thy, back, first[0], first[1], first[2]))
  print('%d files, %d in which a block is out of the order of the '
        'source' % (files, bad))
  return bad


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
