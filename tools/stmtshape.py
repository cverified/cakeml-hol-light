"""a statement of the port has the shape of the source's

  python3 -I tools/stmtshape.py [<theory>...]

A statement of phase two may not be weaker than the one of the
source (CLAUDE.md, and the rules of a formalization).  tools/
stmtnames.py says that no constant of a statement is lost; this
counts the connectives of the statement of the source and of the
one that the port has for it, and says where they differ: a
hypothesis or a conjunct that fell away is a difference of the
count, and so is one that the port added.

A difference is not always a fault -- HOL4 writes some things with
a connective where the port writes it without one (a case
expression that the port expands, an equation of booleans that
HOL4 writes with <=>, a pattern that binds a variable) -- so this
prints the statements to read, not errors.
"""
import sys, os, re, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, hol4, thmcheck

ML = T + '../ml/'


def reviewed():
  """the statements of tools/shapeok.txt: the ones whose counts
     differ and that a reading has found right"""
  out = set()
  for l in open(T + 'shapeok.txt'):
    if l.startswith('#') or not l.strip() or l.startswith(' '):
      continue
    out.add(l.split()[0])
  return out

# the connectives, as HOL4 writes them and as the port does
OPS = [
  ('!', [u'∀', '!'], ['!']),
  ('?', [u'∃', '?'], ['?']),
  ('==>', [u'⇒', '==>'], ['==>']),
  ('/\\', [u'∧', '/\\'], ['/\\']),
  ('\\/', [u'∨', '\\/'], ['\\/']),
  # HOL4's x <> y is the port's ~(x = y) and its x NOTIN s is
  # ~(x IN s), so an inequality and a non-membership of the
  # source count as a negation
  # HOL4's $~ is the negation as a function, which the port
  # writes as (~) or, of a number, as (--)
  ('~', [u'¬', '~', u'≠', '<>', u'∉', 'NOTIN'],
   ['~', '(--)']),
  # the complement of a word: HOL4 writes ~0w for the word of
  # all ones, which the port writes as word_not (n2w 0), and
  # the library layer's name for HOL4's word_1comp is the
  # same word_not
  ('word_not', ['word_not', 'word_1comp'],
   ['word_not', 'word_1comp']),
]


# the symbols of HOL4 that have a connective in them and are not
# one: the function relation of its transfer library (|==> and
# ===>), which the port writes as FUN_REL, the ~> of its PEG
# library (the ignoreL of two expressions) and the !! and ?? of
# its words theory (the or and the xor of two words)
NOT_OPS = ['|==>', '===>', '~>', '<~', '!!', '??']


# a character or a string of a source can have a connective in it
# (mlint's statements are about the character #"~")
LIT = re.compile(u'#?"(?:[^"\\\\]|\\\\.)*"|\u00ab[^\u00bb]*\u00bb')


def count(text, toks):
  """how often one of the tokens is in the text, the longest
     match first so that ==> is not two tokens, and a symbol that
     has one in it is not one"""
  n = 0
  i = 0
  while i < len(text):
    for t in NOT_OPS:
      if text.startswith(t, i):
        i += len(t)
        break
    else:
      for t in sorted(toks, key=len, reverse=True):
        if text.startswith(t, i):
          n += 1
          i += len(t)
          break
      else:
        i += 1
  return n


def shape(text, which):
  return tuple(count(text, pats[which]) for _, _, pats in
               [(a, b, (b, c)) for a, b, c in OPS])


def main():
  want = set(sys.argv[1:])
  db = dbmod.Db()
  ok = reviewed()
  n = bad = 0
  rows = []
  for thy, path, kind in dbmod.load_order():
    if kind != 'cakeml' or (want and thy not in want): continue
    try:
      text = open(ML + db.mlpath_of(thy)).read()
    except OSError:
      continue
    got = collections.defaultdict(list)
    for nm, line, stmt in thmcheck.scan(text):
      k = nm.find('[')
      got[nm[:k] if k >= 0 else nm].append((line, stmt))
    for b in hol4.parse(path):
      if b.kind not in ('Theorem', 'Triviality'): continue
      if not b.name or not got.get(b.name): continue
      line, mine = got[b.name].pop(0)
      mine = LIT.sub('', mine)
      # a statement of a source can have a comment in it, with a
      # hypothesis of its own in that comment (bvi_tailrecProof's
      # code_rel_union), which the port cannot keep: HOL Light has
      # no comment inside a quotation
      src = LIT.sub('', hol4.strip_comments(
        dbmod.strip_quote(b.body or '')))
      # a statement that antiquotes a term that the ML code of the
      # source builds is written out by the port, so it has the
      # connectives of that term and the source has none of them
      if '^' in src: continue
      # HOL4 writes the negation of a number and the complement of
      # a word with the ~ of a formula as well (~&n of mlint and
      # the ~0w of word_inst), which the port writes as -- and as
      # word_not: a ~ in front of a numeral is not a negation
      src = re.sub(r'~\s*(?=(0x[0-9A-Fa-f]+|[0-9]+)w\b)',
                   ' word_not ', src)
      src = re.sub(r'~\s*(?=[&0-9])', '', src)
      n += 1
      a = shape(src, 0)
      z = shape(mine, 1)
      if a != z:
        if '%s$%s' % (thy, b.name) in ok: continue
        bad += 1
        rows.append((thy, b.name, line,
                     [(o, x, y) for (o, _, _), x, y in zip(OPS, a, z)
                      if x != y]))
  for thy, nm, line, diff in rows:
    print('%s$%s (line %d): %s' % (
      thy, nm, line,
      ', '.join('%s %d in the source and %d in the port'
                % (o, x, y) for o, x, y in diff)))
  print('%d statements of the port, %d that count the connectives '
        'of the source differently and that tools/shapeok.txt does '
        'not account for' % (n, bad))
  return bad


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
