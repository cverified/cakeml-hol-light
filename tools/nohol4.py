"""No HOL4 code in the port: a ground rule of CLAUDE.md.

The port says what the HOL4 sources say in HOL Light, and where it
cannot say it, it points at the lines of the source instead of
keeping them.  So no SML, no HOL4 tactic and no HOL4 quotation is
in ml/, in a comment or anywhere else.  What is allowed is the
port's own prose about what HOL4 does, and the pointers.

Two things are looked for:

  - a comment of ml/ whose body is HOL4 code (the same test that
    tools/port.py uses on the comments of a source: a comment that
    holds a block of one is code, and one that sketches a line or
    two of it in prose is a comment)
  - a line of ml/ outside a comment that starts with one of the
    keywords of a HOL4 script
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import port as portmod

ML = os.path.dirname(os.path.abspath(__file__)) + '/../ml/'

# the comment that the port writes where it cannot say what the
# source says: it points at the file and the lines of the source
POINTER = re.compile(r'\s*HOL4 \S+\.sml:\d')

# the symbols that HOL4 writes a term with and HOL Light has no
# parser for: a quotation of the port that has one in it is a term
# of HOL4 that the translation left as it stands
HOL4_SYMBOL = re.compile(u'[\u00ac\u2190-\u22ff\u27e8\u27e9'
                         u'\u2983\u2984\u00ab\u00bb\u27f0-\u27ff]')


# a line of a HOL4 script, which no line of the port can be
HOL4_LINE = re.compile(
  r"^\s*(Theory|Ancestors|Libs|Theorem|Triviality|Proof|QED|End|"
  r"Termination|Datatype|Definition|Inductive|CoInductive)\b")


def comments(text):
  """the comments of an OCaml file, as (line, body) pairs"""
  out = []
  i = depth = 0
  start = 0
  line = 1
  startline = 1
  while i < len(text):
    if text.startswith('(*', i):
      if not depth: start, startline = i + 2, line
      depth += 1
      i += 2
      continue
    if text.startswith('*)', i) and depth:
      depth -= 1
      if not depth: out.append((startline, text[start:i]))
      i += 2
      continue
    if text[i] == '\n': line += 1
    i += 1
  return out


def code_free(text):
  """the text with its comments taken out, line numbering kept.
     A comment of a source inside a term or a datatype
     specification is the comment of HOL Light there (// and to
     the end of the line), and is one of them"""
  out = []
  i = depth = 0
  while i < len(text):
    if text.startswith('(*', i): depth += 1; i += 2; continue
    if text.startswith('*)', i) and depth: depth -= 1; i += 2; continue
    if not depth and text.startswith('//', i):
      j = text.find('\n', i)
      if j < 0: j = len(text)
      # a comment of the port holds no backquote, so the first one
      # on the line is the quotation closing around the comment,
      # which is code and stays
      k = text.find('`', i)
      if 0 <= k < j: j = k
      out.append(' ' * (j - i)); i = j; continue
    out.append('\n' if text[i] == '\n' else
               (' ' if depth else text[i]))
    i += 1
  return ''.join(out)


# what the lines that a pointer points at have to look like, by
# what the pointer says is there
EXPECT = [
  ('the ML values', r'^\s*(val|fun|local)\b'),
  ('a proof', r'^\s*(Resume|Finalise)\b|^\s*(>>|>-|\\\\)|'
              r'\b(Cases_on|qexists_tac|qabbrev_tac|match_mp_tac|'
              r'metis_tac|rw|fs|gvs|simp|rfs|strip_tac)\s*[\[(`]'),
  # a pointer that says ML code may not point at a block that the
  # port is supposed to have ported
  ('ML code', r'^(?!\s*(Definition|Theorem|Datatype|Inductive|'
              r'Triviality|Type|Overload)\b)\s*\S'),
  ('code that the source has in a comment', r'^\s*\(\*'),
  ('a comment with ML code after it', r'^\s*\(\*'),
  ('the tactic that proves the termination',
   r'(Termination|WF_REL_TAC|tDefine|measure)'),
  ('the Termination', r'Termination'),
  ('an overload that the source brings to the front',
   r'bring_to_front_overload|bring_fwd_ctors'),
  ('the overload', r'^\s*Overload\b'),
  ('the type abbreviation', r'^\s*Type\b'),
  ('the definition', r'^\s*Definition\b'),
  # the value may be a Theorem block of the source or the ML of
  # one (val foo = Q.prove(...) |> SIMP_RULE ..., save_thm)
  ('a theorem that HOL4 states as the value of an ML expression',
   r'^\s*(Theorem|Triviality|val|fun|local)\b|save_thm'),
  ('a theorem whose statement the port cannot state yet',
   r'^\s*(Theorem|Triviality)\b'),
  # a statement that HOL Light's parser rejects (tools/unstated.py)
  ('a theorem whose statement HOL Light does not read',
   r'^\s*(Theorem|Triviality|val|fun|local)\b|save_thm'),
  ('the theorem', r'^\s*(Theorem|Triviality)\b'),
  ('the triviality', r'^\s*(Theorem|Triviality)\b'),
]

AT = re.compile(r'\s*HOL4 (\S+\.sml):(\d+)(?:-(\d+))?:\s*(.*)', re.S)


def pointers():
  """check that every pointer of the port points at lines of the
     HOL4 source that hold what it says they hold"""
  import db as dbmod
  src = {re.sub(r'^.*/', '', path): path
         for thy, path, kind in dbmod.load_order()}
  n = bad = 0
  for root, _, fs in os.walk(ML):
    for f in sorted(fs):
      if not f.endswith('.ml'): continue
      rel = os.path.relpath(os.path.join(root, f), ML)
      text = open(os.path.join(root, f)).read()
      for line, body in comments(text):
        m = AT.match(body)
        if not m: continue
        n += 1
        name, a, z, what = m.group(1), int(m.group(2)), m.group(3), \
                           ' '.join(m.group(4).split())
        z = int(z) if z else a
        path = src.get(name)
        if path is None:
          print('%s:%d: %s is not a source of the port' % (rel, line, name))
          bad += 1; continue
        lines = open(path).read().split('\n')
        if not 1 <= a <= z <= len(lines):
          print('%s:%d: %s has no lines %d-%d' % (rel, line, name, a, z))
          bad += 1; continue
        body = '\n'.join(lines[a-1:z])
        pat = next((p for k, p in EXPECT if what.startswith(k)), None)
        if pat is None:
          # a pointer whose text is the name of what it points at
          # ("mw2n_lt", or "mw2n_APPEND, where the port writes
          # dimword (:'a) EXP n for HOL4's dimwords n (:'a)"): the
          # test is that the name is on the lines it points at
          named = re.match(r"([A-Za-z_][A-Za-z0-9_']*)\b", what)
          if named and re.search(r'\b%s\b' % re.escape(named.group(1)),
                                 body):
            continue
          print('%s:%d: no test for %r' % (rel, line, what[:40]))
          bad += 1; continue
        if not re.search(pat, body, re.M):
          print('%s:%d: %s:%d-%d is not %r' % (rel, line, name, a, z,
                                               what[:40]))
          bad += 1
  print('%d pointers, %d that do not point at what they say' % (n, bad))
  return bad


def main():
  bad = 0
  files = 0
  for root, _, fs in os.walk(ML):
    for f in sorted(fs):
      if not f.endswith('.ml'): continue
      p = os.path.join(root, f)
      rel = os.path.relpath(p, ML)
      text = open(p).read()
      files += 1
      for line, body in comments(text):
        # a pointer at the lines of a HOL4 source is what the port
        # puts where it cannot say what the source says
        if POINTER.match(body): continue
        # the same test that tools/port.py uses on a comment of a
        # source: a comment with a block of one in it is code, and
        # one that sketches a line or two of it in prose is a
        # comment (the head comment of bvi_let documents the
        # transformation and sketches a Let of BVI in the prose)
        if portmod.commented_code(body):
          bad += 1
          m = portmod.COMMENTED_CODE.search(portmod.uncomment(body))
          print('%s:%d: HOL4 code in a comment: %r'
                % (rel, line, (m.group(0) if m else body)
                   .strip()[:40]))
      # a quotation of the port is a term of HOL Light, whose
      # parser is ASCII: a symbol of HOL4's in one is a term that
      # the translation left as it stands (the comments are out of
      # the way first, so a comment of a source that writes a
      # condition of HOL4 in prose is no error)
      code = code_free(text)
      for m in re.finditer(r'`([^`]*)`', code):
        m2 = HOL4_SYMBOL.search(m.group(1))
        if m2:
          bad += 1
          print('%s:%d: a symbol of HOL4 in a quotation: %r'
                % (rel, code[:m.start()].count('\n') + 1,
                   ' '.join(m.group(1).split())[:40]))
      for i, l in enumerate(code.split('\n')):
        m = HOL4_LINE.match(l)
        if m:
          bad += 1
          print('%s:%d: a line of a HOL4 script: %r'
                % (rel, i + 1, l.strip()[:40]))
  print('%d files, %d with HOL4 code in them' % (files, bad))
  return bad + pointers()


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
