"""No HOL4 code in the port: a ground rule of CLAUDE.md.

The port says what the HOL4 sources say in HOL Light, and where it
cannot say it, it points at the lines of the source instead of
keeping them.  So no SML, no HOL4 tactic and no HOL4 quotation is
in ml/, in a comment or anywhere else.  What is allowed is the
port's own prose about what HOL4 does, and the pointers.

Two things are looked for:

  - a comment of ml/ whose body is HOL4 code (the same test that
    tools/port.py uses on the comments of a source)
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
  """the text with its comments taken out, line numbering kept"""
  out = []
  i = depth = 0
  while i < len(text):
    if text.startswith('(*', i): depth += 1; i += 2; continue
    if text.startswith('*)', i) and depth: depth -= 1; i += 2; continue
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
  ('the overload', r'^\s*Overload\b'),
  ('the type abbreviation', r'^\s*Type\b'),
  ('the definition', r'^\s*Definition\b'),
  # the value may be a Theorem block of the source or the ML of
  # one (val foo = Q.prove(...) |> SIMP_RULE ..., save_thm)
  ('a theorem that HOL4 states as the value of an ML expression',
   r'^\s*(Theorem|Triviality|val|fun|local)\b|save_thm'),
  ('a theorem whose statement the port cannot state yet',
   r'^\s*(Theorem|Triviality)\b'),
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
        m = portmod.COMMENTED_CODE.search(portmod.uncomment(body))
        if m:
          bad += 1
          print('%s:%d: HOL4 code in a comment: %r'
                % (rel, line, m.group(0).strip()[:40]))
      for i, l in enumerate(code_free(text).split('\n')):
        m = HOL4_LINE.match(l)
        if m:
          bad += 1
          print('%s:%d: a line of a HOL4 script: %r'
                % (rel, i + 1, l.strip()[:40]))
  print('%d files, %d with HOL4 code in them' % (files, bad))
  return bad + pointers()


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
