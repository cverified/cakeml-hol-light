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
        m = portmod.COMMENTED_CODE.search(body)
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
  return bad


if __name__ == '__main__':
  sys.exit(1 if main() else 0)
