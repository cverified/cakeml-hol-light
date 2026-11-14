"""the theorems that a file of the port states

A theorem of the port is what HOL Light writes, with the name of
the source and the attributes of HOL4 in a comment over it where
they are not the binding itself (tools/port.py):

    (* foo[simp] *)
    let bar = prove
     (`...`,
      tac);;

and a theorem that a source states as the value of another one
(HOL4's Theorem foo = bar) is a binding of that other theorem:

    let bar = baz;;

HOL4's [simp] is the one attribute that the port does act on: it
is a call after the theorem (`add_simp bar;;`), not a comment, and
this gives it back as an attribute all the same.

so this reads a file of the port and gives, of every theorem, the
binding, the name of the source, the attributes, the line and the
statement.  The checks that look for a statement ask here, which
is the one place that knows the shape: they used to look for
`cake_theorem`, the wrapper of the library that phase two had and
that a plain `prove` took the place of -- and then said that the
port has no statement at all (0 of them), which no check can
fail.
"""
import re

# a binding of the port, with the prove on the next line where the
# name is too long for one (tools/port.py: prove_head)
HEAD = re.compile(r"(?m)^let ([A-Za-z_][A-Za-z_0-9']*) =\n?"
                  r"[ ]*prove$")

# the binding of another theorem that an alias is
ALIAS = re.compile(r"(?m)^let ([A-Za-z_][A-Za-z_0-9']*) =\n?"
                   r"[ ]*([A-Za-z_][A-Za-z_0-9']*);;$")

# the comment that says the name of the source and the attributes:
# the name stands there where the binding is not that name, the
# attributes where the theorem has any, and nothing else is on the
# line
NOTE = re.compile(r"^\(\* ([A-Za-z_][A-Za-z_0-9']*)?"
                  r"(\[[A-Za-z_,]*\])? \*\)$")


# the call that puts a theorem in the simp set, which the port
# writes right after it where HOL4 writes [simp] over it
SIMP = re.compile(r"(?m)^add_simp ([A-Za-z_][A-Za-z_0-9']*);;$")


def simped(text):
  """the bindings of a file of the port that are in the simp set"""
  return set(SIMP.findall(text))


def strip_dslash(text):
  """the text without the comments of a term of the port, which
     stand after // and run to the end of the line"""
  return re.sub(r'(?m)^(\s*`?)//[^`\n]*', r'\1', text)


def note_of(text, start):
  """the name of the source and the attributes of the theorem that
     the binding at that offset is, out of the comments that stand
     right over it -- the port writes the note first and the one
     that says that the statement is read with the names of the
     fields as variables after it, so the note is the last line of
     the comments over the binding that has nothing else on it.

     The block ends at a blank line or at the end of the phrase
     before it: a pointer at the source may stand between two
     theorems with no blank line after the `;;`, and a scan that
     runs past it takes the note of the theorem before (which
     made two statements of dataProps and of pegComplete carry
     the name of the one over them)"""
  lines = text[:start].split('\n')[:-1]
  i = len(lines)
  while i > 0 and lines[i - 1].strip() and \
        not lines[i - 1].rstrip().endswith(';;'):
    i -= 1
  for l in reversed(lines[i:]):
    m = NOTE.match(l)
    if m:
      at = m.group(2)
      return m.group(1), ([a for a in at[1:-1].split(',') if a]
                          if at else [])
  return None, None


def theorems(text):
  """every theorem of a file of the port, in the order of the file:
     the binding, the name of the source, the attributes, the line
     and the statement"""
  out = []
  sp = simped(text)
  for m in HEAD.finditer(text):
    bind = m.group(1)
    i = text.find('`', m.end())
    if i < 0: continue
    j = text.find('`', i + 1)
    if j < 0: continue
    nm, at = note_of(text, m.start())
    at = (at or []) + (['simp'] if bind in sp else [])
    out.append((bind, nm or bind, at,
                text[:m.start()].count('\n') + 1,
                strip_dslash(text[i + 1:j])))
  return out


def aliases(text):
  """every theorem that the port states as the binding of another
     one: the binding, the name of the source, the attributes and
     the line"""
  out = []
  sp = simped(text)
  for m in ALIAS.finditer(text):
    nm, at = note_of(text, m.start())
    at = (at or []) + (['simp'] if m.group(1) in sp else [])
    out.append((m.group(1), nm or m.group(1), at,
                text[:m.start()].count('\n') + 1, m.group(2)))
  return out
