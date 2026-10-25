"""the OCaml identifiers that are taken before the port loads

  python3 -I tools/mkhlidents.py > tools/hl-idents.txt

A theorem or a definition of the port is a binding, and OCaml has
one namespace, so a binding of the port that HOL Light or the hand
written part of the library layer has already must get the name of
its theory in front of it (tools/port.py's bindname) -- otherwise
it shadows the one that was there, and a proof that names it gets
the port's statement instead of HOL Light's lemma with no error at
all.

This writes the list of those names: the top level bindings of the
files that HOL Light's hol_lib.ml loads, of help.ml, database.ml
and Library/words.ml (what ml/lib/preamble.ml adds), and of the
hand written files of ml/lib.  Run it again when the switch is
upgraded or a hand written library file gains a binding.
"""
import os, re, sys, glob

T = os.path.dirname(os.path.abspath(__file__)) + '/'
HL = os.environ.get('HOLLIGHT',
                    os.path.expanduser('~/.opam/hol-light/lib/hol_light'))
HAND = ['bag', 'define', 'fastdef', 'finite_map', 'hol4', 'lemmas',
        'llist', 'mc_tailrec', 'path', 'preamble', 'records',
        'relation', 'string4', 'tactics', 'theorem', 'words4']
# a top level binding of OCaml, in the shapes HOL Light writes
# one: `let foo =', `let rec foo =', `and foo =', a binding with
# its type in brackets (`let (ASM_REWRITE_TAC:thm list->tactic)')
# and a tuple of bindings (`let lhs,rhs = ...')
BIND = re.compile(r"^(?:let|and)[ \t]+(?:rec[ \t]+)?"
                  r"\(?([A-Za-z_][A-Za-z_0-9']*"
                  r"(?:[ \t]*,[ \t]*[A-Za-z_][A-Za-z_0-9']*)*)",
                  re.M)


# the kernel is a module, so its exported bindings (ASSUME,
# TRANS, REFL, ...) are indented by two spaces; every other file
# of HOL Light binds at the margin, and an indented let there is a
# local one
MODBIND = re.compile(r"^  (?:let|and)[ \t]+(?:rec[ \t]+)?"
                     r"\(?([A-Za-z_][A-Za-z_0-9']*)", re.M)


# a binding of several names, each with its type in brackets, over
# as many lines as HOL Light writes it (`let (X_GEN_TAC: ...),\n
# (X_CHOOSE_TAC: ...),\n (EXISTS_TAC: ...) =')
TYPED = re.compile(r"\(+([A-Za-z_][A-Za-z_0-9']*)\s*[:)]")


def names_of(text, module=False):
  out = set()
  for m in BIND.finditer(text):
    out |= set(n.strip() for n in m.group(1).split(','))
  # the head of such a binding runs to the `=' that ends it
  for m in re.finditer(r"(?ms)^let (\([^=]*?)=", text):
    out |= set(TYPED.findall(m.group(1)))
  if module: out |= set(MODBIND.findall(text))
  return out


def main():
  files = ['help.ml', 'database.ml', 'Library/words.ml']
  files += re.findall(r'^loads "([a-z_0-9]+\.ml)"',
                      open(HL + '/hol_lib.ml').read(), re.M)
  names = set()
  for f in files:
    try: names |= names_of(open(HL + '/' + f).read(),
                           f == 'fusion.ml')
    except OSError: print('no %s/%s' % (HL, f), file=sys.stderr)
  for h in HAND:
    names |= names_of(open(T + '../ml/lib/%s.ml' % h).read())
  for n in sorted(names): print(n)
  print('%d identifiers of %d files of HOL Light and %d of ml/lib'
        % (len(names), len(files), len(HAND)), file=sys.stderr)


if __name__ == '__main__':
  main()
