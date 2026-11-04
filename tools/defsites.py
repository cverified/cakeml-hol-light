"""where the port defines every constant: the file it is in and the
   name of the OCaml phrase that defines it, from the heads of the
   clauses of every definition phrase of ml/.

   The reports use this instead of searching for a name, because a
   name may be in a file that only uses it (labSem's loc_to_pc is
   in lab_to_targetProof as well).
"""
import re, os

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PHRASE = re.compile(r"^let ([A-Za-z0-9_']+)[ ,].*?;;$", re.M | re.S)
DECLARE = re.compile(r"""cake_declare\s+"([A-Za-z0-9_']+)\"""")
# a theorem of the port (and a lemma of its own): the head of the
# first clause of its statement is no constant that it defines.
# While phase two was going the test was for cake_theorem, the
# wrapper of the library; a theorem is a plain prove now, and the
# test that stayed behind made the heads of 496 statements into
# constants and sent 409 real ones to a theorem about them
PROVED = re.compile(r"^let [A-Za-z0-9_']+ =\s*prove\b")


def clause_heads(phrase):
  """the constants that a phrase of the port defines: the head of
     the first clause of every quotation in it (the clauses of one
     quotation define the same constant, and a mutual definition
     has a quotation for each of them)"""
  out = set()
  for q in re.findall(r'`([^`]*)`', phrase, re.S):
    # a comment of the source that stands inside the quotation is
    # no clause of the definition (HOL Light reads // to the end
    # of the line as a comment)
    q = re.sub(r'(?m)//.*$', '', q)
    cl = re.split(r'/\\', q)[0].strip()
    while cl.startswith('('): cl = cl[1:].lstrip()
    cl = re.sub(r'^!\s*[^.]*\.\s*', '', cl)
    m = re.match(r"([A-Za-z_][A-Za-z0-9_']*)", cl)
    if m: out.add(m.group(1))
  return out


def sites():
  """{constant: (file of ml/, name of the phrase)}"""
  out = {}
  for root, dirs, files in os.walk(C + '/ml'):
    for f in sorted(files):
      if not f.endswith('.ml'): continue
      p = os.path.join(root, f)
      rel = os.path.relpath(p, C + '/ml')
      src = open(p).read()
      for m in PHRASE.finditer(src):
        # a theorem is not a definition of the constants its
        # statement mentions
        if PROVED.match(m.group(0)): continue
        for h in clause_heads(m.group(0)):
          out.setdefault(h, (rel, m.group(1)))
      for m in DECLARE.finditer(src):
        out.setdefault(m.group(1), (rel, None))
  return out
