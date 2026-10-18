"""write tmp/fieldovl.txt, the overloads of the accessors of a
   record field: the name and the constant of every one

  python3 -I tools/fieldovl.py

A statement that uses such a name for a variable of its own is
read with those overloads taken away (`cake_as_vars` of
ml/lib/theorem.ml); tools/diag.ml does the same, so that a
diagnosis says what a run says.  Only the accessors go: a name
that a constant of its own has as well (bvl_to_bvi's compile
against the compile of a state) keeps that constant, which is why
the file has the constant of every overload in it and not only
the name.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'
OVL = re.compile(r'hol4_field_overload\s*\n?\s*"([^"]+)"\s*\n?\s*'
                 r'"([^"]+)"')
out = set()
for dp, _, fs in os.walk(ML):
  for f in sorted(fs):
    if not f.endswith('.ml'): continue
    for m in OVL.finditer(open(os.path.join(dp, f)).read()):
      out.add((m.group(1), m.group(2)))
with open(T + '../tmp/fieldovl.txt', 'w') as o:
  for n, c in sorted(out):
    o.write('%s\t%s\n' % (n, c))
print('%d overloads of a record field, %d names'
      % (len(out), len(set(n for n, _ in out))))
