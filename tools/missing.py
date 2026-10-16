"""the names that a file of the port uses and that nothing
   provides: HOL Light does not have them, the library layer does
   not have them and no theory of the port defines them.  They are
   free variables of the definitions that use them, which is why
   cake_define cannot make those definitions.

     python3 -I tools/missing.py [<file>...]
"""
import sys, os, re, collections

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, C + '/tools')
import db as dbmod

db = dbmod.Db()
known = set(db.hl) | set(db.provided) | set(db.defs)
# the names that the port gives its constants
known |= set(v for v in db.rename.values())
# the OCaml vocabulary of a file of the port and the words of its
# comments are not names of the terms
SKIP = set(['let', 'in', 'and', 'if', 'then', 'else', 'match',
            'with', 'function', 'when', 'needs', 'cake_define',
            'cake_define_list', 'cake_define_wf', 'thm', 'term',
            'define_datatype', 'define_record', 'hol4_overload',
            'hol4_only', 'cake_inductive', 'cake_declare',
            'cake_define_list_wf', 'new_type_abbrev', 'size_thms',
            'MEASURE', 'INDUCT', 'RECURSION', 'FIELDS', 'T', 'F'])

def quotations(text):
  """the quotations of a file, without the comments around them"""
  text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
  return re.findall(r'`([^`]*)`', text, re.S)

args = sys.argv[1:]
files = []
for root, dirs, fs in os.walk(C + '/ml'):
  for f in sorted(fs):
    if f.endswith('.ml'):
      files.append(os.path.relpath(os.path.join(root, f), C + '/ml'))
if args: files = [f for f in files if f in args]
out = collections.defaultdict(set)
for f in files:
  if f.startswith('lib/'): continue
  text = open(C + '/ml/' + f).read()
  for q in quotations(text):
    # a bound variable is lower case, a constant of the port is
    # not: only names that look like constants are reported
    for nm in re.findall(r"[A-Za-z][A-Za-z0-9_']*", q):
      if nm in SKIP or nm in known: continue
      if nm[0].islower() and '_' not in nm: continue
      out[nm].add(f)
for nm in sorted(out, key=lambda n: (-len(out[n]), n)):
  fs = sorted(out[nm])
  print('%-32s %d  %s' % (nm, len(fs), ' '.join(fs[:3])))
print(len(out), 'names that nothing provides')
