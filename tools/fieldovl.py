"""write tmp/fieldovl.txt, the names that overload the accessors
   of a record field

  python3 -I tools/fieldovl.py

A statement that uses one of them for a variable of its own is
read with them taken away (`cake_as_vars` of ml/lib/theorem.ml);
tools/diag.ml does the same, so that a diagnosis says what a run
says.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod

T = os.path.dirname(os.path.abspath(__file__)) + '/'
db = dbmod.Db()
amb = db.ambiguous_fields()
names = sorted(set(list(amb.values()) +
                   [v + '_fupd' for v in amb.values()]))
open(T + '../tmp/fieldovl.txt', 'w').write('\n'.join(names) + '\n')
print('%d names that overload a record field' % len(names))
