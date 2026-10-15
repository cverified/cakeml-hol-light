"""how much of every file of the port is there

  python3 -I tools/coverage.py [theory...]

reports, for each theory, how many blocks of the HOL4 source the
port has to have and how many it has (a PENDING comment counts as
missing).
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, port as portmod

# the blocks that have to become a definition of the port; a Type
# with parameters and an Overload are expanded by the translation,
# so they do not
KINDS = ('Datatype', 'Definition', 'Inductive', 'CoInductive')

def main():
  db = dbmod.Db()
  thys = sys.argv[1:] or [t for t, _, k in db.order]
  tot = [0, 0, 0, 0]
  print('%-28s %6s %6s %6s %6s' %
        ('theory', 'blocks', 'in', 'pend', 'fail'))
  for thy in thys:
    path = db.thy_of_file.get(thy)
    if not path: continue
    p = portmod.Porter(db, thy)
    want = 0
    for b in hol4.parse(path):
      if b.kind in KINDS and p.wanted(b): want += 1
      elif b.kind == 'Type' and p.wanted(b):
        try:
          ty = hterm.parse_type_text(dbmod.strip_quote(b.body))
          if not hterm.type_vars_of(ty): want += 1
        except Exception:
          pass
    mlpath = portmod.ML + db.mlpath_of(thy)
    try:
      text = open(mlpath).read()
    except Exception:
      text = ''
    have = len(re.findall(r'^let [^=]*= *(cake_define|cake_define_wf|'
                          r'cake_define_list|cake_define_tac|'
                          r'cake_inductive|define_datatype|'
                          r'define_record)', text, re.M))
    have += len(re.findall(r'^new_type_abbrev', text, re.M))
    pend = len(re.findall(r'^\(\* PENDING', text, re.M))
    fail = len(re.findall(r'^\(\* PORT FAILED', text, re.M))
    tot[0] += want; tot[1] += have; tot[2] += pend; tot[3] += fail
    print('%-28s %6d %6d %6d %6d' % (thy, want, have, pend, fail))
  print('%-28s %6d %6d %6d %6d' % ('TOTAL', *tot))

main()
