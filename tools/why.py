"""show why a definition does not parse

  python3 -I tools/why.py <theory> <name>...
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod, port as portmod, hol4, hterm

db = dbmod.Db()
thy = sys.argv[1]
names = sys.argv[2:]
p = portmod.Porter(db, thy)
db.base_grammar(thy)
for b in hol4.parse(p.path):
  if b.kind == 'ML':
    for tok, prec, ass, _ in hol4.fixities(b.text):
      hterm.add_infix(tok, prec, ass)
    mode = hol4.equality_mode(b.text)
    if mode: hterm.set_equality(mode == 'loose')
  if b.name in names or (b.kind in ('Type','Overload') and b.name in names):
    try:
      p.block(b)
      print('OK  ', b.kind, b.name)
    except Exception as ex:
      print('FAIL', b.kind, b.name, '->', ex)
      m = re.search(r'at (\d+)', str(ex))
      body = hol4.strip_comments(b.body)
      if m:
        i = int(m.group(1))
        print('   ...' + body[max(0, i-100):i] + ' <<HERE>> ' +
              body[i:i+60] + '...')
      else:
        print('   body:', body[:200])
