# mkland.py <try file> <statement> : turn a development file of the
# proof loop into the file that tools/landproof.py reads.
#
# A development file has the helpers of a proof as top level lets
# and then one attempt
#
#   let _ = bp "<nm>" <statement term> (fun () -> <tactic>);;
#
# and what landproof wants is the tactic alone, with the helpers
# inside it:
#
#   let <name> = btry "<name>" <statement term>
#    (fun () ->
#      (<the helpers, as lets>
#       <the tactic>));;
#
# The lines of the harness (b_open, b_asm, b_secs, say, pg, pa,
# shw) are dropped, and so is every `shw "..."` of the tactic.
import re, sys

DROP = ('b_open', 'b_asm', 'b_secs', 'print_types_of_subterms',
        'let pg ', 'let pa ', 'let shw ', 'let _ = pg ',
        'let _ = b_end')

def blocks(s):
  """the top level items of the file, each starting at a line that
     starts with `let` or `(*`"""
  out, cur = [], []
  for l in s.split('\n'):
    if (l.startswith('let ') or l.startswith('(*')) and cur:
      out.append('\n'.join(cur)); cur = [l]
    else:
      cur.append(l)
  if cur: out.append('\n'.join(cur))
  return out

def main(argv):
  if len(argv) < 3:
    sys.exit('usage: mkland.py <try file> <statement>')
  s = open(argv[1]).read()
  name = argv[2]
  s = re.sub(r'shw "[a-zA-Z0-9_]+" ?', '', s)
  s = re.sub(r' *W\(fun \(asl,gl\) -> pg "[A-Za-z0-9]+" gl;'
             r'( pa asl;)? ALL_TAC\) THEN\n', '', s)
  bs = blocks(s)
  helpers, attempt = [], None
  for b in bs:
    if re.match(r'let _ = bp\b', b) or re.match(r'let \w+ = b_the \(bp\b', b):
      attempt = b
    elif any(b.startswith(d) or ('\n' + b).find('\n' + d) == 0
             for d in DROP):
      pass
    else:
      helpers.append(b)
  if attempt is None:
    sys.exit('mkland: the file has no bp attempt')
  m = re.match(r'let [^=]+ = (?:b_the \()?bp "[^"]+"', attempt)
  mt = None
  def balanced(t):
    d = 0
    for ch in t:
      if ch == '(': d += 1
      elif ch == ')':
        d -= 1
        if d < 0: return False
    return d == 0
  for c in re.finditer(r'\(fun \(\) ->', attempt):
    if balanced(attempt[m.end():c.start()]):
      mt = c; break
  stmt = attempt[m.end():mt.start()].strip()
  tac = attempt[mt.end():].rstrip()
  tac = re.sub(r'\)*;;\s*$', '', tac)
  # a statement that the attempt names by a binding of its own is
  # not a helper of the tactic: the proof store takes the statement
  # from the file, not from here
  if re.match(r'^\w+$', stmt):
    helpers = [h for h in helpers
               if not re.match(r'(?m)^let %s\b' % re.escape(stmt), h)]
  def lets_in(t):
    t = t.rstrip()
    if t.endswith(';;'): t = t[:-2] + ' in'
    return re.sub(r';;\n', ' in\n', t)
  body = '\n'.join(lets_in(h) for h in helpers if h.strip()) + '\n' + tac
  body = '\n'.join(('   ' + l) if l.strip() else l
                   for l in body.split('\n'))
  out = ('let btry nm tm f = b_the (bp nm tm f);;\n'
         'let %s = btry "%s" %s\n (fun () ->\n%s));;\n'
         % (name, name, stmt, body.lstrip('\n')))
  sys.stdout.write(out)

main(sys.argv)
