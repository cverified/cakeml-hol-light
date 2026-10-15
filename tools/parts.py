"""write the parts of one phrase of an ml file of the port as a
   file that parses them one by one, so that loading it in a
   session that has what the phrase needs says which part does not
   typecheck and why.

     python3 -I tools/parts.py <mlfile> <phrase> <out>

   The parts of a quotation are its conjuncts, and of a conjunct
   whose right hand side is a match, the arms of that match (with
   the left hand side in front of each, so that the types are the
   ones of the clause).
"""
import sys, os, re

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hterm

MARK = """let cake_mark s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "/home/freek/claude/hol-light/cakeml/tmp/mark.txt" in
  output_string ch (s ^ "\\n"); close_out ch;;
"""


def phrases(text):
  return [p for p in re.split(r'(?<=;;)\n', text) if p.strip()]


def quotes(p):
  """the quotations of a phrase, without the backquotes"""
  return re.findall(r'`([^`]*)`', p, re.S)


def split_conj(s):
  """the conjuncts of a term, which /\\ separates outside
     parentheses, brackets and braces"""
  out = []
  cur = ''
  depth = 0
  i = 0
  while i < len(s):
    c = s[i]
    if c in '([{': depth += 1
    elif c in ')]}': depth -= 1
    if not depth and s.startswith('/\\', i):
      out.append(cur); cur = ''; i += 2; continue
    cur += c; i += 1
  out.append(cur)
  return [c for c in out if c.strip()]


def split_arms(s):
  """a term of the form lhs = match x with p1 -> e1 | ... as the
     list of its arms, each with the lhs and the first arm in
     front of it (the first arm fixes the types)"""
  m = re.match(r'(.*?=\s*\(?\s*match\s+.*?\s+with\s+)(.*)$', s, re.S)
  if not m: return []
  head, body = m.group(1), m.group(2)
  arms = []
  cur = ''
  depth = 0
  i = 0
  while i < len(body):
    c = body[i]
    if c in '([{': depth += 1
    elif c in ')]}': depth -= 1
    if not depth and c == '|':
      arms.append(cur); cur = ''; i += 1; continue
    cur += c; i += 1
  arms.append(cur)
  arms = [a for a in arms if a.strip()]
  if len(arms) < 2: return []
  out = []
  for a in arms[1:]:
    out.append(head + arms[0].rstrip().rstrip(')') + ' | ' + a)
  return out


def main():
  src, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
  p = phrases(open(src).read())[n - 1]
  parts = []
  for q in quotes(p):
    cs = split_conj(q)
    if len(cs) > 1:
      parts += cs
    else:
      arms = split_arms(q)
      parts += arms or [q]
  res = [MARK]
  for i, part in enumerate(parts):
    res.append('(try (let _ = (`%s`:term) in ())\n'
               ' with Failure e -> cake_mark ("%d: " ^ e));;\n'
               % (part, i + 1))
  open(out, 'w').write('\n'.join(res))
  for i, part in enumerate(parts):
    print('%d: %s' % (i + 1, ' '.join(part.split())[:70]))


main()
