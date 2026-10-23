"""the statements where a word's bitwise operator meets + or -

  python3 -I tools/wordprec.py [<file of ml/>...]

HOL4 gives `&&` the precedence 490, `??` 485 and `||` 482, and `+`
500, so a bitwise operator binds *looser* than an addition:
`-2w && 16w * tag + 2w` is `-2w && (16w * tag + 2w)`.  The port
gives `&&` 20, `||` 16 and `??` 16, and HOL Light gives `+` 16,
where a *higher* number binds tighter -- so `&&` binds tighter
than `+` there, and `||` and `??` only group HOL4's way when the
bitwise operator comes first (both are right associative at the
same level).  This reports the quoted terms where the two kinds of
operator meet with no parenthesis between them, which are the
statements whose reading in the port is not the source's (see
ISSUES.md, "The precedence of a word's bitwise operators").
"""
import sys, os, re

BITW = ['~&&', '~||', '&&', '||', '??']
ADD = ['+', '-']

# an operator that separates two operand chains: what stands on the
# two sides of it does not group with what stands on the other
SEP = ['==>', '<=>', '/\\', '\\/', '=', ',', '<=', '<', '>', 'IN',
       'THEN', ';', ':']

def chains(term):
  """the operator chains of a term: the operators between one pair
     of parentheses and one pair of separators, in the order read"""
  out, cur, depth, i, n = [], {}, 0, 0, len(term)
  def flush(d):
    if d in cur:
      out.append(cur.pop(d))
  while i < n:
    c = term[i]
    if c in '([':
      depth += 1; i += 1; continue
    if c in ')]':
      flush(depth); depth -= 1; i += 1; continue
    if term.startswith('--', i):          # word negation, not a minus
      i += 2; continue
    if term.startswith('->', i) or term.startswith('>>', i):
      i += 2; continue
    if term.startswith('//', i):          # a comment of the source
      j = term.find('\n', i)
      i = n if j < 0 else j
      continue
    sep = next((o for o in SEP if term.startswith(o, i)), None)
    if sep is not None:
      flush(depth); i += len(sep); continue
    hit = next((o for o in BITW if term.startswith(o, i)), None)
    if hit is not None:
      cur.setdefault(depth, []).append(('bitw', hit)); i += len(hit)
      continue
    if c in ADD and (i + 1 >= n or term[i+1] not in '+->'):
      cur.setdefault(depth, []).append(('add', c)); i += 1
      continue
    i += 1
  for d in sorted(cur):
    out.append(cur[d])
  return out

def quoted(src):
  out, i = [], src.find('`')
  while i >= 0:
    j = src.find('`', i + 1)
    if j < 0:
      break
    out.append(src[i+1:j])
    i = src.find('`', j + 1)
  return out

def files(args):
  if args:
    return args
  out = []
  for d, _, fs in os.walk('ml'):
    out += [os.path.join(d, f) for f in fs if f.endswith('.ml')]
  return sorted(out)

n = 0
for p in files(sys.argv[1:]):
  for term in quoted(open(p).read()):
    for ops in chains(term):
      kinds = [k for k, _ in ops]
      if 'bitw' in kinds and 'add' in kinds:
        n += 1
        flat = ' '.join(o for _, o in ops)
        one = ' '.join(term.split())
        print('%s: %s  in `%s`' % (p, flat, one[:90]))
print('%d term(s) where a bitwise operator meets + or -' % n)
