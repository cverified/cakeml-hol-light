"""write a test that checks the definitions named on the command
   line (file:binding) the way cake_define does: the clauses of a
   clause list have to fit together (cake_conj_list), a definition
   that is one quotation has to typecheck.  The constants are
   renamed, so that a session that has them already does not give
   them their old types.

     python3 -I tools/conjtest.py <tree> <out> <file:binding>...
"""
import re, sys

tree, out = sys.argv[1], sys.argv[2]
tests = []
for arg in sys.argv[3:]:
  f, name = arg.rsplit(':', 1)
  text = open(tree + '/' + f).read()
  ph = [p for p in re.split(r'(?<=;;)\n', text) if p.strip()]
  cand = [p for p in ph
          if re.search(r'^let %s = ' % re.escape(name), p, re.M)]
  if not cand:
    print('MISSING', arg); continue
  q = cand[0]
  # a comment of the phrase may hold the HOL4 ML code that the
  # port did not take over, with quotations of its own in it
  q = re.sub(r'\(\*.*?\*\)', '', q, flags=re.S)
  qs = [x for x in re.findall(r'`([^`]*)`', q, re.S) if x.strip()]
  # the first quotation of a wf form is the termination relation
  if 'cake_define_wf' in q or 'cake_define_list_wf' in q:
    qs = qs[1:]
  lst = 'cake_define_list' in q
  def split_top(s, op):
    """the parts of a term that an operator separates outside
       parentheses"""
    out = []
    cur = ''
    depth = 0
    i = 0
    while i < len(s):
      c = s[i]
      if c in '([{': depth += 1
      elif c in ')]}': depth -= 1
      if not depth and s.startswith(op, i):
        out.append(cur); cur = ''; i += len(op); continue
      cur += c; i += 1
    out.append(cur)
    return [x for x in out if x.strip()]

  def strip(s):
    """a term without its outer parentheses and its leading
       quantifier"""
    while True:
      s = s.strip()
      if s.startswith('('):
        depth = 0
        end = -1
        for i, c in enumerate(s):
          if c in '([{': depth += 1
          elif c in ')]}':
            depth -= 1
            if depth == 0: end = i; break
        if end == len(s) - 1:
          s = s[1:-1]; continue
      if s.startswith('!') and '.' in s:
        s = s.split('.', 1)[1]; continue
      return s

  hs = set()
  for cl in qs:
    for c in split_top(cl, '/\\'):
      c = strip(c)
      # the head of a rule of an inductive relation is the one of
      # its conclusion, which comes after the last ==> that is not
      # inside parentheses
      c = strip(split_top(c, '==>')[-1])
      for c2 in split_top(c, '/\\'):
        m = re.match(r"\s*[(\s]*(?:!\s*[^.]*\.\s*)?"
                     r"([A-Za-z_][A-Za-z0-9_']*)", strip(c2))
        if m: hs.add(m.group(1))
  def rename(s):
    for h in sorted(hs):
      if h in ('T', 'F', 'let', 'match', 'if'): continue
      s = re.sub(r'\b%s\b' % re.escape(h), h + '_zz', s)
    return s
  qs = [rename(x) for x in qs]
  term = ('cake_conj_list [`' + '`;\n  `'.join(qs) + '`]' if lst
          else '(`' + qs[0] + '`:term)')
  tag = f.split('/')[-1] + ':' + name
  tests.append('(try (let _ = %s in\n'
               '   print_string ("OK %s\\n"))\n'
               ' with Failure e ->\n'
               '   print_string ("FAIL %s: " ^ e ^ "\\n"));;'
               % (term, tag, tag))
open(out, 'w').write('\n'.join(tests) + '\n')
print(len(tests), 'tests')
