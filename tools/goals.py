"""classify the unsolved termination goals that a run with
   CAKE_DEBUG=1 logs to tmp/debug.txt

     python3 -I tools/goals.py [tmp/debug.txt]

   prints how often every shape of goal occurs (the goal with its
   numbers and variable names taken out), with one example each,
   and how often every reason a definition failed occurs."""
import sys, re, collections

def untype(s):
  """the goal without the type annotations that HOL Light's
     printer puts in where a term is polymorphic"""
  out = []
  i = 0
  n = len(s)
  while i < n:
    if s[i] == '(':
      # (name:type) is just the name
      j = i + 1
      while j < n and (s[j].isalnum() or s[j] in "_'"): j += 1
      if j < n and s[j] == ':' and j > i + 1:
        k = j + 1
        depth = 0
        while k < n and (depth or s[k] != ')'):
          if s[k] == '(': depth += 1
          elif s[k] == ')': depth -= 1
          k += 1
        if k < n:
          out.append(s[i+1:j])
          i = k + 1
          continue
    out.append(s[i])
    i += 1
  return ''.join(out)



if __name__ == '__main__':
  path = sys.argv[1] if len(sys.argv) > 1 else 'tmp/debug.txt'
  text = open(path, errors='replace').read().split('\n')

  goals = []        # (definition, goal, [assumptions])
  reasons = collections.Counter()
  defs = collections.Counter()
  i = 0
  while i < len(text):
    l = text[i]
    if l.startswith('unsolved termination goal'):
      # the log says of which definition the goal is
      m = re.match(r'unsolved termination goal of (.*):$', l)
      nm = m.group(1) if m else '?'
      i += 1
      g = []
      while i < len(text) and not text[i].startswith('  asm: ') and \
            not text[i].startswith('cannot prove') and \
            not text[i].startswith('unsolved termination goal'):
        g.append(text[i].strip()); i += 1
      asms = []
      while i < len(text) and text[i].startswith('  asm: '):
        asms.append(untype(text[i][7:].strip())); i += 1
      goals.append((nm, untype(' '.join(g)), asms))
      defs[nm] += 1
    elif l.startswith('cannot prove the condition'):
      m = re.search(r'\(([^)]*)\)', l)
      reasons[m.group(1) if m else '?'] += 1
      i += 1
    else:
      i += 1

  def shape(s):
    """the goal with its names and numbers taken out"""
    s = re.sub(r"\b[a-z][A-Za-z0-9_']*\b",
               lambda m: m.group(0) if '_' in m.group(0) else 'v', s)
    s = re.sub(r'\b\d+\b', 'n', s)
    return re.sub(r'\s+', ' ', s).strip()

  kinds = collections.Counter()
  examples = {}
  for nm, g, asms in goals:
    k = shape(g)
    kinds[k] += 1
    examples.setdefault(k, (g, asms))

  print('%d unsolved goals, %d shapes' % (len(goals), len(kinds)))
  print()
  for k, c in kinds.most_common(40):
    g, asms = examples[k]
    print('%4d  %s' % (c, g[:200]))
    for a in asms[:3]:
      print('        asm: %s' % a[:150])
  print()
  coarse = collections.Counter()
  for nm, g, asms in goals:
    k = re.sub(r"\b[A-Za-z0-9_']+_size[0-9]*\b", 'SIZE', shape(g))
    coarse[k] += 1
  print('the same with every size function the same:')
  for k, c in coarse.most_common(20):
    print('%4d  %s' % (c, k[:200]))
  print()
  print('the definitions with the most unsolved goals:')
  for nm, c in defs.most_common(20):
    print('%6d  %s' % (c, nm[:70]))
  print()
  print('how the condition failed:')
  for r, c in reasons.most_common():
    print('%6d  %s' % (c, r))
