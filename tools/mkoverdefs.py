"""the definition blocks of tools/overrides.py, on the new surface

     python3 -I tools/mkoverdefs.py [--write]

   The blocks that overrides.py writes by hand go into a file of
   the port as they stand, so they say how the definition is made
   like every other definition does.  This rewrites the ones that
   still say cake_define, from what a run harvested
   (tools/strategies.py); without --write it only reports.
"""
import io, os, re, sys

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import strategies

# the constant a quotation defines: the first name in it, past the
# quantifiers and the brackets
HEAD = re.compile(r"`\s*(?:!\s*[^.]*?\.\s*)?\(?\s*"
                  r"([A-Za-z_][A-Za-z0-9_']*)")


def way_of(const):
  try: return strategies.BY_CONST[const]
  except (AttributeError, KeyError): pass
  for (thy, c), v in strategies.WAY.items():
    if c == const: return v
  return None


def rewrite(block, head, const, way):
  """the block with its first line and its brackets put right"""
  strat, assumed, rel = way
  bind = head
  ind = (bind[:-4] if bind.endswith('_def') else bind) + '_ind'
  # a rewriting of the clauses says the way what comes out is made
  # in the same word ("sing>nested"); the first of them is what
  # the way is called
  first = strat.split('>')[0]
  recursive = first not in ('new_definition', 'define_single',
                            'new_recursive_definition', 'general')
  if strat == '':
    how, pair, args = 'assume_definition', False, '"assumed"\n  '
  elif strat == 'new_definition':
    return None                      # the name alone changes
  elif first in ('define_single', 'general'):
    how, pair, args = 'define_general', False, ''
  elif not recursive:
    how, pair, args = 'define_cases', False, ''
  elif first in ('nested', 'maplist', 'cond_bool', 'sing', 'cases',
                 'match', 'lift_if'):
    how = 'define_shaped_' + ('wf' if rel else 'rec')
    pair, args = True, '"%s"\n  ' % strat
    if rel: args += '`%s`\n  ' % rel
  elif rel:
    how, pair, args = 'define_wf', True, '`%s`\n  ' % rel
  elif first == 'prim_rec':
    how, pair, args = 'define_rec', True, ''
  else:
    how, pair, args = 'define_guess', True, ''
  if assumed and how.endswith(('_wf', '_rec')): how += '_cheat'
  return how, (bind + ',' + ind if pair else bind), args


def head_of(body, kind):
  """the constant a block defines.  cake_define_wf writes the
     relation first, so the name is in the quotation after it."""
  if kind == '_wf':
    i = body.index('`', body.index('`') + 1) + 1
    body = body[i:]
  m = HEAD.search(body)
  return m.group(1) if m else None


def block_end(s, i):
  """the index past the `;;` that ends the block that starts at i,
     counting quotations so that a `;;` inside one does not end
     it"""
  q = False
  while i < len(s) - 1:
    if s[i] == '`': q = not q
    elif not q and s[i] == ';' and s[i + 1] == ';': return i + 2
    i += 1
  return len(s)


def convert(s, m):
  """the new text of the block that m starts, or None to leave it"""
  bind, kind = m.group(1), m.group(2) or ''
  end = block_end(s, m.end())
  body = s[m.end():end]
  const = head_of(body, kind)
  if not const: return None
  way = way_of(const)
  if not way: return None
  r = rewrite(body, bind, const, way)
  if r is None:
    return 'let %s = new_definition\n%s' % (bind, body)
  how, binding, args = r
  # cake_define_wf writes the relation first and the term after,
  # and the new way takes the clauses as a list
  if kind == '_wf':
    i = body.index('`', body.index('`') + 1) + 1
    args, body = '%s\n  ' % body[:i].strip(), body[i:]
  if kind != '_list':
    i, j = body.index('`'), body.rindex('`')
    body = body[:i] + '[' + body[i:j + 1] + ']' + body[j + 1:]
  return 'let %s = %s\n  %s%s' % (binding, how, args,
                                   body.lstrip())


def main():
  write = '--write' in sys.argv
  p = T + 'overrides.py'
  s = io.open(p, encoding='utf-8').read()
  out, n, left = [], 0, 0
  pat = re.compile(
      r"^let ([A-Za-z0-9_]+) = cake_define(_list|_wf|_gen)?\n", re.M)
  pieces, at = [], 0
  for m in pat.finditer(s):
    const = head_of(s[m.end():block_end(s, m.end())],
                    m.group(2) or '')
    way = way_of(const) if const else None
    out.append('%-34s %-22s %s'
               % (m.group(1), const, way if way else 'NO HARVEST'))
    new = convert(s, m) if way else None
    if new is None:
      left += 1; continue
    n += 1
    end = block_end(s, m.end())
    pieces.append(s[at:m.start()]); pieces.append(new); at = end
  pieces.append(s[at:])
  print('\n'.join(out))
  print('%d of %d blocks rewritten' % (n, n + left))
  if write and n:
    io.open(p, 'w', encoding='utf-8').write(''.join(pieces))
    print('tools/overrides.py written')
  return 0


if __name__ == '__main__':
  sys.exit(main())
