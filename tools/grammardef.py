"""HOL4's grammarLib, which the port cannot run: mk_grammar_def
   takes the grammar of semantics/gram in BNF and makes a datatype
   of its nonterminals (MMLnonT) and the grammar itself (cmlG).

   This parses the BNF and the ML code around it and gives the
   blocks back, so that the port writes them as it writes the other
   definitions that HOL4 makes with ML code.
"""
import re

# -- the ML code around the grammar ------------------------------

TOKMAP = re.compile(r'\("((?:[^"\\]|\\.)*)"\s*,\s*(?:``|“)'
                    r'([^`”]*)(?:``|”)\)')
GINFO = re.compile(r'val\s+ginfo\s*=\s*\{(.*?)\}', re.S)
FIELD = re.compile(r'(\w+)\s*=\s*([^,}]*)')


def parse_ml(text):
  """the token map and the ginfo of the ML code of a theory"""
  tokmap = {}
  m = re.search(r'val\s+tokmap0\s*=(.*?)\nfun\s', text, re.S)
  if m:
    for s, t in TOKMAP.findall(m.group(1)):
      tokmap[s] = ' '.join(t.split())
  info = {}
  m = GINFO.search(text)
  if m:
    for k, v in FIELD.findall(m.group(1)):
      info[k] = v.strip()
  for k in ('nt_tyname', 'start', 'gname'):
    if k in info:
      info[k] = info[k].strip().strip('"').strip('`').strip()
  m = re.search(r'mkntname\s*=\s*\(fn\s+\w+\s*=>\s*"([^"]*)"',
                info.get('mkntname', ''))
  info['ntprefix'] = m.group(1) if m else 'n'
  info['tokmap'] = tokmap
  return info


# -- the BNF -----------------------------------------------------

def strip_comments(s):
  out = []
  i = 0
  depth = 0
  while i < len(s):
    if s.startswith('(*', i):
      depth += 1; i += 2; continue
    if s.startswith('*)', i) and depth:
      depth -= 1; i += 2; continue
    if not depth: out.append(s[i])
    i += 1
  return ''.join(out)


def split_rules(s):
  """the text of the rules, which end in a ; that is not in a
     string or in an antiquotation"""
  out = []
  cur = ''
  i = 0
  while i < len(s):
    c = s[i]
    if c == '"':
      j = s.index('"', i + 1)
      cur += s[i:j + 1]; i = j + 1; continue
    if c == '^':
      j = aq_end(s, i)
      cur += s[i:j]; i = j; continue
    if c == ';':
      out.append(cur); cur = ''; i += 1; continue
    cur += c; i += 1
  if cur.strip(): out.append(cur)
  return out


def aq_end(s, i):
  """the end of the antiquotation that starts at the ^ at i"""
  assert s[i] == '^'
  j = i + 1
  while j < len(s) and s[j].isspace(): j += 1
  if j < len(s) and s[j] == '(':
    depth = 0
    while j < len(s):
      if s[j] == '(': depth += 1
      elif s[j] == ')':
        depth -= 1
        if depth == 0: return j + 1
      j += 1
  raise SyntaxError('antiquotation at %d' % i)


def aq_term(s):
  """the term of an antiquotation ^(``...``)"""
  t = s.strip()
  assert t[0] == '^'
  t = t[1:].strip()
  assert t[0] == '(' and t[-1] == ')'
  t = t[1:-1].strip()
  for a, b in (('``', '``'), ('“', '”')):
    if t.startswith(a) and t.endswith(b):
      return t[len(a):-len(b)]
  return t


def split_alts(s):
  """the alternatives of a rule, which | separates outside a
     string and an antiquotation"""
  out = []
  cur = ''
  i = 0
  while i < len(s):
    c = s[i]
    if c == '"':
      j = s.index('"', i + 1)
      cur += s[i:j + 1]; i = j + 1; continue
    if c == '^':
      j = aq_end(s, i)
      cur += s[i:j]; i = j; continue
    if c == '|':
      out.append(cur); cur = ''; i += 1; continue
    cur += c; i += 1
  out.append(cur)
  return out


def parse_syms(s):
  """the symbols of an alternative"""
  out = []
  i = 0
  while i < len(s):
    c = s[i]
    if c.isspace(): i += 1; continue
    if c == '"':
      j = s.index('"', i + 1)
      out.append(('str', s[i + 1:j])); i = j + 1; continue
    if c == '<':
      j = s.index('>', i)
      out.append(('tok', s[i + 1:j].strip())); i = j + 1; continue
    m = re.match(r"[A-Za-z][A-Za-z0-9_']*", s[i:])
    if m:
      out.append(('nt', m.group(0))); i += len(m.group(0)); continue
    raise SyntaxError('grammar symbol at %r' % s[i:i + 20])
  return out


def parse_bnf(q):
  """the rules of a BNF quotation as (name, [clause]), where a
     clause is ('syms',[sym]) or ('aq',term)"""
  out = []
  for rule in split_rules(strip_comments(q)):
    if not rule.strip(): continue
    m = re.match(r"\s*([A-Za-z][A-Za-z0-9_']*)\s*::=(.*)$", rule, re.S)
    if not m: raise SyntaxError('grammar rule at %r' % rule[:40])
    nt, body = m.group(1), m.group(2)
    cls = []
    for alt in split_alts(body):
      if alt.strip().startswith('^'):
        cls.append(('aq', aq_term(alt)))
      else:
        cls.append(('syms', parse_syms(alt)))
    out.append((nt, cls))
  return out


def nonterminals(rules, prefix='n'):
  """the names of the datatype of the nonterminals, in the order
     in which HOL4 makes them (it folds over a set of strings that
     is ordered by <, prepending, so they come out the other way
     round)"""
  nts = set()
  for nt, cls in rules:
    nts.add(prefix + nt)
    for kind, c in cls:
      if kind != 'syms': continue
      for k, s in c:
        if k == 'nt': nts.add(prefix + s)
  return sorted(nts, reverse=True)


# -- what mk_grammar_def makes -----------------------------------

def var_names(tys):
  """the names that HOL4 gives the arguments of a token: the first
     letter of the type, with a prime where that is taken"""
  out = []
  for ty in tys:
    base = ty.strip().lstrip("'")[:1] or 'x'
    nm = base
    while nm in out: nm += "'"
    out.append(nm)
  return out


def generate(rules, info, p, hterm):
  """the datatype of the nonterminals and the grammar itself, as
     the port writes them.  p is the porter, for the names that
     the port gives the constants and for printing the terms of
     the antiquotations"""
  prefix = info['ntprefix']
  nty = info['nt_tyname']
  nts = nonterminals(rules, prefix)
  dt = '%s = %s' % (nty, ' | '.join(nts))

  def term(txt):
    """a HOL4 term of the ML code, as the port writes it"""
    return p.term(txt)

  def tok(txt):
    return '%s (%s)' % (p.ctx.name('TOK'), term(txt))

  def nt(name):
    return '%s (INL %s)' % (p.ctx.name('NT'), prefix + name)

  def syms_clause(syms):
    """the set of one alternative: the list of its symbols, and
       where a token takes arguments they are variables that the
       set abstraction binds"""
    out = []
    used = []
    for kind, s in syms:
      if kind == 'nt':
        out.append(nt(s)); continue
      if kind == 'str':
        txt = info['tokmap'].get(s)
        if txt is None:
          raise SyntaxError('no token for %r' % s)
        out.append(tok(txt)); continue
      # <Name>: the token constant, applied to a variable for
      # every argument it takes
      tys = []
      n = 0
      while (p.db.con_argty_thy.get(('tokens', s, n)) is not None):
        tys.append(p.db.con_argty_thy[('tokens', s, n)]); n += 1
      vs = []
      for v in var_names(tys):
        while v in used or v in vs: v += "'"
        vs.append(v)
      used += vs
      out.append(tok(' '.join([s] + vs)) if vs else tok(s))
    body = '[' + '; '.join(out) + ']'
    if not used: return '{' + body + '}'
    return '{%s | %s | T}' % (body, ','.join(used))

  def aq_clause(txt):
    """the antiquotation of an alternative is a set of tokens, and
       the alternative is the set of the one element lists of
       those tokens (HOL4's image in grammarLib)"""
    e = hterm.Parser(hterm.tokenize(txt), p.ctx).parse()

    def go(e):
      while e.kind == 'paren': e = e.e
      if e.kind == 'set':
        # the elements of a set are separated by commas, not by
        # the semicolons of a list
        return '{' + ','.join(
          '[%s (%s)]' % (p.ctx.name('TOK'), pr(i)) for i in e.items) + '}'
      if e.kind == 'setabs':
        return '{[%s (%s)] | %s}' % (p.ctx.name('TOK'), pr(e.e), pr(e.p))
      if e.kind == 'setabs2':
        return '{[%s (%s)] | %s | %s}' % (p.ctx.name('TOK'), pr(e.e),
                                          pr(e.p), pr(e.p2))
      if e.kind == 'infix' and e.op in ('UNION', '∪'):
        return '(%s UNION %s)' % (go(e.l), go(e.r))
      raise SyntaxError('grammar antiquotation %r' % txt[:40])

    def pr(x):
      return hterm.Printer(p.ctx).pr(x, 0)

    return go(e)

  parts = []
  for name, cls in rules:
    sets = []
    for kind, c in cls:
      sets.append(syms_clause(c) if kind == 'syms' else aq_clause(c))
    rhs = sets[0]
    for s in sets[1:]:
      rhs = '(%s UNION %s)' % (rhs, s)
    parts.append('(INL %s,%s)' % (prefix + name, rhs))
  rules_txt = 'FEMPTY'
  for q in parts:
    rules_txt += ' |+ ' + q
  gr = 'mk_grammar (INL %s%s) (%s)' % (prefix, info['start'], rules_txt)
  return dt, '%s = %s' % (info['gname'], gr)
