"""Parsing of the HOL4 script files of CakeML.

Splits a Script.sml file into top level blocks and extracts the
names that each block defines.
"""
import re, os

SRC = '/home/freek/claude/hol-light/cakeml/cakeml-src/'


def strip_comments(s):
  """remove (* ... *) comments, respecting nesting and strings"""
  out = []; i = 0; depth = 0; n = len(s)
  while i < n:
    if s.startswith('(*', i):
      depth += 1; i += 2; continue
    if s.startswith('*)', i) and depth:
      depth -= 1; i += 2; continue
    if depth == 0 and s[i] == '"':
      j = i + 1
      while j < n and s[j] != '"':
        j += 2 if s[j] == '\\' else 1
      out.append(s[i:j+1]); i = j + 1; continue
    if depth == 0:
      out.append(s[i])
    elif s[i] == '\n':
      out.append('\n')
    i += 1
  return ''.join(out)


# a relation that a source defines with ML code: the rules are a
# quotation in which a symbol stands for the relation, and HOL4
# replaces it by the name of the relation before parsing
HOL_RELN = re.compile(
    r'val\s*\(\s*(\w+)_rules\s*,\s*\w+_ind\s*,\s*\w+_cases'
    r'\s*\)\s*=(.*?)`(.*)`\s*;?\s*$', re.S)
REPLACE_QUOTE = re.compile(r'replace_quote\s*"([^"]*)"\s*"([^"]*)"')


def unescape_ml(s):
  """an ML string literal with the decimal escapes that a HOL4
     source uses for a character outside ASCII"""
  out = bytearray()
  i = 0
  while i < len(s):
    m = re.match(r'\\(\d{1,3})', s[i:])
    if m:
      out.append(int(m.group(1))); i += m.end()
    else:
      out += s[i].encode('utf-8'); i += 1
  return out.decode('utf-8', 'replace')


DECLARE_MONAD = re.compile(
    r'declare_monad\s*\(\s*"([^"]*)"\s*,\s*\{(.*?)\}\s*\)', re.S)
ENABLE_MONAD = re.compile(
    r'(?:temp_)?enable_monad\s*\(?\s*"([^"]*)"')
MONAD_FIELD = re.compile(
    r"(\w+)\s*=\s*(?:SOME\s*)?(?:``|\u201c)\s*\$?([^`\u201d]*?)\s*"
    r"(?:``|\u201d)")


def monad_decls(text):
  """the monads that an ML block declares: the name and the terms
     of its fields (bind, unit, ignorebind, ...)"""
  out = []
  for m in DECLARE_MONAD.finditer(text):
    flds = dict(MONAD_FIELD.findall(m.group(2)))
    if 'NONE' in m.group(2):
      # a field that is NONE has no term
      for f in re.findall(r'(\w+)\s*=\s*NONE', m.group(2)):
        flds.pop(f, None)
    out.append((m.group(1), flds))
  return out


def monad_enabled(text):
  """the monad that an ML block enables, if any; HOL4's option
     monad syntax is a monad of its own"""
  if 'add_option_monadsyntax' in text: return 'option'
  m = ENABLE_MONAD.search(text)
  return m.group(1) if m else None


ML_TERM = re.compile(r"val\s+([A-Za-z0-9_']+)\s*=\s*"
                     r"(?:``|\u201c)(.*?)(?:``|\u201d)", re.S)


def ml_terms(text):
  """the terms that an ML block keeps in a value, which the source
     may antiquote into a definition (dataSem's ^s)"""
  return [(m.group(1), m.group(2).strip())
          for m in ML_TERM.finditer(text)]


def hol_reln(text):
  """the name and the rules of an ML block that calls Hol_reln"""
  m = HOL_RELN.match(text.strip())
  if not m or 'Hol_reln' not in m.group(2): return None
  body = m.group(3)
  for frm, to in REPLACE_QUOTE.findall(m.group(2)):
    body = body.replace(unescape_ml(frm), to)
  return m.group(1), body


class Block:
  def __init__(self, kind, name, attrs, body, extra=None, text=''):
    self.kind = kind      # Theory Ancestors Libs Datatype Definition
                          # Inductive Theorem Type Overload ML Comment
    self.name = name
    self.attrs = attrs    # list of strings
    self.body = body      # main text (term)
    self.extra = extra    # termination text / proof text
    self.text = text      # the original text of the block

  def __repr__(self):
    return f'<{self.kind} {self.name}>'


HEAD = re.compile(r'''^(Theory|Ancestors|Libs|Datatype|Definition|
    Inductive|CoInductive|Theorem|Triviality|Type|Overload|
    Datatype)\b''', re.X)


def sml_string(s):
  """the value of an SML string literal body (\\ddd is a byte)"""
  out = bytearray()
  i = 0
  while i < len(s):
    if s[i] == '\\' and i + 3 < len(s) and s[i+1:i+4].isdigit():
      out.append(int(s[i+1:i+4])); i += 4
    elif s[i] == '\\':
      out.append(ord(s[i+1])); i += 2
    else:
      out.extend(s[i].encode('utf-8')); i += 1
  return out.decode('utf-8', 'replace')


FIXITY = re.compile(r'(temp_)?set_fixity\s*"((?:[^"\\]|\\.)*)"\s*'
                    r'\(\s*(Infixl|Infixr|Infix)\s*'
                    r'(?:\(\s*(LEFT|RIGHT|NONASSOC)\s*,\s*)?(\d+)')
ADD_INFIX = re.compile(r'(temp_)?add_infix\s*\(\s*'
                       r'"((?:[^"\\]|\\.)*)"\s*,'
                       r'\s*(\d+)\s*,\s*(?:\w+\.)?'
                       r'(LEFT|RIGHT|NONASSOC)')
# the fields of a set_mapped_fixity record come in either order
# (pegTheory writes the fixity before the token)
MAPPED_FIXITY = re.compile(
  r'(temp_)?set_mapped_fixity\s*\{([^}]*)\}', re.S)
MAPPED_TOK = re.compile(r'tok\s*=\s*"((?:[^"\\]|\\.)*)"')
MAPPED_FIX = re.compile(r'fixity\s*=\s*(Infixl|Infixr|Infix)\s*'
                        r'(?:\(\s*(LEFT|RIGHT|NONASSOC)\s*,\s*)?'
                        r'(\d+)')


def fixities(text):
  """the infixes that the ML declarations of a HOL4 source add, as
     (token, precedence, associativity, temporary); a temporary one
     does not reach the theories that descend from this one"""
  out = []
  pairs = [m.groups() for m in FIXITY.finditer(text)]
  for m in MAPPED_FIXITY.finditer(text):
    mt = MAPPED_TOK.search(m.group(2))
    mf = MAPPED_FIX.search(m.group(2))
    if mt and mf:
      pairs.append((m.group(1), mt.group(1), mf.group(1),
                    mf.group(2), mf.group(3)))
  for temp, tok, kind, ass, prec in pairs:
    a = 'l' if kind == 'Infixl' else 'r' if kind == 'Infixr' else \
        {'LEFT': 'l', 'RIGHT': 'r'}.get(ass, 'n')
    out.append((sml_string(tok), int(prec), a, bool(temp)))
  for m in ADD_INFIX.finditer(text):
    temp, tok, prec, ass = m.groups()
    out.append((sml_string(tok), int(prec),
                {'LEFT': 'l', 'RIGHT': 'r'}.get(ass, 'n'), bool(temp)))
  return out


EQ_MODE = re.compile(r'\b(?:temp_)?(loose|tight)_equality\b')


def pmatch_mode(text):
  """does a block enable the pmatch syntax of HOL4's patternMatches
     library?"""
  return 'enable_pmatch' in text


def equality_mode(text):
  """a loose_equality or tight_equality declaration of a block"""
  m = EQ_MODE.search(text)
  return m.group(1) if m else None


# an old style definition in ML: Define, tDefine, a qualified one
# (TotalDefn.tDefine) or a wrapper that a source writes itself
# (data_to_word's assign_Define, which only keeps the theorem in a
# list as well), with new_definition as the other form
ML_DEF = re.compile(r"""^val\s+([A-Za-z0-9_']+)\s*=\s*
                        (?:[A-Za-z0-9_.]+\s+)*?
                        (?:[A-Za-z0-9_.]*[txzq]?Define\b
                           \s*("[^"]*")?\s*
                          |new_(?:binder_|infixr_|infixl_)?definition
                           \s*\(\s*"[^"]*"\s*,\s*)""", re.X)


def ml_definition(text):
  """an old style HOL4 definition in ML (Define, tDefine, ...) as a
     Definition block, so that it is ported like the others"""
  m = ML_DEF.match(text)
  if not m: return None
  # a quotation of HOL4 is `...`, ``...``, “...” or ‘...’
  i = min([k for k in (text.find(q, m.end())
                       for q in ('`', '“', '‘')) if k >= 0]
          or [-1])
  if i < 0: return None
  if text[i] == '“':
    j = text.find('”', i + 1)
    body, rest = text[i+1:j], text[j+1:]
  elif text[i] == '‘':
    j = text.find('’', i + 1)
    body, rest = text[i+1:j], text[j+1:]
  elif text[i:i+2] == '``':
    j = text.find('``', i + 2)
    body, rest = text[i+2:j], text[j+2:]
  else:
    j = text.find('`', i + 1)
    body, rest = text[i+1:j], text[j+1:]
  if j < 0: return None
  rest = rest.strip()
  if rest.endswith(';'): rest = rest[:-1].strip()
  # the closing parenthesis of a new_definition call, or the
  # termination tactic of a tDefine
  while rest.startswith(')') or rest.endswith(')'):
    if rest.startswith('('): break
    rest = (rest[1:] if rest.startswith(')') else rest[:-1]).strip()
  if rest.startswith('(') and rest.endswith(')'): rest = rest[1:-1]
  # the name of the val may say nothing (data_to_word writes every
  # one of its assign_Define definitions to a val called def), so
  # the name of the block is the one of the constant it defines
  name = m.group(1)
  if not name.endswith('_def'):
    try:
      name = definition_names(body)[0] + '_def'
    except Exception:
      pass
  return Block('Definition', name, [], body, rest or None,
               text=text)


def in_quote(text):
  """is this text in the middle of a term quotation?"""
  if text.count('“') > text.count('”'): return True
  if text.count('‘') > text.count('’'): return True
  s = text.replace('``', '`')
  return s.count('`') % 2 == 1


def blanks_before(lines, i):
  """the number of blank lines just before line i"""
  k = 0
  while i - k - 1 >= 0 and not lines[i-k-1].strip(): k += 1
  return k


def parse(path):
  """returns the list of blocks of a Script.sml file"""
  src = open(path, encoding='utf-8').read()
  lines = src.split('\n')
  # a comment on the line that closes a block (as in "End(* ... *)"
  # or "End (*catchall*)") becomes a line of its own, so that the
  # block is recognized
  def split_end(line):
    m = re.match(r'^(End|QED)\s*\(\*', line)
    if not m: return [line]
    return [line[:m.end(1)], line[m.end(1):].lstrip()]

  lines = [l for line in lines for l in split_end(line)]
  # every block records the line it starts at, so that the port can
  # keep the blank lines of the source between the blocks
  cur = [0]
  class Blocks(list):
    def append(self, b):
      b.line = cur[0]
      b.blanks = blanks_before(lines, cur[0])
      list.append(self, b)
  blocks = Blocks()
  i = 0
  n = len(lines)
  while i < n:
    cur[0] = i
    line = lines[i]
    # comments are kept, as they have to end up in the port
    if line.lstrip().startswith('(*'):
      j = i; depth = 0
      while j < n:
        depth += lines[j].count('(*') - lines[j].count('*)')
        j += 1
        if depth <= 0: break
      text = '\n'.join(lines[i:j])
      blocks.append(Block('Comment', None, [], text, text=text))
      i = j; continue
    m = HEAD.match(line)
    if not m:
      if line.strip():
        j = i
        while j < n:
          # a comment or a blank line inside a quotation belongs to
          # the block (the definitions that data_to_word makes with
          # assign_Define have comments in them)
          acc = '\n'.join(lines[i:j])
          # a definition in ML may have its comments between the
          # call and the quotation (multiword's mw_div_loop)
          if in_quote(acc) or (ML_DEF.match(acc) and
                               not re.search('[`“‘]', acc)):
            j += 1; continue
          if not lines[j].strip() or HEAD.match(lines[j]) or \
             lines[j].lstrip().startswith('(*'):
            break
          j += 1
        text = '\n'.join(lines[i:j])
        b = ml_definition(text)
        if b is None:
          # an old style inductive definition (indexedLists' and
          # walkstar's are a val of the three theorems that
          # Hol_reln gives) is an Inductive block
          r = hol_reln(text)
          if r:
            b = Block('Inductive', r[0] + '_rules', [], r[1], text=text)
        blocks.append(b if b else Block('ML', None, [], text, text=text))
        i = j
      else:
        i += 1
      continue
    kind = m.group(1)
    if kind in ('Theory',):
      blocks.append(Block('Theory', line.split()[1], [], '', text=line))
      i += 1; continue
    if kind in ('Ancestors', 'Libs'):
      j = i + 1
      while j < n and (lines[j].startswith(' ') or lines[j].startswith('\t')) \
          and lines[j].strip():
        j += 1
      blocks.append(Block(kind, None, [], '\n'.join(lines[i+1:j]),
                          text='\n'.join(lines[i:j])))
      i = j; continue
    if kind in ('Type', 'Overload'):
      # Type name = “:ty”   (may continue on following lines)
      j = i + 1
      while j < n and not HEAD.match(lines[j]) and lines[j].strip() \
          and not lines[j].lstrip().startswith('(*'):
        j += 1
      text = '\n'.join(lines[i:j])
      # the name is a word, or any token in quotes (a symbolic
      # infix the source overloads with a constant)
      mm = re.match(r'^\w+\s+(?:([A-Za-z0-9_\']+)|"([^"]*)")'
                    r'\s*(\[[^\]]*\])?\s*=\s*(.*)$', text, re.S)
      name = (mm.group(1) or mm.group(2)) if mm else None
      attrs = ((mm.group(3) or '')[1:-1].split(',')
               if mm and mm.group(3) else [])
      body = mm.group(4) if mm else ''
      blocks.append(Block(kind, name, attrs, body.strip(), text=text))
      i = j; continue
    # Theorem name = term is a one line form without Proof and QED
    if kind in ('Theorem', 'Triviality') and \
       re.match(r'^\w+\s+[A-Za-z0-9_\']+\s*(\[[^\]]*\])?\s*=', line):
      j = i + 1
      while j < n and lines[j].strip() and not HEAD.match(lines[j]) \
          and not lines[j].lstrip().startswith('(*'):
        j += 1
      text = '\n'.join(lines[i:j])
      blocks.append(Block('ThmValue', None, [], text, text=text))
      i = j; continue
    # block structures ending in End or QED
    if kind in ('Datatype', 'Definition', 'Inductive', 'CoInductive'):
      endkw = 'End'
    else:
      endkw = 'QED'
    j = i
    while j < n and lines[j].rstrip() != endkw:
      j += 1
    text = '\n'.join(lines[i:j+1])
    head = lines[i]
    mm = re.match(r'^\w+\s*([A-Za-z0-9_\'\$]*)\s*(\[[^\]]*\])?\s*[:=]?\s*(.*)$',
                  head)
    name = mm.group(1) or None
    attrs = (mm.group(2) or '')[1:-1].split(',') if mm.group(2) else []
    body = '\n'.join([mm.group(3)] + lines[i+1:j])
    extra = None
    # the rules of an Inductive may be labelled ([~Number:] on a
    # line of its own), which is a name for the rule, not syntax
    if kind in ('Inductive', 'CoInductive'):
      # the label separates the rules, and each of them is a
      # conjunct of its own: without the parentheses the
      # quantifier of a rule would reach over the ones after it
      rules = [[]]
      for l in body.split('\n'):
        # the label may be on a line of its own or in front of the
        # rule (data_to_word_memoryProof's [~unchanged:])
        # a rule that has no name of its own may be separated by
        # a label that is the conjunction itself (clos_opProof's
        # red_rel has four of them)
        m = re.match(r"^\s*\[(?:[~^]?[A-Za-z0-9_']*:|∧)\]"
                     r"\s*(.*)$", l)
        if m:
          rules.append([])
          if m.group(1).strip(): rules[-1].append(m.group(1))
        else:
          rules[-1].append(l)
      rs = [r for r in ('\n'.join(x) for x in rules) if r.strip()]
      if len(rs) > 1:
        body = ' /\\\n'.join('(' + r.strip() + ')' for r in rs)
      elif rs:
        body = rs[0]
    if kind == 'Definition':
      k = body.find('\nTermination')
      if k >= 0:
        extra = body[k+len('\nTermination'):]
        body = body[:k]
    if kind in ('Theorem', 'Triviality'):
      k = body.find('\nProof')
      if k >= 0:
        extra = body[k+len('\nProof'):]
        body = body[:k]
    blocks.append(Block(kind, name, attrs, body, extra, text=text))
    i = j + 1
  return quotation_definitions(blocks)


# a definition that HOL4 makes in ML from a quotation that it keeps
# in a value, so that it can also make the pmatch version of it:
#
#   local val foo_quotation = `foo x = ...`
#   in val foo_def = Define foo_quotation ... end

QUOTATION = re.compile(r"(?:local\s+)?val\s+([A-Za-z0-9_']+)"
                       r"\s*=\s*`", re.S)
QUOT_DEF = re.compile(r"val\s+([A-Za-z0-9_']+)_def\s*=\s*"
                      r"[txzq]?Define\s+([A-Za-z0-9_']+)"
                      r"(?![A-Za-z0-9_'])", re.S)


def quotation_definitions(blocks):
  quots = {}
  for b in blocks:
    if b.kind != 'ML': continue
    m = QUOTATION.match(b.text.strip())
    if m:
      t = b.text.strip()
      i = t.index('`', m.end() - 1)
      j = t.find('`', i + 1)
      if j > 0: quots[m.group(1)] = (b, t[i+1:j])
  out = []
  for b in blocks:
    m = b.kind == 'ML' and QUOT_DEF.search(b.text)
    if m and m.group(2) in quots:
      qb, body = quots[m.group(2)]
      out = [x for x in out if x is not qb]
      nb = Block('Definition', m.group(1) + '_def', [], body,
                 None, text=qb.text + b.text)
      nb.blanks = getattr(qb, 'blanks', 1)
      out.append(nb)
    else:
      out.append(b)
  return out


# ---------------------------------------------------------------
# extracting the names that a block defines
# ---------------------------------------------------------------

IDENT = r"[A-Za-z][A-Za-z0-9_']*"


def datatype_names(body):
  """returns [(tyname, [constructors], [fields])] of a Datatype block"""
  body = strip_comments(body)
  res = []
  # split into the separate type definitions, which are separated by ;
  parts = split_top(body, ';')
  for part in parts:
    if not part.strip(): continue
    mm = re.match(r'\s*(' + IDENT + r')\s*=\s*(.*)$', part, re.S)
    if not mm: continue
    ty = mm.group(1); rhs = mm.group(2).strip()
    if rhs.startswith('<|'):
      flds = [f.split(':')[0].strip()
              for f in split_top(rhs[2:rhs.rindex('|>')], ';')
              if f.strip()]
      res.append((ty, [], flds))
    else:
      cons = []
      for alt in split_top(rhs, '|'):
        alt = alt.strip()
        if not alt: continue
        m2 = re.match(r'(' + IDENT + r')', alt)
        if m2: cons.append(m2.group(1))
      res.append((ty, cons, []))
  return res


def split_top(s, sep):
  """split on sep, but not inside brackets or quotations"""
  out = []; depth = 0; cur = ''
  i = 0
  while i < len(s):
    c = s[i]
    if c in '([{': depth += 1
    elif c in ')]}': depth -= 1
    elif c == '<' and s[i:i+2] == '<|': depth += 1; cur += '<|'; i += 2; continue
    elif c == '|' and s[i:i+2] == '|>': depth -= 1; cur += '|>'; i += 2; continue
    if c == sep and depth == 0:
      out.append(cur); cur = ''; i += 1; continue
    cur += c; i += 1
  out.append(cur)
  return out


def definition_names(body):
  """the function names defined by a Definition block"""
  body = strip_comments(body)
  names = []
  for cl in split_clauses(body):
    cl = cl.strip()
    if not cl: continue
    cl = re.sub(r'^\s*[!∀][^.]*\.', '', cl)   # drop leading quantifier
    cl = cl.lstrip()
    m = re.match(r'\(?\s*(' + IDENT + r')', cl)
    if m and m.group(1) not in ('if', 'let', 'case'):
      names.append(m.group(1))
  out = []
  for x in names:
    if x not in out: out.append(x)
  return out


def split_clauses(body):
  """split a definition body into its clauses (on top level ∧ / /\\)"""
  parts = [body]
  for sep in ['∧', '/\\']:
    new = []
    for p in parts: new += split_top_str(p, sep)
    parts = new
  return parts


def split_top_str(s, sep):
  out = []; depth = 0; cur = ''; i = 0
  while i < len(s):
    c = s[i]
    if s.startswith(sep, i) and depth == 0:
      out.append(cur); cur = ''; i += len(sep); continue
    if c in '([{': depth += 1
    elif c in ')]}': depth -= 1
    cur += c; i += 1
  out.append(cur)
  return out


# the monadic state machinery that HOL4's ml_monadBaseLib makes
# with ML code: the accessors of a state record, the manipulators
# of its fixed size arrays, the functions of its exception type
# and the run function of an initial state (reg_alloc and
# linear_scan use all four).  tools/port.py writes out the
# definitions that it makes; tools/db.py uses the same patterns to
# know which constants those are

MONAD_ACCESS_FUNS = re.compile(
  r'define_monad_access_funs\s*(?:``|“)'
  r'\s*:\s*([A-Za-z0-9_\']+)')
MONAD_EXN_FUNS = re.compile(
  r'define_monad_exception_functions\s*'
  r'(?:``|“)\s*:\s*([A-Za-z0-9_\']+)'
  r'(?:``|”)\s*(?:``|“)\s*:\s*([A-Za-z0-9_\']+)')
MONAD_ARR_FUNS = re.compile(
  r'define_MFarray_manip_funs\s*\[([^\]]*)\]\s*(\w+)\s*(\w+)', re.S)
MONAD_RUN_FUN = re.compile(
  r'define_run\s*(?:``|“)\s*:\s*([A-Za-z0-9_\']+)'
  r'(?:``|”)\s*(\w+)\s*"([^"]*)"', re.S)
MONAD_ARR_NAMES = re.compile(
  r'val\s+array_fields_names\s*=\s*\[([^\]]*)\]', re.S)
