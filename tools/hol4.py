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
MAPPED_FIXITY = re.compile(
  r'(temp_)?set_mapped_fixity\s*\{[^}]*?'
  r'tok\s*=\s*"((?:[^"\\]|\\.)*)"'
  r'[^}]*?fixity\s*=\s*(Infixl|Infixr|Infix)\s*'
  r'(?:\(\s*(LEFT|RIGHT|NONASSOC)\s*,\s*)?(\d+)', re.S)


def fixities(text):
  """the infixes that the ML declarations of a HOL4 source add, as
     (token, precedence, associativity, temporary); a temporary one
     does not reach the theories that descend from this one"""
  out = []
  for m in list(FIXITY.finditer(text)) + \
           list(MAPPED_FIXITY.finditer(text)):
    temp, tok, kind, ass, prec = m.groups()
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


ML_DEF = re.compile(r"""^val\s+([A-Za-z0-9_']+)\s*=\s*
                        (?:[txz]?Define\b\s*("[^"]*")?\s*
                          |new_(?:binder_|infixr_|infixl_)?definition
                           \s*\(\s*"[^"]*"\s*,\s*)""", re.X)


def ml_definition(text):
  """an old style HOL4 definition in ML (Define, tDefine, ...) as a
     Definition block, so that it is ported like the others"""
  m = ML_DEF.match(text)
  if not m: return None
  i = text.find('`', m.end())
  if i < 0: return None
  if text[i:i+2] == '``':
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
  return Block('Definition', m.group(1), [], body, rest or None,
               text=text)


def blanks_before(lines, i):
  """the number of blank lines just before line i"""
  k = 0
  while i - k - 1 >= 0 and not lines[i-k-1].strip(): k += 1
  return k


def parse(path):
  """returns the list of blocks of a Script.sml file"""
  src = open(path, encoding='utf-8').read()
  lines = src.split('\n')
  # a comment on the line that closes a block (as in "End(* ... *)")
  # becomes a line of its own, so that the block is recognized
  lines = [l for line in lines
             for l in (re.split(r'(?<=^End)(?=\(\*)|(?<=^QED)(?=\(\*)',
                                line)
                       if re.match(r'^(End|QED)\(\*', line) else [line])]
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
        while j < n and lines[j].strip() and not HEAD.match(lines[j]) \
            and not lines[j].lstrip().startswith('(*'):
          j += 1
        text = '\n'.join(lines[i:j])
        b = ml_definition(text)
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
      mm = re.match(r'^\w+\s+([A-Za-z0-9_\']+)\s*(\[[^\]]*\])?\s*=\s*(.*)$',
                    text, re.S)
      name = mm.group(1) if mm else None
      attrs = (mm.group(2) or '')[1:-1].split(',') if mm and mm.group(2) else []
      body = mm.group(3) if mm else ''
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
  return blocks


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
