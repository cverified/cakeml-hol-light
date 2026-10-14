"""HOL4 term syntax -> HOL Light term syntax.

tokenize/parse a HOL4 term and print it as a HOL Light term,
keeping the line structure of the original.
"""
import re, sys

# ---------------------------------------------------------------
# tokens
# ---------------------------------------------------------------

UNI = {
  '∧': '/\\', '∨': '\\/', '¬': '~', '⇒': '==>', '⇔': '<=>',
  '∀': '!', '∃': '?', 'λ': '\\', '≤': '<=', '≥': '>=', '≠': '<>',
  '∈': 'IN', '∉': 'NOTIN', '⊆': 'SUBSET', '∪': 'UNION', '∩': 'INTER',
  '∅': '{}', '⧺': '++', '∘': 'o', '−': '-', '×': '*', '≼': '<<=',
  '⊂': 'PSUBSET', '≥': '>=', '⊕': 'XOR',
}

GREEK = dict(zip('αβγδεζηθ'
                 'ικμνξοπρ'
                 'στυφχψω',
                 ["'g" + c for c in 'abcdefghijklmnopqrstuvw']))

KEYWORDS = ['if', 'then', 'else', 'let', 'and', 'in', 'case', 'of',
            'do', 'od', 'with', 'otherwise', 'some']

# symbols, longest first
SYMS = ['<=>', '==>', '>>>', '#>>', '#<<', '<=+', '>=+', '||', '&&',
        "''", '--', '%%',
        '??', '|->', '<|', '|>', ':=', '<-', '->', '=>', '::', '++',
        '<<', '>>', '@@', '**', '|+', '/\\', '\\/', '<>', '<=', '>=',
        '<+', '>+', '=+', '<*>', '<<=', '≼', '«', '»', '⟪', '⟫',
        '𝕌', 'univ',
        '(', ')', '[', ']', '{', '}', ',', ';', '.', '|', '=', '<',
        '>', '+', '-', '*', '/', '~', '!', '?', '\\', ':', '$', '&',
        '^', '#', '@', '%', '§', '><']


class Tok:
  def __init__(self, kind, text, pos, nl, indent):
    self.kind = kind     # id num str chr sym key
    self.text = text
    self.pos = pos
    self.nl = nl         # number of newlines before this token
    self.indent = indent # the column of this token

  def __repr__(self):
    return f'{self.kind}:{self.text}'


def tokenize(s):
  toks = []
  i = 0
  n = len(s)
  nl = 0
  col = 0
  while i < n:
    c = s[i]
    if c == '\n':
      nl += 1; i += 1; col = 0; continue
    if c in ' \t':
      i += 1; col += 1; continue
    if s.startswith('(*', i):
      depth = 1; j = i + 2
      while j < n and depth:
        if s.startswith('(*', j): depth += 1; j += 2
        elif s.startswith('*)', j): depth -= 1; j += 2
        else:
          if s[j] == '\n': nl += 1
          j += 1
      i = j; continue
    start = i; icol = col
    if c in UNI:
      t = UNI[c]
      toks.append(Tok('key' if t in KEYWORDS else 'sym', t, start, nl, icol))
      i += 1; col += 1; nl = 0; continue
    if c == '«':
      j = s.index('»', i)
      toks.append(Tok('mlstr', s[i+1:j], start, nl, icol))
      i = j + 1; nl = 0; continue
    if c == '⟪':
      j = s.index('⟫', i)
      toks.append(Tok('quoted', s[i+1:j], start, nl, icol))
      i = j + 1; nl = 0; continue
    if c == '"':
      j = i + 1
      while j < n and s[j] != '"':
        j += 2 if s[j] == '\\' else 1
      toks.append(Tok('str', s[i:j+1], start, nl, icol))
      i = j + 1; col += j + 1 - start; nl = 0; continue
    if c == '#' and i + 1 < n and s[i+1] == '"':
      j = i + 2
      while j < n and s[j] != '"':
        j += 2 if s[j] == '\\' else 1
      toks.append(Tok('chr', s[i:j+1], start, nl, icol))
      i = j + 1; col += j + 1 - start; nl = 0; continue
    if c.isdigit():
      j = i
      while j < n and (s[j].isalnum() or s[j] == '_'): j += 1
      toks.append(Tok('num', s[i:j], start, nl, icol))
      i = j; col += j - i; nl = 0; continue
    if c in GREEK:
      toks.append(Tok('tyvar', GREEK[c], start, nl, icol))
      i += 1; col += 1; nl = 0; continue
    if c == '𝕌':
      toks.append(Tok('sym', '𝕌', start, nl, icol))
      i += 1; col += 1; nl = 0; continue
    if c.isalpha() or c == '_':
      j = i
      while j < n and (s[j].isalnum() or s[j] in "_'"): j += 1
      # qualified name thy$name
      if j < n and s[j] == '$' and j + 1 < n and (s[j+1].isalpha()
                                                  or s[j+1] == '_'):
        j += 1
        while j < n and (s[j].isalnum() or s[j] in "_'"): j += 1
      w = s[i:j]
      toks.append(Tok('key' if w in KEYWORDS else 'id', w, start, nl, icol))
      i = j; col += j - i; nl = 0; continue
    if s.startswith("''", i):
      toks.append(Tok('sym', "''", start, nl, icol))
      i += 2; col += 2; nl = 0; continue
    if c == "'" and not (i + 1 < n and (s[i+1].isalnum()
                                       or s[i+1] == '_')):
      toks.append(Tok('sym', "'", start, nl, icol))
      i += 1; col += 1; nl = 0; continue
    if c == "'":                      # type variable
      j = i + 1
      while j < n and (s[j].isalnum() or s[j] in "_'"): j += 1
      toks.append(Tok('tyvar', s[i:j], start, nl, icol))
      i = j; nl = 0; continue
    for sym in SYMS:
      if s.startswith(sym, i):
        toks.append(Tok('sym', sym, start, nl, icol))
        i += len(sym); col += len(sym); nl = 0; break
    else:
      raise SyntaxError(f'tokenize: {s[i:i+20]!r}')
  toks.append(Tok('eof', '', n, nl, 0))
  return toks


# ---------------------------------------------------------------
# the operator table: HOL4 precedence, associativity, HOL Light
# precedence and name
# ---------------------------------------------------------------
#    hol4 name : (hol4 prec, assoc, hol light name, hol light prec)

INFIX = {
  ',':     (50,  'r', ',',      14),
  '<=>':   (100, 'r', '<=>',     2),
  '==>':   (200, 'r', '==>',     4),
  '\\/':   (300, 'r', '\\/',     6),
  '/\\':   (400, 'r', '/\\',     8),
  '=':     (450, 'n', '=',      12),
  '<>':    (450, 'n', '<>',     12),
  '<':     (450, 'n', '<',      12),
  '>':     (450, 'n', '>',      12),
  '<=':    (450, 'n', '<=',     12),
  '>=':    (450, 'n', '>=',     12),
  'IN':    (450, 'n', 'IN',     11),
  'NOTIN': (450, 'n', 'NOTIN',  11),
  'SUBSET':(450, 'n', 'SUBSET', 12),
  'PSUBSET':(450,'n', 'PSUBSET',12),
  '<<=':   (450, 'n', '<<=',    12),
  '<+':    (450, 'n', '<+',     12),
  '>+':    (450, 'n', '>+',     12),
  '<=+':   (450, 'n', '<=+',    12),
  '>=+':   (450, 'n', '>=+',    12),
  '|+':    (500, 'l', '|+',     15),
  '|->':   (100, 'n', '|->',    13),
  '++':    (480, 'l', '++',     16),
  '::':    (490, 'r', '::',     15),
  '+':     (500, 'l', '+',      16),
  '-':     (500, 'l', '-',      18),
  'UNION': (500, 'l', 'UNION',  16),
  'INTER': (600, 'l', 'INTER',  20),
  'DIFF':  (500, 'l', 'DIFF',   18),
  'INSERT':(490, 'r', 'INSERT', 21),
  '*':     (600, 'l', '*',      20),
  '/':     (600, 'l', '/',      22),
  'DIV':   (600, 'l', 'DIV',    22),
  'MOD':   (650, 'l', 'MOD',    22),
  '**':    (700, 'r', 'EXP',    24),
  'EXP':   (700, 'r', 'EXP',    24),
  '&&':    (650, 'l', '&&',     20),
  '||':    (650, 'l', '||',     16),
  '??':    (650, 'l', '??',     16),
  '<<':    (680, 'l', '<<',     23),
  '>>':    (680, 'l', '>>',     23),
  '>>>':   (680, 'l', '>>>',    23),
  '#>>':   (680, 'l', '#>>',    23),
  '#<<':   (680, 'l', '#<<',    23),
  '@@':    (700, 'l', '@@',     23),
  'o':     (800, 'r', 'o',      26),
  "'":     (2000, 'l', 'FAPPLY', 0),
  "''":    (350, 'l', 'word_slice', 0),
  '--':    (350, 'l', 'word_bits', 0),
  '%%':    (400, 'l', 'word_bit', 0),
  '=+':    (715, 'l', '=+',     23),
  '><':    (350, 'l', '><',     23),
  '<*>':   (500, 'l', '<*>',    16),
}

PREFIX = {'~': (900, '~'), '-': (900, '--')}

QUANTS = {'!': '!', '?': '?', '?!': '?!', '@': '@', '\\': '\\'}

APP = 2000
PRE_APP = 1900       # HOL Light: application binds tightest
EOFPREC = 0


# ---------------------------------------------------------------
# the syntax tree
# ---------------------------------------------------------------

class Node:
  def __init__(self, kind, tok=None, **kw):
    self.kind = kind
    self.tok = tok
    self.__dict__.update(kw)

  def __repr__(self):
    d = {k: v for k, v in self.__dict__.items() if k not in ('tok',)}
    return f'{d}'


STOP = {')', ']', '}', '|', ';', '=>', 'of', 'then', 'else', 'in',
        'od', '|>', 'and', '.', '->', ':=', '<-', '»', '⟫', ','}


class Parser:
  def __init__(self, toks, ctx=None):
    self.toks = toks
    self.i = 0
    self.ctx = ctx          # the translation context (names, records)

  def peek(self, k=0):
    return self.toks[min(self.i + k, len(self.toks) - 1)]

  def next(self):
    t = self.toks[self.i]; self.i += 1; return t

  def expect(self, text):
    t = self.next()
    if t.text != text:
      raise SyntaxError(f'expected {text!r} but found {t.text!r} '
                        f'at {t.pos}')
    return t

  def at(self, text):
    return self.peek().text == text and self.peek().kind in ('sym', 'key')

  # -- types ------------------------------------------------------

  def parse_type(self):
    """a type, as a list of tokens"""
    out = []
    depth = 0
    while True:
      t = self.peek()
      if t.kind == 'eof': break
      if t.text in ('(', '[') :
        depth += 1
      elif t.text in (')', ']'):
        if depth == 0: break
        depth -= 1
      elif depth == 0 and (t.text in STOP and t.text not in ('->',)
                           or t.kind == 'num' and False):
        break
      elif depth == 0 and t.kind == 'key':
        break
      out.append(t); self.next(); continue
      out.append(t); self.next()
    return out

  # -- terms ------------------------------------------------------

  def parse(self, prec=0):
    e = self.parse_atoms()
    return self.parse_infix(e, prec)

  def parse_infix(self, e, prec):
    while True:
      t = self.peek()
      if t.kind not in ('sym', 'id', 'key'): break
      op = t.text
      if op not in INFIX: break
      p, assoc, _, _ = INFIX[op]
      if p < prec: break
      self.next()
      if assoc == 'n' and self.ctx is not None:
        pass
      rprec = p + 1 if assoc in ('l', 'n') else p
      r = self.parse_atoms()
      r = self.parse_infix(r, rprec)
      e = Node('infix', tok=t, op=op, l=e, r=r)
    return e

  def starts_atom(self, arg=False):
    """arg: in the position of an argument of an application, where a
       prefix operator does not start a new argument"""
    t = self.peek()
    if t.kind in ('id', 'num', 'str', 'chr', 'tyvar', 'mlstr',
                  'quoted'):
      return not (t.text in INFIX and t.kind == 'id')
    if t.kind == 'key':
      return t.text in ('if', 'let', 'case', 'do', 'some')
    if t.kind == 'sym':
      if t.text in ('(', '[', '{', '$', '&', '<|', '«', '⟪',
                    '𝕌'):
        return True
      if t.text == '~': return True
      return not arg and t.text in ('!', '?', '\\', '@', '-', '^')
    return False

  def parse_atoms(self):
    e = self.parse_fields(self.parse_atom())
    while self.starts_atom(True):
      a = self.parse_fields(self.parse_atom())
      e = Node('app', tok=e.tok, fn=e, arg=a)
    e = self.parse_postfix(e)
    if self.at(':'):
      self.next()
      ty = self.parse_type()
      e = Node('typed', tok=e.tok, e=e, ty=ty)
    return e

  def parse_fields(self, e):
    while self.peek().text == '.' and self.peek(1).kind == 'id':
      t = self.next(); fld = self.next()
      e = Node('field', tok=t, e=e, fld=fld.text)
    return e

  def parse_postfix(self, e):
    while True:
      t = self.peek()
      if t.text == 'with':
        self.next()
        if self.at('<|'):
          self.next()
          upds = self.parse_updates()
          self.expect('|>')
        else:
          upds = self.parse_updates(single=True)
        e = Node('recupd', tok=t, e=e, upds=upds)
      else:
        break
    return e

  def parse_updates(self, single=False):
    upds = []
    while True:
      fld = self.next()
      self.expect(':=')
      v = self.parse(60)
      upds.append((fld.text, v))
      if single or not self.at(';'): break
      self.next()
    return upds

  def parse_binders(self):
    vs = []
    while not self.at('.'):
      t = self.peek()
      if t.text == '(':
        vs.append(self.parse_atom())
      elif t.kind == 'id':
        self.next()
        vs.append(Node('id', tok=t, name=t.text))
      elif t.text == '_':
        self.next()
        vs.append(Node('id', tok=t, name='_'))
      else:
        raise SyntaxError(f'binder expected at {t.pos}: {t.text!r}')
    self.expect('.')
    return vs

  def parse_atom(self):
    t = self.next()
    if t.kind == 'num':
      return Node('num', tok=t, text=t.text)
    if t.kind == 'str':
      return Node('str', tok=t, text=t.text)
    if t.kind == 'chr':
      return Node('chr', tok=t, text=t.text)
    if t.kind == 'id':
      return Node('id', tok=t, name=t.text)
    if t.kind == 'tyvar':
      return Node('id', tok=t, name=t.text)
    if t.kind == 'key':
      if t.text == 'if':
        c = self.parse(0); self.expect('then')
        a = self.parse(0); self.expect('else')
        b = self.parse(0)
        return Node('cond', tok=t, c=c, a=a, b=b)
      if t.text == 'let':
        binds = []
        while True:
          pat = self.parse_atoms()
          self.expect('=')
          v = self.parse(0)
          binds.append((pat, v))
          if self.at('and'): self.next(); continue
          break
        self.expect('in')
        b = self.parse(0)
        return Node('let', tok=t, binds=binds, body=b)
      if t.text == 'some':
        vs = self.parse_binders()
        b = self.parse(0)
        return Node('some', tok=t, vs=vs, body=b)
      if t.text == 'case':
        s = self.parse(0)
        self.expect('of')
        arms = []
        if self.at('|'): self.next()
        while True:
          pat = self.parse(60)
          self.expect('=>')
          b = self.parse(60)
          arms.append((pat, b))
          if self.at('|'): self.next(); continue
          break
        return Node('case', tok=t, s=s, arms=arms)
      if t.text == 'do':
        stmts = []
        while not self.at('od'):
          if self.peek(1).text == '<-':
            v = self.next(); self.next()
            e = self.parse(0)
            stmts.append((v.text, e))
          else:
            e = self.parse(0)
            stmts.append((None, e))
          if self.at(';'): self.next()
        self.expect('od')
        return Node('do', tok=t, stmts=stmts)
    if t.kind == 'sym':
      if t.text == '(':
        if self.at(':'):
          self.next()
          ty = self.parse_type()
          self.expect(')')
          return Node('tyterm', tok=t, ty=ty)
        if self.at(')'):
          self.next()
          return Node('id', tok=t, name='()')
        e = self.parse(0)
        self.expect(')')
        return Node('paren', tok=t, e=e)
      if t.text == '[':
        items = []
        if not self.at(']'):
          while True:
            items.append(self.parse(60))
            if self.at(';'): self.next(); continue
            break
        self.expect(']')
        return Node('list', tok=t, items=items)
      if t.text == '{':
        if self.at('}'):
          self.next(); return Node('set', tok=t, items=[])
        e = self.parse(0)
        if self.at('|'):
          self.next()
          p = self.parse(0)
          if self.at('|'):
            self.next()
            p2 = self.parse(0)
            self.expect('}')
            return Node('setabs2', tok=t, e=e, p=p, p2=p2)
          self.expect('}')
          return Node('setabs', tok=t, e=e, p=p)
        items = [e]
        while self.at(';'):
          self.next(); items.append(self.parse(60))
        self.expect('}')
        return Node('set', tok=t, items=items)
      if t.text == '<|':
        upds = self.parse_updates()
        self.expect('|>')
        return Node('reclit', tok=t, upds=upds)
      if t.text in ('!', '?', '\\', '@'):
        q = t.text
        if q == '?' and self.at('!'):
          self.next(); q = '?!'
        vs = self.parse_binders()
        b = self.parse(0)
        return Node('quant', tok=t, q=q, vs=vs, body=b)
      if t.text == '~':
        e = self.parse_atoms()
        return Node('prefix', tok=t, op='~', e=e)
      if t.text == '-':
        e = self.parse_atoms()
        return Node('prefix', tok=t, op='-', e=e)
      if t.text == '&':
        e = self.parse_atom()
        return Node('prefix', tok=t, op='&', e=e)
      if t.text in ('𝕌', 'univ'):
        self.expect('(')
        self.expect(':')
        ty = self.parse_type()
        self.expect(')')
        return Node('univ', tok=t, ty=ty)
      if t.text == '$':
        o = self.next()
        return Node('dollar', tok=t, name=o.text)
      if t.text == '«':
        parts = []
        while not self.at('»'):
          parts.append(self.next())
        self.expect('»')
        return Node('mlstring', tok=t, parts=parts)
      if t.text == '⟪':
        e = self.parse(0)
        self.expect('⟫')
        return Node('quoted', tok=t, e=e)
      if t.text == '^':
        e = self.parse_atom()
        return Node('antiq', tok=t, e=e)
    raise SyntaxError(f'parse_atom: {t.kind}:{t.text!r} at {t.pos}')


# ---------------------------------------------------------------
# printing HOL Light
# ---------------------------------------------------------------

HLPREC = {}
for k, v in INFIX.items():
  HLPREC[v[2]] = v[3]


NAME_MAP = {}          # set by the porter, from tools/overrides.py


ARGPERM = {
  'FOLDR': (3, [0, 2, 1], 'ITLIST'),
}


def strip_app(e):
  args = []
  while e.kind == 'app':
    args.append(e.arg); e = e.fn
  return e, list(reversed(args))


class Ctx:
  """what the printer needs to know about the port"""

  def __init__(self, names=None, fields=None, recs=None, thy='',
               overloads=None, accessors=None, cons=None):
    self.names = names or {}     # cakeml name -> hol light name
    self.fields = fields or {}   # field name -> record type name
    self.recs = recs or {}       # record type -> [field names]
    self.overloads = overloads or {}   # name -> hol light term text
    self.accessors = accessors or {}   # field name -> accessor name
    self.cons = cons or set()          # the constructor names
    self.thy = thy
    self.wild = 0
    self.warn = []

  def name(self, n):
    if '$' in n:
      thy, n2 = n.split('$')
      return self.names.get((thy, n2), self.names.get(n2, n2))
    if n in NAME_MAP: return NAME_MAP[n]
    return self.names.get((self.thy, n), self.names.get(n, n))

  def field(self, f):
    """the accessor of a record field, without its argument"""
    if f in self.accessors: return self.accessors[f]
    if f in self.fields: return self.fields[f] + '_' + f
    self.warn.append(f'unknown record field {f}')
    return '?_' + f

  def fresh(self):
    self.wild += 1
    return '_' + str(self.wild)


def greek(toks):
  """a type with type variables that came from Greek letters, which
     HOL4 unifies with the types around it, but HOL Light does not"""
  return any(t.kind == 'tyvar' and t.text.startswith("'g") for t in toks)


def layout(tok, s):
  if tok is not None and tok.nl:
    return '\n' * tok.nl + ' ' * tok.indent + s
  return s


class Printer:
  def __init__(self, ctx):
    self.ctx = ctx
    self.done = set()

  def pr(self, e, prec=0):
    tok = e.tok
    fresh = tok is not None and tok.pos not in self.done
    if fresh: self.done.add(tok.pos)
    s = self.pr0(e, prec)
    return layout(tok, s) if fresh else s

  def paren(self, s, inner, outer):
    return '(' + s + ')' if inner < outer else s

  def pr_type(self, toks):
    out = ''
    for t in toks:
      txt = self.ctx.name(t.text) if t.kind == 'id' else t.text
      if out and not out.endswith('(') and not out.endswith(',') \
         and txt not in (')', ',', '#'):
        out += ' '
      elif out.endswith(',') or out.endswith('#'):
        out += ' '
      out += txt
    return out

  def pr0(self, e, prec):
    k = e.kind
    if k == 'id':
      n = e.name
      if n == '_': return self.ctx.fresh()
      if n in self.ctx.overloads:
        return '(' + self.ctx.overloads[n] + ')'
      return self.ctx.name(n)
    if k == 'num':
      t = e.text
      if t.endswith('w'):
        return '(n2w ' + t[:-1] + ')'
      if t.endswith('n') or t.endswith('i') or t.endswith('c'):
        return t[:-1]
      if t.startswith('0x'):
        return str(int(t, 16))
      return t
    if k == 'str':
      return e.text
    if k == 'chr':
      c = e.text[2:-1]
      c = {'\\n': '\n', '\\t': '\t', '\\\\': '\\', '\\"': '"'}.get(c, c)
      return '(CHR ' + str(ord(c)) + ')'
    if k == 'mlstr':
      return '(strlit "' + e.text + '")'
    if k == 'paren':
      return '(' + self.pr(e.e, 0) + ')'
    if k == 'typed':
      if greek(e.ty):
        return self.pr(e.e, prec)
      return self.paren(self.pr(e.e, 1) + ':' + self.pr_type(e.ty),
                        0, prec)
    if k == 'app':
      hop, args = strip_app(e)
      if hop.kind == 'id':
        n = self.ctx.name(hop.name)
        if n in ARGPERM:
          ar, perm, newname = ARGPERM[n]
          if len(args) == ar:
            s = newname + ' ' + ' '.join(self.pr(args[i], APP)
                                         for i in perm)
            return self.paren(s, PRE_APP, prec)
      fn = self.pr(e.fn, PRE_APP)
      arg = self.pr(e.arg, APP)
      return self.paren(fn + ' ' + arg, PRE_APP, prec)
    if k == 'infix':
      op = e.op
      if op == '<>':
        return self.paren('~(' + self.pr(e.l, 12) + ' = ' +
                          self.pr(e.r, 13) + ')', PRE_APP, prec)
      if op == 'NOTIN':
        return self.paren('~(' + self.pr(e.l, 11) + ' IN ' +
                          self.pr(e.r, 12) + ')', PRE_APP, prec)
      if op in ("'", "''", '--'):
        return self.paren(INFIX[op][2] + ' ' + self.pr(e.l, APP) + ' ' +
                          self.pr(e.r, APP), PRE_APP, prec)
      if op == '%%':
        return self.paren('word_bit ' + self.pr(e.r, APP) + ' ' +
                          self.pr(e.l, APP), PRE_APP, prec)
      _, assoc, hop, hprec = INFIX[op]
      if assoc == 'r':
        l = self.pr(e.l, hprec + 1); r = self.pr(e.r, hprec)
      elif assoc == 'l':
        l = self.pr(e.l, hprec); r = self.pr(e.r, hprec + 1)
      else:
        l = self.pr(e.l, hprec + 1); r = self.pr(e.r, hprec + 1)
      sep = '' if hop == ',' else ' '
      return self.paren(l + sep + hop + sep + r, hprec, prec)
    if k == 'prefix':
      if e.op == '~':
        return self.paren('~' + self.pr(e.e, PRE_APP), PRE_APP, prec)
      if e.op == '-':
        return self.paren('--' + self.pr(e.e, PRE_APP), PRE_APP, prec)
      if e.op == '&':
        return self.paren('&' + self.pr(e.e, APP), PRE_APP, prec)
    if k == 'some':
      vs = ' '.join(self.pr(v, APP) for v in e.vs)
      return self.paren('some (\\' + vs + '. ' + self.pr(e.body, 0) +
                        ')', PRE_APP, prec)
    if k == 'quant':
      vs = ' '.join(self.pr(v, APP) for v in e.vs)
      return self.paren(e.q + vs + '. ' + self.pr(e.body, 0), 1, prec)
    if k == 'cond':
      s = ('if ' + self.pr(e.c, 0) + ' then ' + self.pr(e.a, 0) +
           ' else ' + self.pr(e.b, 0))
      return self.paren(s, 1, prec)
    if k == 'let':
      bs = ' and '.join(self.pr(p, 0) + ' = ' + self.pr(v, 0)
                        for p, v in e.binds)
      return self.paren('let ' + bs + ' in ' + self.pr(e.body, 0),
                        1, prec)
    if k == 'case':
      arms = ' | '.join(self.pr(p, 0) + ' -> ' + self.pr(b, 0)
                        for p, b in e.arms)
      return self.paren('match ' + self.pr(e.s, 0) + ' with ' + arms,
                        1, prec)
    if k == 'field':
      return self.paren(self.ctx.field(e.fld) + ' ' + self.pr(e.e, APP),
                        PRE_APP, prec)
    if k == 'recupd':
      s = self.pr(e.e, APP)
      for i, (fld, v) in enumerate(e.upds):
        s = (self.ctx.field(fld) + '_fupd (K ' + self.pr(v, APP) +
             ') ' + s)
        if i < len(e.upds) - 1: s = '(' + s + ')'
      return self.paren(s, PRE_APP, prec)
    if k == 'reclit':
      flds = [f for f, _ in e.upds]
      rty = self.ctx.fields.get(flds[0], '?')
      order = self.ctx.recs.get(rty, flds)
      vals = []
      for f in order:
        v = [v for g, v in e.upds if g == f]
        vals.append(self.pr(v[0], APP) if v else 'ARB')
      return self.paren('mk_' + rty + ' ' + ' '.join(vals),
                        PRE_APP, prec)
    if k == 'list':
      return '[' + '; '.join(self.pr(i, 0) for i in e.items) + ']'
    if k == 'set':
      if not e.items: return '{}'
      return '{' + ','.join(self.pr(i, 0) for i in e.items) + '}'
    if k == 'setabs':
      return '{' + self.pr(e.e, 0) + ' | ' + self.pr(e.p, 0) + '}'
    if k == 'setabs2':
      return ('{' + self.pr(e.e, 0) + ' | ' + self.pr(e.p, 0) + ' | ' +
              self.pr(e.p2, 0) + '}')
    if k == 'dollar':
      n = e.name
      if n in INFIX: return '(' + INFIX[n][2] + ')'
      return self.ctx.name(n)
    if k == 'univ':
      if greek(e.ty): return 'UNIV'
      return '(UNIV:' + self.pr_type(e.ty) + '->bool)'
    if k == 'tyterm':
      return '(:' + self.pr_type(e.ty) + ')'
    if k == 'quoted':
      return '(' + e.text + ')'
    if k == 'antiq':
      return self.pr(e.e, prec)
    if k == 'do':
      return self.pr_do(e.stmts)
    raise SyntaxError(f'print: {k}')

  def pr_do(self, stmts):
    (v, e) = stmts[0]
    if len(stmts) == 1:
      return self.pr(e, 0)
    rest = self.pr_do(stmts[1:])
    if v is None:
      return ('monad_ignore_bind ' + self.pr(e, APP) + ' (' + rest + ')')
    return ('monad_bind ' + self.pr(e, APP) + ' (\\' + v + '. ' +
            rest + ')')


def rename_ast(e, sub):
  """rename identifiers in a syntax tree"""
  if isinstance(e, Node):
    d = {}
    for k, v in e.__dict__.items():
      if k in ('tok', 'kind'): continue
      elif k == 'name' and v in sub: d[k] = sub[v]
      else: d[k] = rename_ast(v, sub)
    return Node(e.kind, tok=e.tok, **d)
  if isinstance(e, list): return [rename_ast(x, sub) for x in e]
  if isinstance(e, tuple): return tuple(rename_ast(x, sub) for x in e)
  return e


def clauses_of(e):
  """the clauses of a definition, as (head, args, rhs)"""
  def conj(e):
    if e.kind == 'paren': return conj(e.e)
    if e.kind == 'quant' and e.q == '!': return conj(e.body)
    if e.kind == 'infix' and e.op == '/\\':
      return conj(e.l) + conj(e.r)
    return [e]
  out = []
  for cl in conj(e):
    while cl.kind == 'paren': cl = cl.e
    if cl.kind == 'quant' and cl.q == '!':
      cl = cl.body
      while cl.kind == 'paren': cl = cl.e
    if cl.kind != 'infix' or cl.op not in ('=', '<=>'):
      raise SyntaxError('clauses_of: not an equation')
    l = cl.l
    while l.kind == 'paren': l = l.e
    hop, args = strip_app(l)
    while hop.kind in ('paren', 'typed'): hop = hop.e
    out.append((hop, args, cl.r))
  return out


def translate(text, ctx):
  """translate a HOL4 term to a HOL Light term"""
  toks = tokenize(text)
  p = Parser(toks, ctx)
  e = p.parse()
  if p.peek().kind != 'eof':
    t = p.peek()
    raise SyntaxError(f'unparsed input at {t.pos}: {t.text!r}')
  return Printer(ctx).pr(e, 0)


# ---------------------------------------------------------------
# types
# ---------------------------------------------------------------
# a type is ('v',name) | ('op',name,args)

class TypeParser:
  def __init__(self, toks):
    self.toks = toks; self.i = 0

  def peek(self, k=0):
    return self.toks[min(self.i + k, len(self.toks) - 1)]

  def next(self):
    t = self.toks[self.i]; self.i += 1; return t

  def at(self, s):
    return self.i < len(self.toks) and self.peek().text == s

  def parse(self):
    ty = self.parse_prod()
    if self.at('->'):
      self.next()
      return ('op', 'fun', [ty, self.parse()])
    return ty

  def parse_prod(self):
    ty = self.parse_sum()
    if self.at('|->'):
      self.next()
      return ('op', 'fmap', [ty, self.parse_prod()])
    return ty

  def parse_sum(self):
    ty = self.parse_prodonly()
    if self.at('+'):
      self.next()
      return ('op', 'sum', [ty, self.parse_sum()])
    return ty

  def parse_prodonly(self):
    ty = self.parse_app()
    if self.at('#'):
      self.next()
      return ('op', 'prod', [ty, self.parse_prodonly()])
    return ty

  def parse_app(self):
    ty = self.parse_atom()
    while self.i < len(self.toks) and self.peek().kind == 'id':
      ty = ('op', self.next().text, [ty])
    return ty

  def parse_atom(self):
    t = self.next()
    if t.kind == 'tyvar':
      return ('v', t.text)
    if t.kind == 'num':
      return ('op', t.text, [])      # :8 (word sizes)
    if t.kind == 'id':
      return ('op', t.text, [])
    if t.text == '(':
      tys = [self.parse()]
      while self.at(','):
        self.next(); tys.append(self.parse())
      if not self.at(')'):
        raise SyntaxError('type: ) expected')
      self.next()
      if len(tys) == 1:
        ty = tys[0]
        while self.i < len(self.toks) and self.peek().kind == 'id':
          ty = ('op', self.next().text, [ty])
        return ty
      name = self.next()
      return ('op', name.text, tys)
    raise SyntaxError(f'type: {t.kind}:{t.text!r} at {t.pos}')


def parse_type_text(s):
  return TypeParser(tokenize(s)[:-1]).parse()


def type_subst(ty, sub):
  k = ty[0]
  if k == 'v': return sub.get(ty[1], ty)
  return ('op', ty[1], [type_subst(a, sub) for a in ty[2]])


def expand_type(ty, abbrevs):
  """expand the type abbreviations of the port"""
  if ty[0] == 'v': return ty
  args = [expand_type(a, abbrevs) for a in ty[2]]
  name = ty[1]
  if name in abbrevs:
    params, body = abbrevs[name]
    if len(params) == len(args):
      return expand_type(type_subst(body, dict(zip(params, args))),
                         abbrevs)
  return ('op', name, args)


def print_type(ty, ctx=None, prec=0):
  if ty[0] == 'v': return ty[1]
  name, args = ty[1], ty[2]
  if name == 'fun':
    s = (print_type(args[0], ctx, 3) + '->' +
         print_type(args[1], ctx, 2))
    return '(' + s + ')' if prec > 2 else s
  if name == 'prod':
    s = (print_type(args[0], ctx, 5) + '#' +
         print_type(args[1], ctx, 4))
    return '(' + s + ')' if prec > 4 else s
  if name == 'sum':
    s = (print_type(args[0], ctx, 4) + '+' +
         print_type(args[1], ctx, 3))
    return '(' + s + ')' if prec > 3 else s
  nm = ctx.name(name) if ctx is not None else name
  if not args: return nm
  if len(args) == 1:
    s = print_type(args[0], ctx, 6) + ' ' + nm
    return '(' + s + ')' if prec > 5 else s
  return '(' + ','.join(print_type(a, ctx, 0) for a in args) + ')' + nm


def type_vars_of(ty):
  if ty[0] == 'v': return [ty[1]]
  out = []
  for a in ty[2]:
    for v in type_vars_of(a):
      if v not in out: out.append(v)
  return out
