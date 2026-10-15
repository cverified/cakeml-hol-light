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
  '⊌': 'FUNION', '⊑': 'SUBMAP', '≪': '<<', '≫': '>>', '⋙': '>>>',
  '‖': '||', '↦': '|->', '⊎': 'BAG_UNION',
}

GREEK = dict(zip('αβγδεζηθ'
                 'ικμνξοπρ'
                 'στυφχψω',
                 ["'g" + c for c in 'abcdefghijklmnopqrstuvw']))

# the Greek letters that a CakeML source uses for a term variable
# and not for a type variable; HOL Light needs an ASCII name
GREEK_VAR = {'μ': 'mu', 'σ': 'sigma', 'τ': 'tau', 'ρ': 'rho'}

KEYWORDS = ['if', 'then', 'else', 'let', 'and', 'in', 'case', 'of',
            'do', 'od', 'with', 'otherwise', 'some']

# symbols, longest first
SYMS = ['<=>', '==>', '>>>', '#>>', '#<<', '<=+', '>=+', '||', '&&',
        '{|', '|}', '❲', '❳',
        '##',
        "''", '--', '%%',
        '??', '|->', '<|', '|>', ':=', '<-', '->', '=>', '::', '++',
        '<<', '>>', '@@', '**', '|++', '|+', '/\\', '\\/', '<>',
        '<=', '>=',
        '<+', '>+', '=+', '<*>', '<<=', '≼', '«', '»', '⟪', '⟫',
        '𝕌', 'univ',
        '(', ')', '[', ']', '{', '}', ',', ';', '.', '|', '=', '<',
        '>', '+', '-', '*', '/', '~', '!', '?', '\\\\', '\\', ':',
        '$', '&',
        '^', '#', '@', '%', '§', '><', '⟨', '⟩']


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
      # the unsigned word comparisons have a subscript plus
      n2 = 1
      if t in ('<', '<=', '>', '>=') and s.startswith('₊', i + 1):
        t += '+'; n2 = 2
      toks.append(Tok('key' if t in KEYWORDS else 'sym', t, start,
                      nl, icol))
      i += n2; col += n2; nl = 0; continue
    if c == '^' and i + 1 < n and (s[i+1].isalpha() or
                                   s[i+1] in '_('):
      # HOL4's quotation filter reads ^ followed at once by a name
      # or a parenthesis as an antiquotation, and the ML value that
      # it splices in is in ANTIQ (a ^ b with the spaces is the
      # infix of mlstring)
      j = i + 1
      while j < n and (s[j].isalnum() or s[j] in "_'"): j += 1
      nm = s[i+1:j]
      if nm in ANTIQ:
        toks.append(Tok('sym', '(', start, nl, icol))
        toks += [x for x in tokenize(ANTIQ[nm]) if x.kind != 'eof']
        toks.append(Tok('sym', ')', start, 0, icol))
        i = j; col += j - i; nl = 0; continue
      if nm:
        toks.append(Tok('id', nm, start, nl, icol))
        i = j; col += j - i; nl = 0; continue
      # ^( : the parenthesis that follows does the grouping
      i += 1; col += 1; continue
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
    if c in GREEK_VAR:
      j = i + 1
      while j < n and (s[j].isalnum() or s[j] in "_'"): j += 1
      toks.append(Tok('id', GREEK_VAR[c] + s[i+1:j], start, nl, icol))
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
        # the unsigned word comparisons are <, <=, > and >= with a
        # subscript plus
        n2 = len(sym)
        if sym in ('<', '<=', '>', '>=') and s.startswith('₊', i + n2):
          sym += '+'; n2 += 1
        toks.append(Tok('sym', sym, start, nl, icol))
        i += n2; col += n2; nl = 0; break
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
  '|++':   (500, 'l', '|++',    15),
  '\\\\':    (600, 'l', '\\\\',     21),
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
  '%':     (650, 'l', '%',      22),
  '**':    (700, 'r', 'EXP',    24),
  'pow':   (700, 'r', 'pow',    24),
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
  '##':    (490, 'r', '##',     20),
  'FUNION':(500, 'l', 'FUNION', None),
  'BAG_UNION':(500, 'l', 'BAG_UNION', None),
  'SUBMAP':(450, 'n', 'SUBMAP', 12),
  '$':     (460,  'r', '$',      0),
  "'":     (2000, 'l', 'FAPPLY', 0),
  "''":    (350, 'l', 'word_slice', 0),
  '--':    (350, 'l', 'word_bits', 0),
  '%%':    (400, 'l', 'word_bit', 0),
  '=+':    (320, 'n', '=+',     23),
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

# where a type stops: everything that only occurs in terms
TYPE_STOP = (STOP - {'->'}) | {'=', '<=>', '==>', '/\\', '\\/', '<',
        '>', '<=', '>=', '~', '::', '++', '*', '@', '$', '!', '?',
        '\\', '&', '%%', "'", "''", '--', '|+', '|++'}


def mk_app(name, args, tok=None):
  e = Node('id', tok=tok, name=name)
  for a in args:
    e = Node('app', tok=tok, fn=e, arg=a)
  return e


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

  def parse_type(self, stop_unknown=False):
    """a type, as a list of tokens.  A type that is not in
       parentheses ends at a name that is not a type: HOL4 reads
       !i:num ms. as !(i:num) ms, because ms is no type of its
       own"""
    out = []
    depth = 0
    while True:
      t = self.peek()
      if t.kind == 'eof': break
      if t.text in ('(', '['):
        depth += 1
      elif t.text in (')', ']'):
        if depth == 0: break
        depth -= 1
      elif depth == 0 and (t.text in TYPE_STOP or t.kind == 'key'):
        break
      elif (stop_unknown and depth == 0 and out and t.kind == 'id'
            and self.ctx is not None and self.ctx.tyops
            and t.text.split('$')[-1] not in self.ctx.tyops):
        break
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
      if t.text == '$':
        # $+ is the function form of an operator, f $ x is an
        # application with a low precedence
        return self.peek(1).pos == t.pos + 1
      if t.text in ('(', '[', '{', '{|', '{}', '&', '<|', '«', '⟪',
                    '𝕌'):
        return True
      if t.text == '~': return True
      return not arg and t.text in ('!', '?', '\\', '@', '-', '^')
    return False

  def parse_atoms(self, annot=True):
    e = self.parse_fields(self.parse_atom())
    # R^* is RTC R and R^+ is TC R (relationTheory)
    while self.peek().text == '^' and \
          self.peek(1).text in ('*', '+') and \
          self.peek(1).pos == self.peek().pos + 1:
      self.next()
      e = mk_app('RTC' if self.next().text == '*' else 'TC', [e])
    while self.starts_atom(True):
      a = self.parse_fields(self.parse_atom())
      e = Node('app', tok=e.tok, fn=e, arg=a)
    e = self.parse_postfix(e)
    if annot and self.at(':'):
      self.next()
      ty = self.parse_type()
      e = Node('typed', tok=e.tok, e=e, ty=ty)
    return e

  def parse_fields(self, e):
    while True:
      t = self.peek()
      if t.text == '.' and self.peek(1).kind == 'id':
        self.next(); fld = self.next()
        e = Node('field', tok=t, e=e, fld=fld.text)
      # l❲i❳ is EL i l and l❲i ↦ v❳ is LUPDATE v i l (the list
      # syntax of HOL4's combinpp)
      elif t.text == '❲':
        self.next()
        i = self.parse(0)
        if self.at('|->'):
          self.next()
          v = self.parse(0)
          e = mk_app('LUPDATE', [v, i, e], t)
        else:
          e = mk_app('EL', [i, e], t)
        self.expect('❳')
      else:
        break
    return e

  def parse_postfix(self, e):
    while True:
      t = self.peek()
      # fm⟨k ↦ v⟩ is fm |+ (k,v) and fm⟨k⟩ is fm ' k (the finite map
      # syntax of HOL4's combinpp)
      if t.text == '⟨':
        self.next()
        while True:
          k = self.parse(101)
          if self.at('|->'):
            self.next()
            v = self.parse(0)
            e = Node('infix', tok=t, op='|+', l=e,
                     r=Node('infix', tok=t, op=',', l=k, r=v))
          else:
            e = Node('infix', tok=t, op="'", l=e, r=k)
          if self.at(';'): self.next(); continue
          break
        self.expect('⟩')
      elif t.text == 'with':
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
      # HOL4 has r with fld := v and r with fld updated_by f
      if self.peek().text == 'updated_by':
        self.next(); fn = True
      else:
        self.expect(':='); fn = False
      v = self.parse(60)
      upds.append((fld.text, v, fn))
      if single or not self.at(';'): break
      self.next()
      # a record literal may have a semicolon before its |>
      if self.at('|>'): break
    return upds

  def parse_binders(self):
    # HOL4 writes a paired abstraction as \x,y. e as well as as
    # \(x,y). e, and a lambda may have several of them next to
    # each other (reg_alloc's \p:num,x p',x'. p>p')
    groups = []
    comma = False
    while not self.at('.'):
      if self.at(','):
        self.next(); comma = True; continue
      t = self.peek()
      if t.text == '(':
        v = self.parse_atom()
      elif t.kind == 'id' or t.text == '_':
        self.next()
        v = Node('id', tok=t, name=t.text)
        if self.at(':'):
          self.next()
          v = Node('typed', tok=t, e=v,
                   ty=self.parse_type(True))
      else:
        raise SyntaxError(f'binder expected at {t.pos}: {t.text!r}')
      if comma and groups: groups[-1].append(v)
      else: groups.append([v])
      comma = False
      if self.at('::'):
        self.next()
        groups[-1][-1].res = self.parse(0)
    self.expect('.')
    vs = []
    for g in groups:
      if len(g) == 1:
        vs.append(g[0])
      else:
        e = g[-1]
        for v in reversed(g[:-1]):
          e = Node('infix', tok=v.tok, op=',', l=v, r=e)
        vs.append(Node('paren', tok=g[0].tok, e=e))
    return vs

  def starts_binder(self):
    """does a list of binders and a dot follow?"""
    j = self.i
    while j < len(self.toks):
      t = self.toks[j]
      if t.text == '.': return j > self.i
      if t.kind == 'id' or t.kind == 'tyvar' or \
         t.text in ('(', ')', ',', ':', '_'):
        j += 1
      else:
        return False
    return False

  def parse_case(self, t):
    s = self.parse(0)
    self.expect('of')
    arms = []
    if self.at('|'): self.next()
    while True:
      # HOL4 allows parentheses around an alternative, which is how
      # a case inside one is kept apart from the alternatives after
      # it
      if self.at('('):
        save = self.i
        try:
          self.next()
          pat = self.parse(50)
          self.expect('=>')
          b = self.parse(60)
          self.expect(')')
          arms.append((pat, b))
          if self.at('|'): self.next(); continue
          break
        except SyntaxError:
          self.i = save
      # a pattern may be a tuple (HOL4 writes a case on several
      # values as "case x, y of p, q => ...")
      pat = self.parse(50)
      self.expect('=>')
      b = self.parse(60)
      arms.append((pat, b))
      if self.at('|'): self.next(); continue
      break
    return Node('case', tok=t, s=s, arms=arms)

  def parse_atom(self):
    t = self.next()
    if t.kind == 'num':
      return Node('num', tok=t, text=t.text)
    if t.kind == 'str':
      return Node('str', tok=t, text=t.text)
    if t.kind == 'chr':
      return Node('chr', tok=t, text=t.text)
    if t.kind == 'mlstr':
      return Node('mlstr', tok=t, text=t.text)
    if t.kind == 'quoted':
      return Node('quoted', tok=t, text=t.text)
    if t.kind == 'id':
      # the patternMatches library of HOL4 writes a case as a pmatch
      if t.text == 'pmatch' and PMATCH[0]:
        return self.parse_case(t)
      # the binders of HOL4 that are constants in HOL Light
      if t.text in HOL4_BINDERS and self.starts_binder():
        vs = self.parse_binders()
        return Node('some', tok=t, name=t.text, vs=vs,
                    body=self.parse(0))
      return Node('id', tok=t, name=t.text)
    if t.kind == 'tyvar':
      return Node('id', tok=t, name=t.text)
    if t.kind == 'key':
      if t.text == 'if':
        # the branches of a conditional of HOL4 stop at a comma:
        # (if b then x else y, z) is the pair of the conditional
        # and z
        c = self.parse(0); self.expect('then')
        a = self.parse(51); self.expect('else')
        b = self.parse(51)
        return Node('cond', tok=t, c=c, a=a, b=b)
      if t.text == 'let':
        binds = []
        seq = False
        while True:
          pat = self.parse_atoms()
          self.expect('=')
          v = self.parse(0)
          binds.append((pat, v))
          if self.at('and'): self.next(); continue
          # HOL4 also separates the bindings of a let with a
          # semicolon, and then they are nested (and there may be
          # one before the in)
          if self.at(';'):
            self.next()
            if self.at('in'): break
            seq = True; continue
          break
        self.expect('in')
        b = self.parse(0)
        if seq:
          for pat, v in reversed(binds[1:]):
            b = Node('let', tok=None, binds=[(pat, v)], body=b)
          binds = binds[:1]
        return Node('let', tok=t, binds=binds, body=b)
      if t.text == 'some':
        vs = self.parse_binders()
        b = self.parse(0)
        return Node('some', tok=t, name='some', vs=vs, body=b)
      if t.text == 'case':
        return self.parse_case(t)
      if t.text == 'do':
        stmts = []
        while not self.at('od'):
          # the left hand side of a <- may be a pattern
          save = self.i
          v = None
          try:
            v = self.parse_atoms()
            if not self.at('<-'): v = None
          except SyntaxError:
            v = None
          if v is None:
            self.i = save
            stmts.append((None, self.parse(0)))
          else:
            self.next()
            stmts.append((v, self.parse(0)))
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
        # the operator form of an operator, as in FIELDS ((=) #"\n") ls
        if self.peek().kind in ('sym', 'id') and \
           self.peek(1).text == ')' and \
           (self.peek().text in INFIX or
            self.peek().text in ('&', '~', '--')):
          o = self.next(); self.next()
          return Node('dollar', tok=t, name=o.text)
        e = self.parse(0)
        self.expect(')')
        return Node('paren', tok=t, e=e)
      if t.text == '[':
        items = []
        if not self.at(']'):
          while True:
            # HOL4 separates the elements with a semicolon, so a
            # comma in an element makes it a pair
            items.append(self.parse(50))
            if self.at(';'): self.next()
            else: break
            if self.at(']'): break
        self.expect(']')
        return Node('list', tok=t, items=items)
      if t.text == '{}':
        return Node('set', tok=t, items=[])
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
          self.next()
          if self.at('}'): break
          items.append(self.parse(50))
        self.expect('}')
        return Node('set', tok=t, items=items)
      # the bag of HOL4's bagTheory
      if t.text == '{|':
        items = []
        if not self.at('|}'):
          while True:
            items.append(self.parse(50))
            if self.at(';'): self.next()
            else: break
            if self.at('|}'): break
        self.expect('|}')
        return Node('bag', tok=t, items=items)
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
        # a binder of HOL4 may be restricted (!x::s. P is
        # RES_FORALL s (\x. P), of res_quanTheory)
        if any(getattr(v, 'res', None) is not None for v in vs):
          run = []
          for v in reversed(vs):
            r = getattr(v, 'res', None)
            if r is None:
              run.insert(0, v); continue
            if run:
              b = Node('quant', tok=t, q=q, vs=run, body=b); run = []
            b = Node('resq', tok=t, q=q, v=v, s=r, body=b)
          if run: b = Node('quant', tok=t, q=q, vs=run, body=b)
          return b
        return Node('quant', tok=t, q=q, vs=vs, body=b)
      if t.text == '~':
        e = self.parse_atoms()
        return Node('prefix', tok=t, op='~', e=e)
      if t.text == '-':
        e = self.parse_atoms()
        return Node('prefix', tok=t, op='-', e=e)
      if t.text == '&':
        # HOL4's & is a prefix that binds looser than application,
        # so &LENGTH l is &(LENGTH l); a type annotation after it
        # is of the whole (mlint's int_gcd)
        e = self.parse_atoms(False)
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
TYPE_MAP = {}          # the same, for the type names


ARGPERM = {
  'FOLDR': (3, [0, 2, 1], 'ITLIST'),
}

# HOL4 functions that take a pair where HOL Light's take two
# arguments
UNCURRIED = set(['ZIP'])


def dtarg_texts(alt):
  """the texts of the argument types of one alternative of a HOL4
     datatype specification"""
  toks = tokenize(alt)
  tp = TypeParser(toks[1:-1])
  out = []
  while tp.i < len(tp.toks):
    i0 = tp.i
    tp.parse_dtarg()
    out.append(' '.join(t.text for t in tp.toks[i0:tp.i]))
  return out


def subnodes(e):
  """the direct children of a node"""
  out = []
  def add(v):
    if isinstance(v, Node): out.append(v)
    elif isinstance(v, (list, tuple)):
      for w in v: add(w)
  for k, v in e.__dict__.items():
    if k != 'tok': add(v)
  return out


# the constructors of HOL Light that a pattern can use
HLCONS = set(['SOME', 'NONE', 'INL', 'INR', 'CONS', 'NIL', 'T', 'F'])


def pattern_vars(e, cons, lam=False):
  """the variables that a pattern binds; lam is true where the head
     of an application is bound as well (a lambda or a let)"""
  while e.kind in ('paren', 'typed'): e = e.e
  if e.kind == 'id':
    # a source may write a constructor with the name of its theory
    nm = e.name.split('$')[-1]
    return [] if not lam and (nm in cons or nm in HLCONS) \
           else [e.name]
  if e.kind == 'app':
    h, args = strip_app(e)
    out = pattern_vars(h, cons, True) if lam else []
    for a in args: out += pattern_vars(a, cons)
    return out
  if e.kind == 'infix':
    return pattern_vars(e.l, cons) + pattern_vars(e.r, cons)
  if e.kind in ('list', 'set'):
    return [v for i in e.items for v in pattern_vars(i, cons)]
  return []


def bound_names(e, cons, defn=False):
  """the names that the term binds somewhere; with defn, it is a
     definition, whose left hand sides bind their arguments"""
  out = set()
  if defn:
    try:
      for _, args, _ in clauses_of(e):
        for a in args: out.update(pattern_vars(a, cons))
    except Exception:
      pass
  def go(e):
    k = e.kind
    if k in ('quant', 'some'):
      for v in e.vs: out.update(pattern_vars(v, cons, True))
    elif k == 'resq':
      out.update(pattern_vars(e.v, cons, True))
    elif k == 'let':
      for p, _ in e.binds: out.update(pattern_vars(p, cons, True))
    elif k == 'case':
      for p, _ in e.arms: out.update(pattern_vars(p, cons))
    elif k == 'do':
      # do v <- e; ... od binds v in what follows it
      for v, _ in e.stmts:
        if v is not None: out.update(pattern_vars(v, cons, True))
    elif k == 'setabs':
      # {f x | p} binds the arguments of f, not f itself, where f
      # is a constructor (pegComplete has {TyvarT s | T})
      out.update(pattern_vars(e.e, cons))
    elif k == 'setabs2':
      # {e | vs | p} binds the variables of the middle part, not
      # the ones of the element
      out.update(pattern_vars(e.p, cons, True))
    for t in subnodes(e): go(t)
  go(e)
  return out


def strip_app(e):
  args = []
  while e.kind == 'app':
    args.append(e.arg); e = e.fn
  return e, list(reversed(args))


class Ctx:
  """what the printer needs to know about the port"""

  def __init__(self, names=None, fields=None, recs=None, thy='',
               overloads=None, accessors=None, cons=None,
               ambfields=None, updaters=None,
               abbrevs=None, tynames=None, overloaded=None,
               con_argty=None):
    self.names = names or {}     # cakeml name -> hol light name
    self.tynames = tynames or {} # the same for the type names
    self.con_argty = con_argty or {}  # (con,index) -> type text
    self.overloaded = overloaded or set()  # names HOL4 overloads
    self.defining = set()        # the names of the block being made
    self.fields = fields or {}   # field name -> record type name
    self.recs = recs or {}       # record type -> [field names]
    self.ambfields = ambfields or {}  # field -> overloaded name
    self.reclit = None           # the record type of a literal
    self.overloads = overloads or {}   # name -> hol light term text
    self.accessors = accessors or {}   # field name -> accessor name
    self.updaters = updaters or {}     # field name -> update name
    self.cons = cons or set()          # the constructor names
    self.tyops = set()                 # the type names in scope
    self.abbrevs = abbrevs or {}       # type abbreviation -> type
    self.intnums = False               # are numerals integers here?
    self.intneg = False                # is $~ the negation of an int?
    self.intvars = set()               # variables holding integers
    self.vars = {}                     # bound variables to rename
    self.wordnot = False               # is ~ the word complement?
    self.thy = thy
    self.wild = 0
    self.warn = []

  def name(self, n):
    if '$' in n:
      thy, n2 = n.split('$')
      return self.names.get((thy, n2), self.names.get(n2, n2))
    if n in NAME_MAP: return NAME_MAP[n]
    # the block that defines a name uses the name of the constant,
    # and everything else the name that HOL4 overloads with it
    if n in self.defining:
      return self.names.get((self.thy, n), self.names.get(n, n))
    if n in self.overloaded: return n
    # the size function of a datatype is called after the type, so
    # it follows the name that the port gives the type (HOL4's
    # exp_size of closLang is closLang_exp_size)
    if (n.endswith('_size') and (self.thy, n) not in self.names
        and n not in self.names):
      ty = self.tyname(n[:-len('_size')])
      if ty != n[:-len('_size')]: return ty + '_size'
    return self.names.get((self.thy, n), self.names.get(n, n))

  def tyname(self, n):
    if '$' in n:
      thy, n2 = n.split('$')
      if n2 in TYPE_MAP: return TYPE_MAP[n2]
      return self.tynames.get((thy, n2), self.tynames.get(n2, n2))
    if n in TYPE_MAP: return TYPE_MAP[n]
    if n in NAME_MAP: return NAME_MAP[n]
    return self.tynames.get((self.thy, n),
                            self.tynames.get(n, n))

  def field(self, f):
    """the accessor of a record field, without its argument"""
    if f in self.accessors: return self.accessors[f]
    # the name of a field that several record types have is an
    # overload of their accessors, which HOL Light resolves by the
    # type of the record, as HOL4 does
    if f in self.ambfields and f not in self.fields:
      return self.ambfields[f]
    if f in self.fields: return self.fields[f] + '_' + f
    self.warn.append(f'unknown record field {f}')
    return '?_' + f

  def fupd(self, f):
    """the update of a record field, without its arguments"""
    if f in self.updaters: return self.updaters[f]
    return self.field(f) + '_fupd'

  def fresh(self):
    self.wild += 1
    return '_' + str(self.wild)


NUMERIC_FUNS = set(['int_of_num', 'num_of_int', 'w2i', 'i2w', 'ival',
                    'iword', 'int_add', 'int_sub', 'int_mul',
                    'int_neg', 'ABS', 'abs', 'Num'])


def sml_char(s):
  """the character that an SML character literal body denotes"""
  esc = {'n': '\n', 't': '\t', '\\': '\\', '"': '"', 'r': '\r',
         'a': '\a', 'b': '\b', 'f': '\f', 'v': '\v'}
  if len(s) > 1 and s[0] == '\\':
    if s[1:].isdigit(): return chr(int(s[1:]))
    if s[1] == 'u': return chr(int(s[2:], 16))
    return esc.get(s[1], s[1])
  return s


def numeric(e):
  """is this term a number rather than a proposition?"""
  while e.kind == 'paren': e = e.e
  if e.kind == 'num': return True
  if e.kind == 'prefix': return e.op in ('&', '-', '~')
  if e.kind == 'infix':
    return e.op in ('+', '-', '*', '/', 'DIV', 'MOD', 'EXP', '**')
  if e.kind == 'app':
    h, _ = strip_app(e)
    return h.kind == 'id' and h.name in NUMERIC_FUNS
  if e.kind == 'typed': return numeric(e.e)
  return False


def greek(toks):
  """a type with type variables that came from Greek letters, which
     HOL4 unifies with the types around it, but HOL Light does not"""
  return any(t.kind == 'tyvar' and t.text.startswith("'g") for t in toks)


def layout(tok, s):
  if tok is not None and tok.nl:
    return '\n' * tok.nl + ' ' * tok.indent + s
  return s


NUMCTX = set(['+', '-', '*', '/', 'DIV', 'MOD', 'EXP', '**',
              '<', '<=', '>', '>='])

# the operators whose two sides have the same numeric type, and the
# functions whose argument is an integer
ARITH = set(['+', '-', '*', '/', '%', 'DIV', 'MOD'])
INT_FUNS = set(['Num', 'ABS'])  # the names of HOL4

# HOL Light constants that are binders, so that f (\x. b) has to be
# printed as f x. b
BINDERS = set(['minimal'])


# the binders of HOL4 that the port writes as a constant applied to
# an abstraction, and whether the pmatch syntax of the patternMatches
# library is enabled in this file
HOL4_BINDERS = set(['LEAST', 'LEAST_INT', 'SEP_EXISTS', 'OLEAST'])
PMATCH = [False]


BASE_INFIX = dict(INFIX)
BASE_SYMS = list(SYMS)


def enable_pmatch(on):
  PMATCH[0] = on


def reset_grammar():
  """the term grammar of a fresh HOL4 theory: the infixes that a
     CakeML source adds itself do not reach the other files"""
  INFIX.clear(); INFIX.update(BASE_INFIX)
  OWN_INFIX.clear()
  MONAD[0] = None
  ANTIQ.clear()
  SYMS[:] = BASE_SYMS
  PMATCH[0] = False


def add_infix(tok, prec, assoc):
  """an infix that a CakeML source declares itself; the port writes
     it as an application of the constant it is overloaded with"""
  INFIX[tok] = (prec, assoc, tok, None)
  OWN_INFIX.add(tok)
  if tok not in SYMS and not tok[0].isalpha():
    SYMS.append(tok)
    SYMS.sort(key=len, reverse=True)


OWN_INFIX = set()      # the infixes a CakeML source declares itself
MONAD = [None]         # the monad that a source has enabled
ANTIQ = {}             # the ML values that a source antiquotes


def set_monad(m):
  """the bind and the ignorebind of the monad whose syntax the
     source of this file uses"""
  MONAD[0] = m


def set_infix_name(tok, name):
  """a symbolic infix that a CakeML source overloads with a constant
     is written as an application of that constant"""
  if tok in INFIX and tok not in BASE_INFIX:
    prec, assoc, _, hprec = INFIX[tok]
    INFIX[tok] = (prec, assoc, name, None)


def set_equality(loose):
  """HOL4's ParseExtras.loose_equality puts = at precedence 100,
     where it binds looser than /\\, and tight_equality back at 450,
     where it binds tighter (which is HOL4's default)"""
  _, assoc, hop, hprec = INFIX['=']
  INFIX['='] = (100 if loose else 450, assoc, hop, hprec)


class Printer:
  def __init__(self, ctx):
    self.ctx = ctx
    self.done = set()
    self.numctx = False

  def cname(self, n):
    """the HOL Light name of a HOL4 constant, expanding an
       overload"""
    if self.ctx.overloads.get(n): return self.ctx.overloads[n]
    return self.ctx.name(n)

  def pr(self, e, prec=0):
    tok = e.tok
    fresh = tok is not None and tok.pos not in self.done
    if fresh: self.done.add(tok.pos)
    s = self.pr0(e, prec)
    return layout(tok, s) if fresh else s

  def paren(self, s, inner, outer):
    return '(' + s + ')' if inner < outer else s

  def pr_type(self, toks):
    try:
      ty = TypeParser(list(toks)).parse()
      return print_type(expand_type(ty, self.ctx.abbrevs), self.ctx)
    except Exception:
      pass
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

  def intvar(self, e):
    """does this expression hold an integer?  It does where it is
       a variable that holds one (a pattern binds such a variable
       where it is the argument of a constructor whose type there
       is int) or a sum or a product of such an expression"""
    while e.kind == 'paren': e = e.e
    if e.kind == 'id': return e.name in self.ctx.intvars
    if e.kind == 'infix' and e.op in ARITH:
      return self.intvar(e.l) or self.intvar(e.r)
    if e.kind == 'prefix' and e.op in ('-', '~'):
      return self.intvar(e.e)
    return False

  def pr0(self, e, prec):
    k = e.kind
    if k == 'id':
      n = e.name
      if n == '_': return self.ctx.fresh()
      if n in self.ctx.vars: return self.ctx.vars[n]
      if n in self.ctx.overloads:
        c = self.ctx.overloads[n]
        return c if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", c) \
               else '(' + c + ')'
      return self.ctx.name(n)
    if k == 'num':
      t = e.text
      if t.endswith('w'):
        return '(n2w ' + t[:-1] + ')'
      if t.endswith('i') or t.endswith('r'):
        return '(&' + t[:-1] + ')'
      if t.endswith('n') or t.endswith('c'):
        return t[:-1]
      if t.startswith('0x'):
        t = str(int(t, 16))
      if self.ctx.intnums:
        return '(&' + t + ')'
      return t
    if k == 'str':
      return e.text
    if k == 'chr':
      return '(CHR ' + str(ord(sml_char(e.text[2:-1]))) + ')'
    if k == 'mlstr':
      # the mlstring literal of HOL4: its constructor is implode,
      # and strlit is an overload of it
      return '(' + self.cname('strlit') + ' "' + e.text + '")'
    if k == 'paren':
      return '(' + self.pr(e.e, 0) + ')'
    if k == 'typed':
      ty = self.pr_type(e.ty)
      # a record literal may say its type, which is the only thing
      # that tells which record type it is where several of them
      # have the fields that it gives
      inner = e.e
      while inner.kind == 'paren': inner = inner.e
      if inner.kind == 'reclit':
        head = re.sub(r'^.*\)', '', ty).strip()
        if head in self.ctx.recs:
          old = self.ctx.reclit
          self.ctx.reclit = head
          try:
            return self.paren(self.pr(e.e, 1) + ':' + ty, 0, prec)
          finally:
            self.ctx.reclit = old
      # a numeral of type int or real is &n in HOL Light
      oldint = self.ctx.intnums
      if ty in ('int', 'real'): self.ctx.intnums = True
      try:
        body = self.pr(e.e, 1)
      finally:
        self.ctx.intnums = oldint
      return self.paren(body + ':' + ty, 0, prec)
    if k == 'app':
      hop, args = strip_app(e)
      old = self.numctx
      if hop.kind == 'id' and hop.name in NUMERIC_FUNS:
        self.numctx = True
      elif hop.kind == 'id':
        self.numctx = False
      if hop.kind == 'id':
        n = self.ctx.name(hop.name)
        if n in BINDERS and len(args) == 1 and args[0].kind == 'quant' \
           and args[0].q == '\\':
          vs = ' '.join(self.pr(v, APP) for v in args[0].vs)
          self.numctx = old
          return self.paren(n + ' ' + vs + '. ' +
                            self.pr(args[0].body, 0), 1, prec)
        if n in ARGPERM:
          ar, perm, newname = ARGPERM[n]
          if len(args) == ar:
            s = newname + ' ' + ' '.join(self.pr(args[i], APP)
                                         for i in perm)
            self.numctx = old
            return self.paren(s, PRE_APP, prec)
      # HOL4's ZIP takes the two lists as a pair
      if hop.kind == 'id' and len(args) == 1 and \
         self.ctx.name(hop.name) in UNCURRIED:
        a = args[0]
        while a.kind == 'paren': a = a.e
        if a.kind == 'infix' and a.op == ',':
          self.numctx = old
          return self.paren(self.ctx.name(hop.name) + ' ' +
                            self.pr(a.l, APP) + ' ' +
                            self.pr(a.r, APP), PRE_APP, prec)
      fn = self.pr(e.fn, PRE_APP)
      # a numeral in an argument of a constructor whose type is an
      # integer or a real is written &n
      oldint = self.ctx.intnums
      if hop.kind == 'id' and \
         self.ctx.con_argty.get((hop.name, len(args) - 1)) in \
           ('int', 'real'):
        self.ctx.intnums = True
      arg = self.pr(e.arg, APP)
      self.ctx.intnums = oldint
      self.numctx = old
      return self.paren(fn + ' ' + arg, PRE_APP, prec)
    if k == 'infix':
      op = e.op
      if op == '<>':
        return self.paren('~(' + self.pr(e.l, 12) + ' = ' +
                          self.pr(e.r, 13) + ')', PRE_APP, prec)
      if op == 'NOTIN':
        return self.paren('~(' + self.pr(e.l, 11) + ' IN ' +
                          self.pr(e.r, 12) + ')', PRE_APP, prec)
      if op == '$':
        return self.paren(self.pr(e.l, PRE_APP) + ' ' +
                          self.pr(e.r, APP), PRE_APP, prec)
      if op in ("'", "''", '--'):
        return self.paren(INFIX[op][2] + ' ' + self.pr(e.l, APP) + ' ' +
                          self.pr(e.r, APP), PRE_APP, prec)
      if op == '%%':
        return self.paren('word_bit ' + self.pr(e.r, APP) + ' ' +
                          self.pr(e.l, APP), PRE_APP, prec)
      _, assoc, hop, hprec = INFIX[op]
      # an infix that HOL Light does not have is written as an
      # application of the constant that HOL4 overloads it with
      if hprec is None:
        fn = self.ctx.overloads.get(hop) if self.ctx is not None \
             else None
        fn = '(' + fn + ')' if fn else self.ctx.name(hop)
        return self.paren(fn + ' ' + self.pr(e.l, APP) + ' ' +
                          self.pr(e.r, APP), PRE_APP, prec)
      old = self.numctx
      self.numctx = op in NUMCTX
      # the exponent of pow, EXP and ** is a natural number, also in
      # a definition whose other numerals are integers or reals
      oldint = self.ctx.intnums
      # a numeral next to a variable that holds an integer is &n
      if ((op in NUMCTX or op in ('=', '<>')) and
          (self.intvar(e.l) or self.intvar(e.r))):
        self.ctx.intnums = True
      # HOL Light's EXP is of natural numbers, so a power of an
      # integer is &(b EXP n) (dataSem's small_num has 2 ** 61 of
      # an integer); its pow is of a real, so a power of a real is
      # &b pow n (binary_ieee's float_round_with_flags has
      # 2 pow (bias (:'w)) of a real)
      if op in ('EXP', '**') and self.ctx.intnums:
        self.ctx.intnums = False
        s = ('&(' + self.pr(e.l, hprec) + ' ' + hop + ' ' +
             self.pr(e.r, hprec + 1) + ')')
        self.numctx = old
        self.ctx.intnums = oldint
        return self.paren(s, PRE_APP, prec)
      lp = hprec + 1 if assoc != 'l' else hprec
      rp = hprec if assoc == 'r' else hprec + 1
      l = self.pr(e.l, lp)
      if op in ('pow', 'EXP', '**'): self.ctx.intnums = False
      r = self.pr(e.r, rp)
      sep = '' if hop == ',' else ' '
      self.numctx = old
      self.ctx.intnums = oldint
      return self.paren(l + sep + hop + sep + r, hprec, prec)
    if k == 'prefix':
      if e.op == '~':
        # HOL4 writes ~ for the negation of a number and for the
        # complement of a word as well as for the negation of a
        # proposition; HOL Light writes -- and word_not for those
        if self.ctx.wordnot:
          return self.paren('word_not ' + self.pr(e.e, APP),
                            PRE_APP, prec)
        op = '--' if numeric(e.e) or self.numctx else '~'
        return self.paren(op + self.pr(e.e, PRE_APP), PRE_APP, prec)
      if e.op == '-':
        return self.paren('--' + self.pr(e.e, PRE_APP), PRE_APP, prec)
      if e.op == '&':
        # the argument of HOL4's & is a natural number, also in a
        # definition whose other numerals are integers or reals
        # (clos_to_bvlProof's cl_rel has Number (&(num_args - 1)))
        oldint = self.ctx.intnums
        self.ctx.intnums = False
        s = '&' + self.pr(e.e, APP)
        self.ctx.intnums = oldint
        return self.paren(s, PRE_APP, prec)
    if k == 'some':
      vs = ' '.join(self.pr(v, APP) for v in e.vs)
      return self.paren(self.ctx.name(e.name) + ' (\\' + vs + '. ' +
                        self.pr(e.body, 0) + ')', PRE_APP, prec)
    if k == 'quant':
      vs = ' '.join(self.pr(v, APP) for v in e.vs)
      return self.paren(e.q + vs + '. ' + self.pr(e.body, 0), 1, prec)
    if k == 'cond':
      s = ('if ' + self.pr(e.c, 0) + ' then ' + self.pr(e.a, 0) +
           ' else ' + self.pr(e.b, 0))
      return self.paren(s, 1, prec)
    if k == 'let':
      # HOL Light parses the binding of a let as a term and splits
      # it at the =, so what is bound to needs its parentheses
      # where it has an operator that binds looser than = does
      # (copying_gc's gc_move has let c = c /\ ... in)
      bs = ' and '.join(self.pr(p, 0) + ' = ' + self.pr(v, 13)
                        for p, v in e.binds)
      return self.paren('let ' + bs + ' in ' + self.pr(e.body, 0),
                        1, prec)
    if k == 'case':
      # a tuple of values or a tuple pattern needs its parentheses,
      # and so does a match, a let or a conditional in an arm
      arms = ' | '.join(self.pr(p, 15) + ' -> ' + self.pr(b, 2)
                        for p, b in e.arms)
      return self.paren('match ' + self.pr(e.s, 15) + ' with ' + arms,
                        1, prec)
    if k == 'field':
      return self.paren(self.ctx.field(e.fld) + ' ' + self.pr(e.e, APP),
                        PRE_APP, prec)
    if k == 'recupd':
      s = self.pr(e.e, APP)
      for i, (fld, v, fn) in enumerate(e.upds):
        s = (self.ctx.fupd(fld) + ' ' +
             (self.pr(v, APP) if fn else '(K ' + self.pr(v, APP) + ')')
             + ' ' + s)
        if i < len(e.upds) - 1: s = '(' + s + ')'
      return self.paren(s, PRE_APP, prec)
    if k == 'reclit':
      flds = [f for f, _, _ in e.upds]
      # the record type of a literal is the one whose fields are
      # exactly the ones of the literal; a field name on its own may
      # be one of several record types
      exact = [ty for ty, fs in self.ctx.recs.items()
               if set(fs) == set(flds)]
      part = [ty for ty, fs in self.ctx.recs.items()
              if set(flds) <= set(fs)]
      cand = exact or part
      rty = (self.ctx.reclit if self.ctx.reclit in part
             else cand[0] if len(cand) == 1
             else self.ctx.fields.get(flds[0], '?'))
      order = self.ctx.recs.get(rty, flds)
      vals = []
      for f in order:
        v = [v for g, v, _ in e.upds if g == f]
        vals.append(self.pr(v[0], APP) if v else 'ARB')
      return self.paren('mk_' + rty + ' ' + ' '.join(vals),
                        PRE_APP, prec)
    if k == 'list':
      return '[' + '; '.join(self.pr(i, 0) for i in e.items) + ']'
    if k == 'bag':
      s = self.ctx.name('EMPTY_BAG')
      for i in reversed(e.items):
        s = (self.ctx.name('BAG_INSERT') + ' ' + self.pr(i, APP) +
             ' (' + s + ')')
      return self.paren(s, PRE_APP, prec) if e.items else s
    if k == 'resq':
      nm = 'RES_FORALL' if e.q == '!' else 'RES_EXISTS'
      return self.paren(self.ctx.name(nm) + ' ' + self.pr(e.s, APP) +
                        ' (\\' + self.pr(e.v, APP) + '. ' +
                        self.pr(e.body, 0) + ')', PRE_APP, prec)
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
      # HOL4's ~ is the negation of a proposition, of a number and
      # the complement of a word
      if n == '~':
        if self.ctx.wordnot: return 'word_not'
        return ('(--)' if self.ctx.intnums or self.ctx.intneg
                else '(~)')
      if n in INFIX: return '(' + INFIX[n][2] + ')'
      # an operator that is not an identifier needs its parentheses
      if not n[0].isalpha() and n[0] != '_':
        return '(' + self.ctx.name(n) + ')'
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
      if len(e.stmts) == 1 and e.stmts[0][0] is None:
        return self.pr(e.stmts[0][1], prec)
      return self.paren(self.pr_do(e.stmts), PRE_APP, prec)
    raise SyntaxError(f'print: {k}')

  def mname(self, n):
    """the bind of the monad that the source has enabled, or the
       overloaded name that HOL4's monadsyntax uses"""
    c = MONAD[0].get(n) if MONAD[0] else None
    if c is None:
      c = 'monad_bind' if n == 'bind' else 'monad_ignore_bind'
      if c in self.ctx.overloads: return '(' + self.ctx.overloads[c] + ')'
      return self.ctx.name(c)
    return c

  def pr_do(self, stmts):
    (v, e) = stmts[0]
    if len(stmts) == 1:
      return self.pr(e, 0)
    rest = self.pr_do(stmts[1:])
    if v is None:
      # a monad without an ignorebind binds a variable that the
      # rest does not use, as HOL4's monad_unitbind does
      if MONAD[0] and not MONAD[0].get('ignorebind'):
        return (self.mname('bind') + ' ' + self.pr(e, APP) +
                ' (\\' + self.ctx.fresh() + '. ' + rest + ')')
      return (self.mname('ignorebind') + ' ' + self.pr(e, APP) +
              ' (' + rest + ')')
    return (self.mname('bind') + ' ' + self.pr(e, APP) + ' (\\' +
            self.pr(v, 0) + '. ' + rest + ')')


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


def head_of(e):
  """the head of an application, through parentheses, annotations
     and the operator form of HOL4 ($f)"""
  while True:
    if e.kind in ('paren', 'typed'): e = e.e
    elif e.kind == 'app': e = strip_app(e)[0]
    elif e.kind == 'dollar': return Node('id', tok=e.tok, name=e.name)
    else: return e


def conjuncts_of(e):
  """the conjuncts of a definition, as terms"""
  if e.kind == 'paren': return conjuncts_of(e.e)
  if e.kind == 'quant' and e.q == '!': return conjuncts_of(e.body)
  if e.kind == 'infix' and e.op == '/\\':
    return conjuncts_of(e.l) + conjuncts_of(e.r)
  return [e]


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
    while l.kind in ('paren', 'typed'): l = l.e
    hop, args = strip_app(l)
    hop = head_of(hop)
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


  def parse_dtarg(self):
    """one argument of a datatype constructor: an identifier or a
       parenthesised type, without absorbing what follows"""
    t = self.next()
    if t.kind == 'tyvar': return ('v', t.text)
    if t.kind in ('id', 'num'): return ('op', t.text, [])
    if t.text == '(':
      tys = [self.parse()]
      while self.at(','):
        self.next(); tys.append(self.parse())
      if not self.at(')'): raise SyntaxError('type: ) expected')
      self.next()
      if len(tys) == 1: return tys[0]
      name = self.next()
      return ('op', name.text, tys)
    raise SyntaxError(f'datatype argument: {t.text!r}')


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
  nm = ctx.tyname(name) if ctx is not None else name
  if not args: return nm
  if len(args) == 1:
    s = print_type(args[0], ctx, 6) + ' ' + nm
    return '(' + s + ')' if prec > 5 else s
  s = '(' + ','.join(print_type(a, ctx, 3) for a in args) + ')' + nm
  return '(' + s + ')' if prec > 5 else s


def type_vars_of(ty):
  if ty[0] == 'v': return [ty[1]]
  out = []
  for a in ty[2]:
    for v in type_vars_of(a):
      if v not in out: out.append(v)
  return out
