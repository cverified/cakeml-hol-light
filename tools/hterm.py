"""HOL4 term syntax -> HOL Light term syntax.

tokenize/parse a HOL4 term and print it as a HOL Light term,
keeping the line structure of the original.
"""
import os, re, sys

# ---------------------------------------------------------------
# tokens
# ---------------------------------------------------------------

UNI = {
  '∧': '/\\', '∨': '\\/', '¬': '~', '⇒': '==>', '⇔': '<=>',
  '∀': '!', '∃': '?', 'λ': '\\', '≤': '<=', '≥': '>=', '≠': '<>',
  '∈': 'IN', '∉': 'NOTIN', '⊆': 'SUBSET', '∪': 'UNION', '∩': 'INTER',
  '∅': '{}', '⧺': '++', '∘': 'o', '−': '-', '×': '*', '≼': '<<=',
  '⊂': 'PSUBSET', '≥': '>=', '⊕': '??',
  '⊑': 'SUBMAP', '≪': '<<', '≫': '>>', '⋙': '>>>',
  '⇎': '<>', '‖': '||', '↦': '|->',
}

# HOL4 prints the type variable 'a as α, 'b as β and so on, so
# the port maps them back (a source writes both, and they are the
# same variable: data_to_word's compile has stubs (:α) and
# (asm_conf:'a asm_config))
GREEK = dict(zip('αβγδεζηθικλμνξοπρςστυφχψω',
                 ["'" + c for c in 'abcdefghijklmnopqrstuvwxy']))

# the Greek letters that a CakeML source uses for a term variable
# and not for a type variable; HOL Light needs an ASCII name
GREEK_VAR = {'μ': 'mu', 'σ': 'sigma', 'τ': 'tau', 'ρ': 'rho'}

KEYWORDS = ['if', 'then', 'else', 'let', 'and', 'in', 'case', 'of',
            'do', 'od', 'with', 'otherwise', 'some']

# symbols, longest first
SYMS = ['<=>', '==>', '>>>', '#>>', '#<<', '<=+', '>=+', '||', '!!',
        '|==>', '===>', '###', '◁', '⦇', '⦈', '⊎', '⊌', '⋲',
        '&&',
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
    self.comments = ()   # the comments of the source before it

  def __repr__(self):
    return f'{self.kind}:{self.text}'


def split_top_sx(s, sep):
  """the parts of a text that a separator divides outside
     brackets and strings"""
  out = []; cur = ''; d = 0; i = 0
  while i < len(s):
    c = s[i]
    if c == '"':
      j = i + 1
      while j < len(s) and s[j] != '"':
        j += 2 if s[j] == '\\' else 1
      cur += s[i:j+1]; i = j + 1; continue
    if c in '([{' or c == '\u27ea': d += 1
    elif c in ')]}' or c == '\u27eb': d -= 1
    if d == 0 and s.startswith(sep, i):
      out.append(cur); cur = ''; i += len(sep); continue
    cur += c; i += 1
  out.append(cur)
  return out


def expand_sx(s):
  """HOL4's simpleSexp writes an s-expression list as
     \u27eax; y; z\u27eb (the SX_CONS of the elements, ending in
     nil) and a cons as \u27eah \u2022 t\u27eb (add_listform and
     add_rule of simpleSexpScript); the port writes the
     constants out.  The innermost brackets go first, so that
     the nested ones come out as well"""
  while True:
    j = s.find('\u27eb')
    if j < 0: return s
    i = s.rfind('\u27ea', 0, j)
    if i < 0: return s
    inner = s[i+1:j]
    parts = split_top_sx(inner, '\u2022')
    if len(parts) == 2:
      out = '(SX_CONS (%s) (%s))' % (parts[0], parts[1])
    else:
      items = [x for x in split_top_sx(inner, ';') if x.strip()]
      out = 'nil'
      for x in reversed(items):
        out = '(SX_CONS (%s) %s)' % (x, out)
    s = s[:i] + out + s[j+1:]


# HOL4 writes a run of primes as a superscript (bvi_tmcProof's
# hypothesis has a variable s'3' as s followed by a prime, a
# superscript three and a prime), which HOL Light cannot read
SUPERSCRIPT = {'\u2070': '0', '\u00b9': '1', '\u00b2': '2',
               '\u00b3': '3', '\u2074': '4', '\u2075': '5',
               '\u2076': '6', '\u2077': '7', '\u2078': '8',
               '\u2079': '9'}


# and a name with a subscript (mlstring's isprefix_thm is about
# s and s with a subscript one)
SUBSCRIPT = {chr(0x2080 + i): str(i) for i in range(10)}


def ascii_name(nm):
  """the name with the superscripts and the subscripts of HOL4 as
     plain digits"""
  return ''.join(SUPERSCRIPT.get(c, SUBSCRIPT.get(c, c)) for c in nm)


# a theory in front of a symbolic name (misc's prim_rec$< is the
# < of the numbers): the name after the $ is what it means, and
# the $ of HOL4 before an operator is how the port already reads
# the operator as a function
QUAL_SYM = re.compile(r"\b[A-Za-z][A-Za-z0-9_']*\$(?=[-+*/<>=!?~^&|#%:@])")


# the tokens that no term starts at: a comment before one of them
# belongs to the term after it
NOHEAD = set([')', ']', '}', '|>', ';', ',', ':=', '.', '|', 'then',
              'else', 'in', 'of', 'updated_by', '=>', '->',
              # a bracket that opens is no term of its own either:
              # the comment goes to the term inside it, which is
              # where the port can write it again (the clauses of
              # a definition are (f x = y) /\ (* a comment *) (f z
              # = w), and the parentheses are gone by then)
              '(', '['])


def tokenize(s):
  s = expand_sx(s) if '\u27ea' in s else s
  s = QUAL_SYM.sub('$', s)
  toks = []
  pend = []
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
      # the comment belongs to the token that follows it, which
      # is where the port writes it again (as the // comment of
      # HOL Light, which runs to the end of the line)
      pend.append((j, s[i:j]))
      i = j; continue
    # a // comment, so that the port can read its own terms again
    if s.startswith('//', i):
      j = s.find('\n', i)
      i = n if j < 0 else j
      continue
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
        # an ML value that the port does not have: a statement
        # that antiquotes one is a term that HOL4 builds with ML
        # code, and the port points at the source instead of
        # writing the name as a variable (bvl_const's
        # SmartOp2_pmatch is a ^tm of its own).  In a definition
        # the name stays, and the definition is assumed with it
        # free, which ml/CHEATS.md reports.
        if ANTIQ_STRICT[0]:
          raise SyntaxError('the ML value ^%s, which the port does'
                            ' not have' % nm)
        toks.append(Tok('id', nm, start, nl, icol))
        i = j; col += j - i; nl = 0; continue
      # ^(name) : HOL4 splices in the value of the ML expression
      # between the parentheses, which for the sources of the port
      # is a name of ANTIQ (the configurations of the targets)
      if s[i+1] == '(':
        d, k = 0, i + 1
        while k < n:
          if s[k] == '(': d += 1
          elif s[k] == ')':
            d -= 1
            if not d: break
          k += 1
        nm = s[i+2:k].strip()
        if nm in ANTIQ:
          toks.append(Tok('sym', '(', start, nl, icol))
          toks += [x for x in tokenize(ANTIQ[nm]) if x.kind != 'eof']
          toks.append(Tok('sym', ')', start, 0, icol))
          i = k + 1; nl = 0; continue
        # an ML expression that the port cannot evaluate: a
        # statement that is one is a pointer at the source, and
        # not the ML read as a term (wordProps' evaluate_clock_const
        # is the conjunction that an ML function of the source
        # builds out of the goals of an induction theorem)
        if ANTIQ_STRICT[0]:
          raise SyntaxError('the ML expression ^(%s...), which the'
                            ' port cannot evaluate'
                            % ' '.join(nm.split())[:30])
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
      w = ascii_name(s[i:j])
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
  # every comment of the source goes to the first token after it
  # that a term can start at, which is where the printer writes it
  # again: an operator or a bracket that closes is no such token
  # (backend_common's word_num_stubs has stack_num_stubs + 1
  # (* raise *) + 1, whose comment would be lost on the +)
  for end, txt in pend:
    for t in toks:
      if (t.pos >= end and t.kind != 'eof' and t.text not in NOHEAD
          and (t.kind != 'sym' or t.text not in INFIX)):
        t.comments = t.comments + (txt,)
        break
    else:
      # a comment at the end of the term has no token to stand
      # before, and it goes to the end of the term itself
      # (backend_common's word_num_stubs ends in (* store consts *))
      toks[-1].comments = toks[-1].comments + (txt,)
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
  # no precedence: HOL Light has neither infix, so the port
  # writes the application (a source that overloads ++ with an
  # append of its own has that one, ctx.overloads)
  '++':    (480, 'l', '++',     None),
  '::':    (490, 'r', '::',     None),
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
  # HOL4 writes the bitwise or of two words as || and as !!
  '!!':    (650, 'l', '||',     16),
  '??':    (650, 'l', '??',     16),
  '<<':    (680, 'l', '<<',     23),
  '>>':    (680, 'l', '>>',     23),
  '>>>':   (680, 'l', '>>>',    23),
  '#>>':   (680, 'l', '#>>',    23),
  '#<<':   (680, 'l', '#<<',    23),
  '@@':    (700, 'l', '@@',     23),
  'o':     (800, 'r', 'o',      26),
  '##':    (490, 'r', '##',     20),
  # HOL4 declares only the symbol of these an infix, so the name
  # itself is an identifier there (misc's FOLDR BAG_UNION b0 ls)
  '⊎':     (500, 'l', 'BAG_UNION', None),
  '⊌':     (500, 'l', 'FUNION', None),
  'SUBMAP':(450, 'n', 'SUBMAP', 12),
  '⋲':     (450, 'n', 'BAG_IN', None),
  # the walkstar of HOL4's unification library, which it writes
  # s <| t (with a triangle)
  '◁':     (700, 'r', 'walkstar', None),
  'f_o_f': (800, 'r', 'f_o_f', 26),
  # HOL4 declares these infixes by name (pairTheory's LEX with
  # new_infixr_definition, finite_mapTheory's o_f)
  'LEX':   (490, 'r', 'LEX', 14),
  'o_f':   (800, 'r', 'o_f', 26),
  # the composition of two relations of HOL4's relationTheory
  'O':     (800, 'r', 'O', None),
  # the relation between two functions of HOL4's transfer library
  # and the relation between two pairs of its pairTheory
  '|==>':  (490, 'r', 'FUN_REL', None),
  '===>':  (490, 'r', 'FUN_REL', None),
  '###':   (490, 'r', 'RPROD', None),
  'RSUBSET':(450, 'n', 'RSUBSET', None),
  'RINTER':(600, 'l', 'RINTER', None),
  'RUNION':(500, 'l', 'RUNION', None),
  '$':     (460,  'r', '$',      0),
  "'":     (2000, 'l', 'FAPPLY', 0),
  "''":    (350, 'l', 'word_slice', 0),
  '--':    (350, 'l', 'word_bits', 0),
  '%%':    (400, 'l', 'word_bit', 0),
  '=+':    (320, 'n', '=+',     23),
  '><':    (350, 'l', '><',     23),
  '<*>':   (500, 'l', 'OPTION_APPLY', None),
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
    e = self.closures(self.parse_fields(self.parse_atom()))
    while self.starts_atom(True):
      a = self.closures(self.parse_fields(self.parse_atom()))
      e = Node('app', tok=e.tok, fn=e, arg=a)
    e = self.parse_with(e)
    if annot and self.at(':'):
      self.next()
      ty = self.parse_type()
      e = Node('typed', tok=e.tok, e=e, ty=ty)
    return e

  def closures(self, e):
    """R^* is RTC R and R^+ is TC R (relationTheory); they bind
       tighter than an application does, so every atom takes
       them (walkstar's walkstarR has mlt1 (vR s)^+)"""
    while self.peek().text == '^' and \
          self.peek(1).text in ('*', '+') and \
          self.peek(1).pos == self.peek().pos + 1:
      self.next()
      e = mk_app('RTC' if self.next().text == '*' else 'TC', [e])
    return e

  def parse_with(self, e):
    """HOL4's r with fld := v binds looser than an application, so
       initial_state f c co cc k with clock := k1 is the update of
       the state that initial_state gives and not of its last
       argument"""
    while self.peek().text == 'with':
      t = self.next()
      if self.at('<|'):
        self.next()
        upds = self.parse_updates()
        self.expect('|>')
      else:
        upds = self.parse_updates(single=True)
      e = Node('recupd', tok=t, e=e, upds=upds)
    return e

  def parse_fields(self, e):
    while True:
      t = self.peek()
      if t.text == '.' and self.peek(1).kind == 'id':
        self.next(); fld = self.next()
        e = Node('field', tok=t, e=e, fld=fld.text)
      # fm⟨k ↦ v⟩ is fm |+ (k,v) and fm⟨k⟩ is fm ' k (the finite
      # map syntax of HOL4's combinpp), which binds to the atom
      # before it (FAPPLY tf⟨ts2 ↦ x⟩ applies FAPPLY to the map)
      elif t.text == '⟨':
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
      # HOL4 writes the update of a function f⦇k ↦ v⦈, which is
      # the (k =+ v) f of its combinTheory
      elif t.text == '⦇':
        self.next()
        while True:
          k = self.parse(101)
          self.expect('|->')
          v = self.parse(0)
          e = Node('app', tok=t, fn=Node('paren', tok=t,
                     e=Node('infix', tok=t, op='=+', l=k, r=v)), arg=e)
          if self.at(';'): self.next(); continue
          break
        self.expect('⦈')
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

  def parse_updates(self, single=False):
    upds = []
    while True:
      fld = self.next()
      # HOL4 has r with fld := v and r with fld updated_by f
      if self.peek().text == 'updated_by':
        self.next(); fn = True
      else:
        self.expect(':='); fn = False
      # the value of an update binds tighter than = and /\ in
      # HOL4 (D with locals := D.locals = D is an equation, and
      # word_bignumProof's reg_write has a clause after the /\),
      # so it stops at an operator of the precedence of = as well
      v = self.parse(451)
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
      res = None
      if t.text == '(':
        v = self.parse_atom()
        # the restriction of a binder may be inside the
        # parentheses, with a pattern in front of it
        # (typeSystem's !((p,e) :: LIST_TO_SET pes). P)
        w = v
        while w.kind == 'paren': w = w.e
        if w.kind == 'infix' and w.op == '::':
          res = w.r
          v = Node('paren', tok=v.tok, e=w.l)
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
      if res is not None: groups[-1][-1].res = res
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
      # the body of an arm reaches over a comma, as it does in
      # HOL4 (data_to_word's assign_WordFromInt gives back
      # case ... of NONE => (GiveUp,l) | SOME h => (if ...), l)
      b = self.parse(50)
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
      # a prefix takes the infixes that bind tighter than it does
      # with it: the ' of HOL4 is the bit of a word, so
      # data_to_word_memoryProof's ~(Smallnum i:'a word) ' 0 says
      # that the bit is not set, and not that it is the bit of the
      # complement
      if t.text == '~':
        e = self.parse_infix(self.parse_atoms(), PREFIX['~'][0])
        return Node('prefix', tok=t, op='~', e=e)
      if t.text == '-':
        e = self.parse_infix(self.parse_atoms(), PREFIX['-'][0])
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


# a HOL4 function whose HOL Light counterpart takes the same
# arguments in another order: the arity, the permutation and the
# name, longest arity first
ARGPERM = {
  'FOLDR': [(3, [0, 2, 1], 'ITLIST')],
  # HOL4's FUNPOW f n x is the ITER n f x of Library/iter.ml
  'FUNPOW': [(2, [1, 0], 'ITER')],
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
  while e.kind in ('paren', 'typed', 'rawtyped'): e = e.e
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


def ident_names(e):
  """every name that occurs as an identifier in a term"""
  out = set()
  def go(x):
    if isinstance(x, Node):
      if x.kind == 'id' and getattr(x, 'name', None):
        out.add(x.name)
      for k, v in x.__dict__.items():
        if k != 'tok': go(v)
    elif isinstance(x, (list, tuple)):
      for v in x: go(v)
  go(e)
  return out


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


# the places where the port leaves a record field to HOL Light to
# resolve: it writes the name that overloads the accessors of the
# field, and the type of the record decides which one it is
AMBUSE = []


class Ctx:
  """what the printer needs to know about the port"""

  def __init__(self, names=None, fields=None, recs=None, thy='',
               overloads=None, accessors=None, cons=None,
               ambfields=None, updaters=None,
               abbrevs=None, tynames=None, overloaded=None,
               con_argty=None, defnames=None, rectys=None):
    self.names = names or {}     # cakeml name -> hol light name
    self.tynames = tynames or {} # the same for the type names
    self.con_argty = con_argty or {}  # (con,index) -> type text
    self.overloaded = overloaded or set()  # names HOL4 overloads
    self.defnames = defnames or set()  # the constants in scope
    self.defining = set()        # the names of the block being made
    self.fields = fields or {}   # field name -> record type name
    self.recs = recs or {}       # record type -> [field names]
    self.rectys = rectys or {}   # record type -> {field: type text}
    self.qualfields = False      # write out the accessor of a
                                 # field instead of the name that
                                 # overloads the accessors of it
    self.hidden = set()          # the names that this file hides
    self.ambfields = ambfields or {}  # field -> overloaded name
    self.reclit = None           # the record type of a literal
    self.reclits = []            # ... of the literals in order
    self.recdflt = {}            # field -> the record it is of by
                                 # default, where several have it
    self.overloads = overloads or {}   # name -> hol light term text
    self.accessors = accessors or {}   # field name -> accessor name
    self.updaters = updaters or {}     # field name -> update name
    self.cons = cons or set()          # the constructor names
    self.tyops = set()                 # the type names in scope
    self.abbrevs = abbrevs or {}       # type abbreviation -> type
    self.intnums = False               # are numerals integers here?
    self.intneg = False                # is $~ the negation of an int?
    self.intvars = set()               # variables holding integers
    self.armvars = {}                  # arm body -> its integer
                                       # variables (a match arm
                                       # binds its own)
    self.vars = {}                     # bound variables to rename
    self.wordnot = False               # is ~ the word complement?
    self.wordnotvars = set()           # ... of these variables
    self.append = False                # is ++ the append of lists?
    self.fieldvar = {}                 # variable -> its record
    self.iffeq = False                 # is <=> plain equality?
    self.thy = thy
    self.wild = 0
    self.warn = []

  def size_name(self, n, thy=None):
    """the name of the size function of a datatype, which is
       called after the type (HOL4's closLang$exp_size is
       closLang_exp_size).  The auxiliary size functions of a
       family (HOL4's exp1_size, exp2_size, ...) are not
       translated: HOL Light numbers the types of a family in
       another order than HOL4 does (of closLang's exp, HOL4's
       exp1_size is the one of a (num # exp) list and ours is the
       one of an exp list), and a name of HOL4 that this gave the
       size function of another type would be a type error."""
    if not n.endswith('_size'): return None
    base = n[:-len('_size')]
    if not base: return None
    ty = self.tyname(base if thy is None else thy + '$' + base)
    if ty == base: return None
    return ty + '_size'

  def case_name(self, n, thy=None):
    """the name of the case constant of a datatype, which HOL4
       calls after the type (its tag_CASE is the case constant of
       reg_alloc's tag, which the port calls reg_alloc_tag)"""
    if not n.endswith('_CASE'): return None
    base = n[:-len('_CASE')]
    if not base: return None
    ty = self.tyname(base if thy is None else thy + '$' + base)
    if ty == base: return None
    return ty + '_CASE'

  def name(self, n):
    if '$' in n:
      thy, n2 = n.split('$')
      if (thy, n2) in self.names or n2 in self.names:
        return self.names.get((thy, n2), self.names.get(n2, n2))
      return self.size_name(n2, thy) or self.case_name(n2, thy) or n2
    if n in NAME_MAP: return NAME_MAP[n]
    # the block that defines a name uses the name of the constant,
    # and everything else the name that HOL4 overloads with it
    if n in self.defining:
      return self.names.get((self.thy, n), self.names.get(n, n))
    if n in self.overloaded: return n
    # the size function of a datatype is called after the type, so
    # it follows the name that the port gives the type (HOL4's
    # exp_size of closLang is closLang_exp_size)
    # a name that a theory in scope defines as a constant of its
    # own is that constant, not the size function of a datatype
    # (wordSem's stack_size is a function of a stack frame list,
    # and dataSem's stack is a datatype whose size function HOL4
    # would call stack_size as well)
    if (n.endswith('_size') and (self.thy, n) not in self.names
        and n not in self.names and n not in self.defnames):
      sz = self.size_name(n)
      if sz: return sz
    # the case constant of a datatype follows the name of the type
    # as well (HOL4's tag_CASE is reg_alloc_tag_CASE here)
    if (n.endswith('_CASE') and (self.thy, n) not in self.names
        and n not in self.names and n not in self.defnames):
      cs = self.case_name(n)
      if cs: return cs
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
    # the body of an overload is read in the theory that declares
    # it, so the accessor of a field of it is written out: a
    # statement that uses the name of the field for a variable of
    # its own is read with the overloads of the field names taken
    # away, and the name in the body of the overload would be that
    # variable then (labSem's read_reg is the regs of a labSem
    # state, and stack_to_labProof's compile_jump_correct has a
    # variable regs)
    if self.qualfields:
      if f in self.fields: return self.fields[f] + '_' + f
      # the field is of several records in the scope of that
      # theory, and the one it means is the record of the theory
      # itself (the regs of labSem's read_reg is the one of a
      # labSem state and not of an asm_state)
      own = [r for r, fs in self.recs.items()
             if f in fs and r.startswith(self.qualfields + '_')]
      if len(own) == 1: return own[0] + '_' + f
    # the name of a field that several record types have is an
    # overload of their accessors, which HOL Light resolves by the
    # type of the record, as HOL4 does -- unless the file hides
    # that name, where the accessor has to be written out
    # (labProps hides mem, which HOL4's field syntax reads all the
    # same: overrides.ACCESSORS says which record it is of)
    if (f in self.ambfields and f not in self.fields
        and self.ambfields[f] not in self.hidden):
      AMBUSE.append((self.thy, f, self.ambfields[f]))
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


def _int_arg_pos():
  """the arguments of the constants of the port whose type is int:
     a numeral in such a place is &n in HOL Light, and a variable
     there holds an integer.  An entry i.j says that the argument
     i is a function whose argument j is an integer, so that a
     lambda there binds an integer (linear_scan's
     check_number_property_strong takes a property of a number of
     an instruction, which is an int).  The table comes from the
     types that the port gives its constants, which
     tools/bin/intargs dumps out of a session."""
  out = {}
  f = os.path.dirname(os.path.abspath(__file__)) + '/intargs.txt'
  try:
    for l in open(f):
      nm, ps = l.rstrip('\n').split('\t')
      if nm.startswith('_'): continue
      args = set(); fns = {}
      for p in ps.split(','):
        if '.' in p:
          i, j = p.split('.')
          fns.setdefault(int(i), set()).add(int(j))
        else:
          args.add(int(p))
      out[nm] = (args, fns)
  except OSError:
    pass
  return out


INT_ARGS_OF = _int_arg_pos()


def _int_result_fns():
  """the constants of the port whose result is an integer
     (tools/intres.txt, which tools/bin/intargs writes out of a
     session): a numeral beside an application of one is &n"""
  out = set()
  f = os.path.dirname(os.path.abspath(__file__)) + '/intres.txt'
  try:
    for l in open(f):
      if l.strip(): out.add(l.strip())
  except OSError:
    pass
  return out


INT_RESULT_FNS = _int_result_fns()


def _port_constants():
  """the name of every constant of the port (tools/constants.txt,
     which tools/bin/intargs writes out of a session): an
     application of one that is not in tools/intres.txt is of
     another type than int, so a numeral beside it is a numeral of
     that type and not &n"""
  out = set()
  f = os.path.dirname(os.path.abspath(__file__)) + '/constants.txt'
  try:
    for l in open(f):
      if l.strip(): out.add(l.strip())
  except OSError:
    pass
  return out


PORT_CONSTANTS = _port_constants()


def int_arg_pos(nm):
  """the arguments of a constant whose type is int"""
  return INT_ARGS_OF.get(nm, (set(), {}))[0]


def int_fn_arg_pos(nm):
  """the arguments of a constant that are a function with an
     integer argument of their own"""
  return INT_ARGS_OF.get(nm, (set(), {}))[1]

# the constants that give an element of a list, a map or an option:
# a numeral beside one of them applied to a container of integers
# is an integer itself
ELEM_FUNS = set(['the', 'THE', 'EL', 'HD', 'LAST', 'sptree_lookup',
                 'FLOOKUP', 'FAPPLY'])

# the type int in the text of the type of a field of a record
INT_TY = re.compile(r"\bint\b")

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


def sml_string_bytes(s):
  """the bytes that the body of an SML string literal denotes"""
  out = bytearray()
  i = 0
  while i < len(s):
    if s[i] == '\\' and i + 1 < len(s):
      j = i + 1
      if s[j].isdigit():
        k = j
        while k < len(s) and s[k].isdigit() and k - j < 3: k += 1
        out.append(int(s[j:k]) % 256); i = k; continue
      if s[j] == 'u':
        out.extend(chr(int(s[j+1:j+5], 16)).encode('utf-8'))
        i = j + 5; continue
      out.extend(sml_char(s[i:i+2]).encode('utf-8')); i += 2; continue
    out.extend(s[i].encode('utf-8')); i += 1
  return out


# how a byte of a string literal is written for HOL Light, whose
# lexer reads the escapes of OCaml (and not the \a, \f, \v and
# \u of SML); a backquote would close the quotation of the port,
# so it is written as the decimal escape
OCAML_ESC = {0x5c: '\\\\', 0x22: '\\"', 0x0a: '\\n', 0x09: '\\t',
             0x0d: '\\r', 0x08: '\\b', 0x60: '\\096'}


def hl_string(body):
  """the body of a string literal of HOL4 as one of HOL Light: the
     escapes of SML are read and written again in the style that
     HOL Light's lexer knows.  A literal of more than fifty
     characters is split, so that the lines of the port can stay
     short (the two pieces are appended)"""
  units = []
  for b in sml_string_bytes(body):
    if b in OCAML_ESC: units.append(OCAML_ESC[b])
    elif 32 <= b < 127: units.append(chr(b))
    else: units.append('\\%03d' % b)
  parts, cur, n = [], [], 0
  for u in units:
    if n + len(u) > 50 and cur:
      parts.append('"%s"' % ''.join(cur)); cur, n = [], 0
    cur.append(u); n += len(u)
  if cur: parts.append('"%s"' % ''.join(cur))
  if not parts: return '""'
  if len(parts) == 1: return parts[0]
  # the pieces are appended, and HOL Light's append is APPEND
  out = parts[-1]
  for i, q in enumerate(reversed(parts[:-1])):
    out = 'APPEND %s %s' % (q, out if not i else '(' + out + ')')
  return '(' + out + ')'


SYMCHARS = set('\\!@#$%^&*-+<>/?|~=:')


def sym_space(op, s):
  """a space between a symbolic prefix and what follows it where
     the two would be read as one symbol (HOL Light's lexer takes
     the longest one, so --&n is not -- and &n)"""
  return ' ' + s if (op and s and op[-1] in SYMCHARS and
                     s[0] in SYMCHARS) else s


def wordlit(e):
  """is this term a word literal of HOL4 (0w, 1w, 0xFFw)?  The ~ of
     a word is its complement and not the negation of a number, so
     ~0w is the word of all ones and not 0w"""
  while e.kind in ('paren', 'typed', 'rawtyped'): e = e.e
  return e.kind == 'num' and e.text.endswith('w')


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


def first_tok(e):
  """the token of a term that comes first in the source"""
  best = [None]

  def go(x):
    if not isinstance(x, Node): return
    t = getattr(x, 'tok', None)
    if t is not None and (best[0] is None or t.pos < best[0].pos):
      best[0] = t
    for k, v in x.__dict__.items():
      if k == 'tok': continue
      if isinstance(v, Node): go(v)
      elif isinstance(v, (tuple, list)):
        for y in v:
          if isinstance(y, Node): go(y)
          elif isinstance(y, (tuple, list)):
            for z in y:
              if isinstance(z, Node): go(z)

  go(e)
  return best[0]


def pop_comments(e):
  """the comments of the source before a term, taken off its first
     token: a clause of a definition that the port writes as the
     arm of a match is a term of its own there, and the comment
     before it goes before the arm"""
  t = first_tok(e)
  if t is None or not t.comments: return []
  cs = [comment_text(c) for c in t.comments
        if not any(q in c for q in QUOTES)]
  t.comments = ()
  return cs


def pop_quoted_comments(e):
  """the comments before a term that cannot stand in a quotation:
     one with a quote in it would end the quotation of OCaml that
     the term of the port stands in, so the port writes it outside
     (bvi_let's compile has `Let xs (Return (GENLIST Var n))` in
     one of its comments)"""
  t = first_tok(e)
  if t is None or not t.comments: return []
  out = [comment_text(c) for c in t.comments
         if any(q in c for q in QUOTES)]
  t.comments = tuple(c for c in t.comments
                     if not any(q in c for q in QUOTES))
  return out


def comment_text(c):
  """the lines of a comment of a source, without its brackets and
     without the indent that the source gave it"""
  t = c[2:-2] if c.startswith('(*') and c.endswith('*)') else c
  lines = [l.strip() for l in t.split('\n')]
  while lines and not lines[0]: lines.pop(0)
  while lines and not lines[-1]: lines.pop()
  return lines or ['']


# a comment that has a quotation in it would end the quotation of
# OCaml that the term of the port stands in
QUOTES = '`\u2018\u201c\u2019\u201d'


def layout(tok, s):
  cs = [c for c in (getattr(tok, 'comments', ()) if tok else ())
        if not any(q in c for q in QUOTES)]
  # a comment of the source that stands before this token: HOL
  # Light reads // to the end of the line in a term quotation, so
  # the comment keeps its place and its text
  if cs:
    ind = ' ' * max(tok.indent, 2)
    out = '\n' * max(tok.nl, 1)
    for c in cs:
      out += '\n'.join(ind + '// ' + l for l in comment_text(c))
      out += '\n'
    return out + ind + s
  if tok is not None and tok.nl:
    return '\n' * tok.nl + ' ' * tok.indent + s
  return s


def sameline(s):
  """the text without the line break that the layout of the source
     put in front of it: what the port writes before it (the ~( of
     a negation) would be alone on a line of its own.  A comment
     that stands there keeps its line, or the term after it would
     be in the comment"""
  if re.match(r'^\n+[ ]*//', s): return s
  return re.sub(r'^\n+[ ]*', '', s)


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

# the constants that the library layer of the port declares as
# infixes of HOL Light: where one of them is applied to its
# arguments the port writes its name in parentheses
HL_INFIX = {'BAG_UNION', 'LEX', 'o_f', 'SUBMAP'}
# (and not PERMUTES or f_o_f, which the port writes as the
# infixes they are: this set is the names that need their
# brackets where the port writes them as a function)

# the infixes of HOL Light whose name is a word: one of
# these standing where a function stands needs its brackets,
# or the parser reads what follows as the right operand
# (MAPi (o (o FST) f) l is unparsed input).  A symbolic
# infix needs them too and is caught by its first character.
# The list is HOL Light's own parse_as_infix calls.
HL_WORD_INFIX = set("""
  CROSS DELETE DIFF div DIV divides DIV EXP has_inf
  HAS_SIZE has_sup IN INSERT INTER INTERSECTION_OF MOD o
  PCROSS pow PSUBSET rem SUBSET treal_add treal_eq
  treal_le treal_mul UNION UNION_OF zpow""".split())


def as_function(nm):
  """a name that stands where a function stands, with the
     brackets round it only where HOL Light would otherwise read
     it as an infix or a binder: (APPEND) is noise, (o) is not"""
  if (nm in HL_INFIX or nm in HL_WORD_INFIX or nm in BINDERS
      or not re.match(r"^[A-Za-z_]", nm)):
    return '(' + nm + ')'
  return nm


MONAD = [None]         # the monad that a source has enabled
ANTIQ = {}             # the ML values that a source antiquotes
# with this, an ML value that ANTIQ does not have is an error and
# not a variable: a statement of phase two that antiquotes one is
# a term that HOL4 builds with ML code, and the port cannot state
# it (tools/port.py sets this while it reads a statement)
ANTIQ_STRICT = [False]
# with this, an annotation that has a type variable in it is left
# out of a statement (overrides.THM_NO_TYVARS)
DROP_TYVAR_ANNOT = [False]
# with this, the type variables of an annotation of a statement are
# the ones of the first annotation of the same type operator in it:
# HOL4 unifies the type variables that a statement writes and HOL
# Light reads a written one as rigid, so the two states of
# bvlProps$do_app_Rval_swap (('a,'b) and ('c,'d)) are one state
# there and two here (overrides.THM_TYVARS).  Leaving the
# annotation out is worse: it takes the record type with it, and
# nothing then says which semantics the statement is about.
UNIFY_TYVAR_ANNOT = [False]
TYVAR_SEEN = {}

# an annotation of a type operator applied to type variables, which
# is the only kind that is unified: ('a,'b)bvlSem_state and the
# one argument form 'ffi semanticPrimitives_state
ANNOT_ARGS = re.compile(r"^\(([^()]*)\)([A-Za-z0-9_']+)$")
ANNOT_ARG = re.compile(r"^('[A-Za-z0-9_]+)\s+([A-Za-z0-9_']+)$")
TYVAR = re.compile(r"^'[A-Za-z0-9_]+$")


def unify_annot(ty):
  """the annotation with the type variables of the first annotation
     of the same type operator in this statement"""
  m = ANNOT_ARGS.match(ty)
  if m:
    args = [a.strip() for a in m.group(1).split(',')]
    op = m.group(2)
  else:
    m = ANNOT_ARG.match(ty)
    if not m: return ty
    args, op = [m.group(1)], m.group(2)
  if not all(TYVAR.match(a) for a in args): return ty
  key = (op, len(args))
  if key not in TYVAR_SEEN:
    TYVAR_SEEN[key] = args
    return ty
  args = TYVAR_SEEN[key]
  return ('(%s)%s' % (','.join(args), op) if len(args) > 1
          else '%s %s' % (args[0], op))


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


def set_infix_lambda(tok):
  """a symbolic infix that a CakeML source overloads with a term
     of its own (cmlPtreeConversion's ' is the bind of the option
     monad, not the application of a finite map) is written as an
     application of that term, which ctx.overloads has"""
  if tok in INFIX:
    prec, assoc, _, _ = INFIX[tok]
    INFIX[tok] = (prec, assoc, tok, None)


def set_equality(loose):
  """HOL4's ParseExtras.loose_equality puts = at precedence 100,
     where it binds looser than /\\, and tight_equality back at 450,
     where it binds tighter (which is HOL4's default)"""
  _, assoc, hop, hprec = INFIX['=']
  INFIX['='] = (100 if loose else 450, assoc, hop, hprec)


AUXSIZE = re.compile(r"^[A-Za-z][A-Za-z0-9_']*?\d+_size$")


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

  def annot_rec(self, e):
    """the record type that an annotation of a term says it is, if
       the term has one: a field of an annotated record is read
       with the accessor of that record and not with the
       overloaded name of the field"""
    while e.kind == 'paren': e = e.e
    if e.kind != 'typed': return None
    try: ty = self.pr_type(e.ty)
    except Exception: return None
    head = re.sub(r'^.*\)', '', ty).strip().split()
    head = head[-1] if head else ''
    return head if head in self.ctx.recs else None

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

  def updfn(self, v, rec, fld):
    r"""the function of an updated_by: its argument is the field
        and not the record, so a lambda there binds a variable of
        the record type of the field (backend_passes' to_bvi_all
        has c with clos_conf updated_by (\c. c with start := s),
        whose inner c is a config of clos_to_bvl)"""
    w = v
    while w.kind == 'paren': w = w.e
    if not (w.kind == 'quant' and w.q == '\\' and len(w.vs) == 1
            and w.vs[0].kind == 'id'):
      return self.pr(v, APP)
    tys = ([self.ctx.rectys.get(rec, {}).get(fld)] if rec else
           [ftys[fld] for ftys in self.ctx.rectys.values()
            if fld in ftys])
    tys = [t for t in tys if t]
    if len(set(tys)) != 1: return self.pr(v, APP)
    r2 = self.ctx.tyname(tys[0])
    if r2 not in self.ctx.recs: return self.pr(v, APP)
    old = self.ctx.fieldvar
    self.ctx.fieldvar = dict(old)
    self.ctx.fieldvar[w.vs[0].name] = r2
    try:
      return self.pr(v, APP)
    finally:
      self.ctx.fieldvar = old

  def fldtys(self, e):
    """the types that the field of a record expression can have:
       the one of the record that the annotation or the overrides
       name, or the ones of every record in scope that has the
       field"""
    rec = self.annot_rec(e.e)
    if rec and e.fld not in self.ctx.recs.get(rec, []): rec = None
    if not rec:
      v = e.e
      while v.kind in ('paren', 'typed', 'rawtyped'): v = v.e
      rec = (self.ctx.fieldvar.get(v.name)
             if v.kind == 'id' else None)
      if rec and e.fld not in self.ctx.recs.get(rec, []): rec = None
    if rec:
      t = self.ctx.rectys.get(rec, {}).get(e.fld)
      return [t] if t else []
    return [ftys[e.fld] for ftys in self.ctx.rectys.values()
            if e.fld in ftys]

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
    # an application of a constant whose result is an integer
    # holds one (linear_scanProof's 0 <= size_of_live_tree lt,
    # whose size is an integer: tools/intres.txt), and so does an
    # element of a list, a map or an option of integers
    # (linear_scanProof's the 0 (lookup r beg_in), whose beg_in is
    # a map of integers)
    if e.kind == 'app':
      h, args = strip_app(e)
      if h.kind == 'id' and self.ctx.name(h.name) in INT_RESULT_FNS:
        return True
      if (h.kind == 'id' and args
          and self.ctx.name(h.name) in ELEM_FUNS):
        return any(self.intvar(a) for a in args)
    # a field whose type is an integer, or a list or a map of
    # them, holds one (linear_scanProof's 0 < EL i sth.int_beg,
    # whose int_beg is a list of integers)
    if e.kind == 'field':
      tys = self.fldtys(e)
      return bool(tys) and all(INT_TY.search(t) for t in tys)
    # a term that the source annotates with int holds one, and so
    # does the Num of one (data_to_word's 0 <= (i:int))
    if e.kind == 'typed':
      if any(t.text == 'int' for t in e.ty): return True
      return self.intvar(e.e)
    return False

  def notint(self, e):
    """does this expression hold something that is not an integer?
       It does where it is an application of a constant of the port
       whose result is of another type: a numeral beside such an
       application is a numeral of that type, whatever the type of
       the term that the numeral stands in (mlint's
       fromString_unsafe is an integer, and the strlen str = 0 and
       the strsub str 0 of its body are of natural numbers)"""
    while e.kind in ('paren', 'typed', 'rawtyped'): e = e.e
    if e.kind != 'app': return False
    h, args = strip_app(e)
    if h.kind != 'id' or not args: return False
    n = self.ctx.name(h.name)
    # an element of a container has the type of its elements,
    # which the name of the container's function does not say
    # (linear_scanProof's 0 < EL i l, whose l is a list of
    # integers)
    if n in ELEM_FUNS: return False
    return (n in PORT_CONSTANTS and n not in INT_RESULT_FNS
            and not self.intvar(e))

  def is_body(self, e):
    """is this expression the body of a definition rather than
       something that a comparison compares?"""
    while e.kind in ('paren', 'typed', 'rawtyped'): e = e.e
    return e.kind in ('cond', 'case', 'do', 'let', 'quant', 'resq',
                      'reclit', 'recupd', 'setabs')

  def pr0(self, e, prec):
    k = e.kind
    if k == 'id':
      n = e.name
      if n == '_': return self.ctx.fresh()
      if n in self.ctx.vars: return self.ctx.vars[n]
      if n in self.ctx.overloads:
        c = self.ctx.overloads[n]
        # a variable with its type on it is parenthesised already
        # (source_evalProof antiquotes (ci:'cfg compiler_instance))
        if re.match(r"^\([A-Za-z_][A-Za-z0-9_']*:[^()]*\)$", c):
          return c
        return c if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", c) \
               else '(' + c + ')'
      n2 = self.ctx.name(n)
      # a constant that the library layer declares as an infix of
      # HOL Light needs its parentheses where it stands on its own
      # (misc's FOLDR BAG_UNION b0 ls)
      if n2 in HL_INFIX: return '(' + n2 + ')'
      # and so does a binder of HOL Light: HOL4's $LEAST P is
      # (minimal) P, because minimal x. P x is the applied form
      if n2 in BINDERS: return '(' + n2 + ')'
      # HOL4's auxiliary size functions of a datatype family
      # (exp1_size, exp2_size, ...) number the types of the family
      # in another order than HOL Light does, so the port cannot
      # say which type a name of one means; a term that uses one
      # is a pointer at the source and not a statement with a free
      # variable where HOL4 has a constant
      if (AUXSIZE.match(n2) and n2 not in self.ctx.defnames
          and n2 not in self.ctx.names.values()):
        raise SyntaxError('the auxiliary size function ' + n2)
      return n2
    if k == 'num':
      t = e.text
      if t.endswith('w'):
        return '(n2w ' + t[:-1] + ')'
      # HOL4's 0i is an integer and its 0r a real, and & is the
      # injection of both in HOL Light: a literal that says which
      # one it is keeps that, or the overload of & would make it a
      # real wherever nothing else says (exists_num of
      # data_to_word_memoryProof, whose statement is false of the
      # reals)
      if t.endswith('i'):
        return '(&' + t[:-1] + ':int)'
      if t.endswith('r'):
        return '(&' + t[:-1] + ':real)'
      if t.endswith('n') or t.endswith('c'):
        return t[:-1]
      if t.startswith('0x'):
        t = str(int(t, 16))
      if self.ctx.intnums:
        return '(&' + t + ')'
      return t
    if k == 'str':
      return hl_string(e.text[1:-1])
    if k == 'chr':
      return '(CHR ' + str(ord(sml_char(e.text[2:-1]))) + ')'
    if k == 'mlstr':
      # the mlstring literal of HOL4: its constructor is implode,
      # and strlit is an overload of it
      return ('(' + self.cname('strlit') + ' ' +
              hl_string(e.text) + ')')
    if k == 'paren':
      return '(' + self.pr(e.e, 0) + ')'
    if k == 'rawtyped':
      # a variable whose type the port says itself, in HOL Light's
      # own notation: the name is one that the port overloads with
      # a record accessor, and the statement means a variable
      # (tools/fieldvars.py)
      return '(' + self.pr(e.e, 0) + ':' + e.tytext + ')'
    if k == 'typed':
      ty = self.pr_type(e.ty)
      # HOL4 unifies the type variables that a statement writes
      # and HOL Light does not (a type variable of a term is rigid
      # there), so a statement about two states of types ('a,'b)
      # and ('c,'d) whose fields have to agree does not typecheck.
      # Where the port is told to, it drops such an annotation and
      # lets HOL Light infer the type, which is the type that HOL4
      # gives the theorem (overrides.THM_NO_TYVARS).
      if UNIFY_TYVAR_ANNOT[0] and "'" in ty:
        ty = unify_annot(ty)
      elif DROP_TYVAR_ANNOT[0] and "'" in ty:
        return self.pr(e.e, prec)
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
        if n in ARGPERM:
          # a permutation of a prefix of the arguments holds for
          # a partial application of that many as well (FUNPOW f
          # n is ITER n f), so the rules of a name are tried from
          # the longest
          for ar, perm, newname in ARGPERM[n]:
            if len(args) < ar: continue
            s = ' '.join([newname] +
                         [self.pr(args[i], APP) for i in perm] +
                         [self.pr(a, APP) for a in args[ar:]])
            self.numctx = old
            return self.paren(s, PRE_APP, prec)
      # HOL4's ZIP takes the two lists as a pair
      # a name of HOL Light's that is a binder: HOL4 writes it
      # applied, as $LEAST (\x. P x) or LEAST x. P x, and HOL
      # Light writes minimal x. P x -- or (minimal) P where there
      # is no abstraction to put under it
      if hop.kind in ('id', 'dollar') and \
         self.ctx.name(hop.name) in BINDERS:
        nb = self.ctx.name(hop.name)
        a0 = args[0] if args else None
        while a0 is not None and a0.kind == 'paren': a0 = a0.e
        self.numctx = old
        if len(args) == 1 and a0 is not None and a0.kind == 'quant' \
           and a0.q == '\\':
          vs = ' '.join(self.pr(v, APP) for v in a0.vs)
          return self.paren(nb + ' ' + vs + '. ' +
                            self.pr(a0.body, 0), 1, prec)
        return self.paren(
          '(' + nb + ') ' + ' '.join(self.pr(a, APP) for a in args),
          PRE_APP, prec)
      if hop.kind == 'id' and len(args) == 1 and \
         self.ctx.name(hop.name) in UNCURRIED:
        a = args[0]
        while a.kind == 'paren': a = a.e
        if a.kind == 'infix' and a.op == ',':
          self.numctx = old
          return self.paren(self.ctx.name(hop.name) + ' ' +
                            self.pr(a.l, APP) + ' ' +
                            self.pr(a.r, APP), PRE_APP, prec)
        # where the pair is not written out (the argument is a
        # term that gives one), the two arguments come from it
        # with the UNCURRY of HOL Light
        self.numctx = old
        return self.paren('UNCURRY ' + self.ctx.name(hop.name) +
                          ' ' + self.pr(a, APP), PRE_APP, prec)
      fn = self.pr(e.fn, PRE_APP)
      # a constant that the library layer declares as an infix of
      # HOL Light needs its parentheses where it is applied
      # (term's varb gives back BAG_UNION (varb t1) (varb t2))
      if hop.kind == 'id' and fn in HL_INFIX: fn = '(' + fn + ')'
      # a numeral in an argument of a constructor whose type is an
      # integer or a real is written &n
      oldint = self.ctx.intnums
      if hop.kind == 'id' and \
         self.ctx.con_argty.get((hop.name.split('$')[-1],
                                 len(args) - 1)) in ('int', 'real'):
        self.ctx.intnums = True
      # and in an argument of a constant whose type says that the
      # argument is an integer (small_int (:'a) (&0))
      if hop.kind == 'id' and (len(args) - 1) in \
         int_arg_pos(self.ctx.name(hop.name)):
        self.ctx.intnums = True
      arg = self.pr(e.arg, APP)
      self.ctx.intnums = oldint
      self.numctx = old
      return self.paren(fn + ' ' + arg, PRE_APP, prec)
    if k == 'infix':
      op = e.op
      if op == '<>':
        # a numeral next to a variable that holds an integer is &n
        # here as well
        oldint = self.ctx.intnums
        if self.intvar(e.l) or self.intvar(e.r):
          self.ctx.intnums = True
        try:
          return self.paren('~(' + sameline(self.pr(e.l, 12)) +
                            ' = ' + self.pr(e.r, 13) + ')',
                            PRE_APP, prec)
        finally:
          self.ctx.intnums = oldint
      if op == 'NOTIN':
        return self.paren('~(' + sameline(self.pr(e.l, 11)) +
                          ' IN ' + self.pr(e.r, 12) + ')',
                          PRE_APP, prec)
      if op == '$':
        return self.paren(self.pr(e.l, PRE_APP) + ' ' +
                          self.pr(e.r, APP), PRE_APP, prec)
      # these are applications of the constant of the infix,
      # unless the source overloads the infix itself (then the
      # value of the overload is what it is applied to)
      if op in ("'", "''", '--') and INFIX[op][3] is not None:
        return self.paren(INFIX[op][2] + ' ' + self.pr(e.l, APP) + ' ' +
                          self.pr(e.r, APP), PRE_APP, prec)
      if op == '%%':
        return self.paren('word_bit ' + self.pr(e.r, APP) + ' ' +
                          self.pr(e.l, APP), PRE_APP, prec)
      # HOL4's <=> is its = with another precedence, so a source
      # may write it where the sides are not of type bool
      if op == '<=>' and self.ctx is not None and self.ctx.iffeq:
        return self.paren(self.pr(e.l, 13) + ' = ' + self.pr(e.r, 13),
                          12, prec)
      # where the source overloads ++ with the choice of a monad
      # and uses it for an append of two lists that nothing else
      # says the type of, the port writes the append out
      if op == '++' and self.ctx is not None and self.ctx.append:
        l = self.pr(e.l, APP)
        if self.ctx.append is True or l in self.ctx.append:
          return self.paren('APPEND ' + l + ' ' +
                            self.pr(e.r, APP), PRE_APP, prec)
      _, assoc, hop, hprec = INFIX[op]
      # an infix that HOL Light does not have is written as an
      # application of the constant that HOL4 overloads it with
      if hprec is None:
        fn = self.ctx.overloads.get(hop) if self.ctx is not None \
             else None
        if fn:
          fn = as_function(fn)
        else:
          fn = as_function(self.ctx.name(hop))
        return self.paren(fn + ' ' + sameline(self.pr(e.l, APP)) +
                          ' ' + self.pr(e.r, APP), PRE_APP, prec)
      old = self.numctx
      self.numctx = op in NUMCTX
      # the exponent of pow, EXP and ** is a natural number, also in
      # a definition whose other numerals are integers or reals
      oldint = self.ctx.intnums
      # a numeral next to a variable that holds an integer is &n
      if ((op in NUMCTX or op in ('=', '<>')) and
          (self.intvar(e.l) or self.intvar(e.r))):
        self.ctx.intnums = True
      # and a numeral next to an application whose result is of
      # another type is a numeral of that type, which an integer
      # around the two of them does not change (mlint's
      # fromString_unsafe is an integer and compares the strlen of
      # its argument with 0, a natural number).  The equation that
      # a definition is does not count: its left hand side is the
      # constant itself, and what tells the two apart is that the
      # body of a definition is a term that a comparison is not
      elif ((op in NUMCTX or op in ('=', '<>')) and self.ctx.intnums
            and (self.notint(e.l) or self.notint(e.r))
            and not self.is_body(e.l) and not self.is_body(e.r)):
        self.ctx.intnums = False
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
        if (self.ctx.wordnot or wordlit(e.e) or
            (e.e.kind == 'id' and
             e.e.name in self.ctx.wordnotvars)):
          return self.paren('word_not ' + self.pr(e.e, APP),
                            PRE_APP, prec)
        # a prefix of HOL Light takes the atom after it and no
        # more, so an application under one needs its parentheses
        op = '--' if numeric(e.e) or self.numctx else '~'
        return self.paren(
          op + sym_space(op, sameline(self.pr(e.e, APP))),
          PRE_APP, prec)
      if e.op == '-':
        return self.paren(
          '--' + sym_space('--', sameline(self.pr(e.e, APP))),
          PRE_APP, prec)
      if e.op == '&':
        # the argument of HOL4's & is a natural number, also in a
        # definition whose other numerals are integers or reals
        # (clos_to_bvlProof's cl_rel has Number (&(num_args - 1)))
        oldint = self.ctx.intnums
        self.ctx.intnums = False
        s = '&' + sameline(self.pr(e.e, APP))
        self.ctx.intnums = oldint
        return self.paren(s, PRE_APP, prec)
    if k == 'some':
      vs = ' '.join(self.pr(v, APP) for v in e.vs)
      n = self.ctx.name(e.name)
      # where this port's name for the binder is a binder of HOL
      # Light as well (HOL4's $LEAST is minimal), it is written
      # as one: minimal x. P x and not minimal (\x. P x)
      if n in BINDERS:
        return self.paren(n + ' ' + vs + '. ' + self.pr(e.body, 0),
                          1, prec)
      return self.paren(n + ' (\\' + vs + '. ' +
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
      def bind(p, v):
        # HOL4 binds a function with its arguments on the left of
        # the =, where HOL Light takes the left hand side for a
        # pattern and leaves the arguments free: the port makes
        # the arguments an abstraction (bvl_const's SmartOp2 has
        # let mk_add_const x1 c2 = ... in)
        if p.kind == 'app':
          hop, args = strip_app(p)
          if hop.kind == 'id':
            return (self.pr(hop, 0) + ' = (\\' +
                    ' '.join(self.pr(a, APP) for a in args) +
                    '. ' + self.pr(v, 0) + ')')
        return self.pr(p, 0) + ' = ' + self.pr(v, 13)
      bs = ' and '.join(bind(p, v) for p, v in e.binds)
      return self.paren('let ' + bs + ' in ' + self.pr(e.body, 0),
                        1, prec)
    if k == 'case':
      # a tuple of values or a tuple pattern needs its parentheses,
      # and so does a match, a let or a conditional in an arm
      def arm(p, b):
        # the pattern of an arm binds its own variables, and some
        # of them hold an integer where the ones of another arm do
        # not (closSem's do_app matches on [Number i] in one arm
        # and on (MemOp (ElemAt i)) in another)
        vs = self.ctx.armvars.get(id(b))
        if not vs: return self.pr(p, 15) + ' -> ' + self.pr(b, 2)
        old = self.ctx.intvars
        self.ctx.intvars = old | vs
        try:
          return self.pr(p, 15) + ' -> ' + self.pr(b, 2)
        finally:
          self.ctx.intvars = old
      arms = ' | '.join(arm(p, b) for p, b in e.arms)
      return self.paren('match ' + self.pr(e.s, 15) + ' with ' + arms,
                        1, prec)
    if k == 'field':
      # the record type of a variable that the overrides name
      # (typeSoundInvariants has the c of a sem_env and the c of
      # a type_env in one rule)
      # an annotation of the record says which one it is, and says
      # it of this occurrence (stack_to_labProof reads the code of
      # (s1:('a,'c,'ffi)stackSem$state), and its s is a state of
      # labSem in two statements and one of stackSem in the rest)
      rec = self.annot_rec(e.e)
      # the field has to be one of that record: an annotation of a
      # record says the type of the term and not of the field, and
      # a term can be annotated where the field is of another
      # record of the statement
      if rec and e.fld not in self.ctx.recs.get(rec, []): rec = None
      if not rec:
        v = e.e
        while v.kind in ('paren', 'typed', 'rawtyped'): v = v.e
        rec = (self.ctx.fieldvar.get(v.name)
               if v.kind == 'id' else None)
        # the record of a variable holds for the fields that it
        # has: the s of data_to_word_memoryProof is a state of
        # dataSem in most of its statements and a gc_state in the
        # ones about the garbage collector, whose h2 and r4 only
        # the gc_state has
        if rec and e.fld not in self.ctx.recs.get(rec, []):
          rec = None
      acc = (rec + '_' + e.fld) if rec else self.ctx.field(e.fld)
      return self.paren(acc + ' ' + self.pr(e.e, APP),
                        PRE_APP, prec)
    if k == 'recupd':
      s = self.pr(e.e, APP)
      # the record type of a variable that the overrides name
      w = e.e
      while w.kind == 'paren': w = w.e
      while w.kind == 'typed': w = w.e
      rec = (self.ctx.fieldvar.get(w.name)
             if w.kind == 'id' else None)
      for i, (fld, v, fn) in enumerate(e.upds):
        s = ((rec + '_' + fld + '_fupd' if rec
              else self.ctx.fupd(fld)) + ' ' +
             (self.updfn(v, rec, fld) if fn
              else '(K ' + self.pr(v, APP) + ')')
             + ' ' + s)
        if i < len(e.upds) - 1: s = '(' + s + ')'
      return self.paren(s, PRE_APP, prec)
    if k == 'reclit':
      flds = [f for f, _, _ in e.upds]
      # a statement whose literals are of several record types that
      # have the same fields says which in order: the two literals
      # of source_to_flatProof's global_env_inv_extend are an
      # environment of source_to_flat and a sem_env, and nothing
      # but the argument of global_env_inv that each is tells which
      # (overrides.THM_RECLITS)
      if self.ctx.reclits:
        rty = self.ctx.reclits.pop(0)
        order = self.ctx.recs.get(rty, flds)
        vals = []
        for f in order:
          v = [v for g, v, _ in e.upds if g == f]
          vals.append(self.pr(v[0], APP) if v else 'ARB')
        return self.paren('mk_' + rty + ' ' + ' '.join(vals),
                          PRE_APP, prec)
      # the record type of a literal is the one whose fields are
      # exactly the ones of the literal; a field name on its own may
      # be one of several record types
      exact = [ty for ty, fs in self.ctx.recs.items()
               if set(fs) == set(flds)]
      part = [ty for ty, fs in self.ctx.recs.items()
              if set(flds) <= set(fs)]
      cand = exact or part
      # a literal whose fields are exactly the ones of a single
      # record type is of that type; the record of the overrides
      # is for the ones that several types have (source_to_flat's
      # env_all_rel makes a sem_env of a c and a v, and an
      # environment of flatSem of a v of its own)
      # where more than one record type has exactly these fields,
      # the record that the field names are of by default decides:
      # the <|v := ...; c := ...|> of a source is a sem_env, also
      # in a theory whose .v is the v of another record
      # (source_to_flatProof's genv.v is a global_env's)
      dflt = [ty for ty in exact
              if any(ty == self.ctx.recdflt.get(f) for f in flds)]
      fld = self.ctx.fields.get(flds[0])
      rty = (exact[0] if len(exact) == 1
             else self.ctx.reclit if self.ctx.reclit in part
             else fld if fld in exact
             else dflt[0] if dflt
             else cand[0] if len(cand) == 1
             else fld or '?')
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
      # HOL4's <> is a notation for the negated equality, which
      # the port writes out; as a function of its own it is the
      # lambda that says the same (EVERY ((<>) x o FST) l)
      if n == '<>': return '(\\x y. ~(x = y))'
      if n in INFIX: return as_function(INFIX[n][2])
      # an operator that is not an identifier needs its parentheses
      if not n[0].isalpha() and n[0] != '_':
        return '(' + self.ctx.name(n) + ')'
      # and so does a binder of HOL Light
      return as_function(self.ctx.name(n))
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
    if e.kind in ('paren', 'typed', 'rawtyped'): e = e.e
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
    while l.kind in ('paren', 'typed', 'rawtyped'): l = l.e
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
