"""translate the ML expression that HOL4 binds a theorem to

A HOL4 source may state a theorem as the value of an ML expression
(`Theorem foo = bar |> SRULE [baz]`).  The statement is then what
that expression computes, and the port cannot state the theorem
without computing it too.  Where the expression is built of the
derived rules that HOL Light has as well, this writes the HOL
Light expression that computes the same theorem, and the port has
the theorem with a proof instead of a pointer at the source.

Nothing here is a translation of a tactic.  These are the derived
rules of the logic, which the two systems share under the same
names, and what the port does with them is run them.  An
expression that needs the ML of HOL4 (a `map`, a `TypeBase`, a
`Q.prove`) is refused, and so is one that names a theorem the port
does not have; the caller then falls back on the pointer.

A rule that rewrites (`SRULE`, `SIMP_RULE`) does not compute the
same theorem in the two systems, because the simpsets differ.  The
port runs what it writes: `tools/derive.nofill` says of every
expression that did not go through why it was taken out again.
"""
import re

TOK = re.compile(r"""
    (?P<q3>“[^”]*”|‘[^’]*’)
  | (?P<q2>``[^`]*``)
  | (?P<q1>`[^`]*`)
  | (?P<arrow>\|->)
  | (?P<pipe>\|>)
  | (?P<id>[A-Za-z_][A-Za-z_0-9'.]*)
  | (?P<num>[0-9]+)
  | (?P<punc>[\[\](),;:@$#])
  | (?P<ws>\s+)
""", re.X)

OPEN, CLOSE = '([', ')]'

# the rules that take the theorem and nothing else, under the name
# that HOL Light gives them as well
SIMPLE = {
  'SPEC_ALL', 'GEN_ALL', 'GSYM', 'UNDISCH', 'UNDISCH_ALL',
  'DISCH_ALL', 'CONJUNCT1', 'CONJUNCT2', 'EQT_ELIM', 'SYM',
  'BETA_RULE', 'NOT_EQ_SYM', 'EQT_INTRO', 'EQF_ELIM',
}

# the rules that take a term and the theorem; HOL4 writes the term
# as a quotation of its own (Q.SPEC) or as one of the ambient
# grammar (SPEC), which the port writes the same way either way
TERM_RULE = {
  'Q.SPEC': 'SPEC', 'SPEC': 'SPEC', 'Q.GEN': 'GEN', 'GEN': 'GEN',
  'Q.ISPEC': 'ISPEC', 'ISPEC': 'ISPEC', 'DISCH': 'DISCH',
  'Q.AP_THM': 'AP_THM', 'AP_THM': 'AP_THM',
}

# the same with a list of terms
TERMS_RULE = {
  'Q.SPECL': 'SPECL', 'SPECL': 'SPECL', 'Q.GENL': 'GENL',
  'GENL': 'GENL', 'Q.ISPECL': 'ISPECL', 'ISPECL': 'ISPECL',
}

# the rules that take another theorem and this one
THM_RULE = {
  'MATCH_MP': 'MATCH_MP', 'MP': 'MP', 'PROVE_HYP': 'PROVE_HYP',
  'CONJ': 'CONJ', 'EQ_MP': 'EQ_MP',
}

# the rules that take a list of theorems and this one
THMS_RULE = {
  'REWRITE_RULE': 'REWRITE_RULE',
  'ONCE_REWRITE_RULE': 'ONCE_REWRITE_RULE',
  'PURE_REWRITE_RULE': 'PURE_REWRITE_RULE',
  'PURE_ONCE_REWRITE_RULE': 'PURE_ONCE_REWRITE_RULE',
  'SRULE': 'SIMP_RULE',
}

# the same, where HOL4 puts the simpset in front of the list
SS_RULE = {
  'SIMP_RULE': 'SIMP_RULE',
  'ASM_SIMP_RULE': 'SIMP_RULE',
  'FULL_SIMP_RULE': 'SIMP_RULE',
}


ATOM = re.compile(r"^[A-Za-z_][A-Za-z_0-9']*$")


def par(e):
  """an expression where it has to stand as an argument: a name
     needs no brackets round it and nothing else goes without"""
  return e if ATOM.match(e) else '(%s)' % e


class No(Exception):
  """the expression is not one the port can write"""


def tokens(text):
  out, i = [], 0
  while i < len(text):
    m = TOK.match(text, i)
    if not m: raise No('%r' % text[i:i+12])
    i = m.end()
    k = m.lastgroup
    if k != 'ws': out.append((k, m.group()))
  return out


def split(toks, kind, what=None):
  """split a token list at the top level"""
  parts, d = [[]], 0
  for t in toks:
    if t[0] == 'punc' and t[1] in OPEN: d += 1
    elif t[0] == 'punc' and t[1] in CLOSE: d -= 1
    if d == 0 and t[0] == kind and (what is None or t[1] == what):
      parts.append([])
    else:
      parts[-1].append(t)
  return parts


def unbracket(toks, o='(', c=')'):
  """the inside of a bracketed token list, or None"""
  if len(toks) < 2 or toks[0][1] != o or toks[-1][1] != c:
    return None
  d = 0
  for i, t in enumerate(toks):
    if t[0] == 'punc' and t[1] in OPEN: d += 1
    elif t[0] == 'punc' and t[1] in CLOSE:
      d -= 1
      if d == 0 and i != len(toks) - 1: return None
  return toks[1:-1]


def app(toks):
  """an application, as the head and the argument token lists"""
  args, d, cur = [], 0, []
  for t in toks:
    if t[0] == 'punc' and t[1] in OPEN:
      if d == 0 and cur: args.append(cur); cur = []
      d += 1
      cur.append(t)
    elif t[0] == 'punc' and t[1] in CLOSE:
      d -= 1
      cur.append(t)
      if d == 0: args.append(cur); cur = []
    elif d:
      cur.append(t)
    else:
      if cur: args.append(cur)
      cur = [t]
  if cur: args.append(cur)
  return args


QUOT = ('q1', 'q2', 'q3')


class Derive:
  def __init__(self, resolve, term, evalconv=None, evaldefs=None):
    self.resolve = resolve        # a HOL4 name -> the port's
    self.term = term              # a HOL4 term -> the port's
    # a HOL4 term -> the HOL Light conversion that computes its
    # value, which is what HOL4's EVAL does with its compset
    self.evalconv = evalconv or (lambda t: None)
    # the name of a definition -> the definitions that its
    # right-hand side reaches, for a rule that evaluates it
    self.evaldefs = evaldefs or (lambda n: None)
    self.base_name = None

  # -------------------------------------------------------------

  def name(self, toks):
    if len(toks) != 1 or toks[0][0] != 'id': raise No('not a name')
    nm = self.resolve(toks[0][1])
    if not nm: raise No('no %s' % toks[0][1])
    return nm

  def quotation(self, toks):
    """the term of a quotation, as the port writes it"""
    if len(toks) != 1 or toks[0][0] not in ('q1', 'q2', 'q3'):
      raise No('not a quotation')
    s = toks[0][1]
    s = s[2:-2] if s.startswith('``') else s[1:-1]
    try:
      return '`%s`' % self.term(s.strip())
    except No:
      raise
    except Exception as e:
      raise No('term %s' % e)

  def thmlist(self, toks):
    """a list of theorems to rewrite with, where a simpset
       fragment of HOL4 (SF ETA_ss) is not one: HOL Light's
       simplifier does what those of these lists ask for"""
    inner = unbracket(toks, '[', ']')
    if inner is None: raise No('not a list')
    if not inner: return '[]'
    out = []
    for p in split(inner, 'punc', ','):
      if p and p[0] == ('id', 'SF'): continue
      out.append(self.thm(p))
    return '[%s]' % '; '.join(out)

  def listof(self, toks, f):
    """a bracketed list, by what its elements are"""
    inner = unbracket(toks, '[', ']')
    if inner is None: raise No('not a list')
    if not inner: return '[]'
    return '[%s]' % '; '.join(f(p) for p in split(inner, 'punc', ','))

  # -------------------------------------------------------------

  def quoted(self, toks):
    inner = unbracket(toks)
    if inner is not None: toks = inner
    return len(toks) == 1 and toks[0][0] in QUOT



  def evaluated(self, toks):
    """the value of a term, which HOL4 computes with the compset
       of its whole development and the port with the definitions
       that the term reaches"""
    inner = unbracket(toks)
    if inner is not None: toks = inner
    s = toks[0][1]
    s = s[2:-2] if s.startswith('``') else s[1:-1]
    e = self.evalconv(s.strip())
    if not e: raise No('EVAL')
    return e

  def thm(self, toks):
    """a token list that computes a theorem"""
    parts = split(toks, 'pipe')
    if not parts[0]: raise No('empty')
    # HOL4's EVAL takes a term and not a theorem, so a pipeline
    # that starts with one is where the theorem comes from
    if (len(parts) > 1 and self.quoted(parts[0]) and
        parts[1] == [('id', 'EVAL')]):
      out, parts = self.evaluated(parts[0]), parts[1:]
    else:
      a = app(parts[0])
      if (len(a) == 2 and a[0] and len(a[0]) == 1 and
          a[0][0] == ('id', 'EVAL') and self.quoted(a[1])):
        out = self.evaluated(a[1])
      else:
        if len(parts[0]) == 1 and parts[0][0][0] == 'id':
          self.base_name = parts[0][0][1]
        out = self.base(parts[0])
    for p in parts[1:]:
      out = self.step(p, out)
    return out

  def base(self, toks):
    if not toks: raise No('empty')
    inner = unbracket(toks)
    if inner is not None: return self.thm(inner)
    a = app(toks)
    if not a: raise No('empty')
    if len(a) == 1: return self.name(a[0])
    head = a[0][0][1] if len(a[0]) == 1 and a[0][0][0] == 'id' else None
    if head == 'LIST_CONJ' and len(a) == 2:
      return 'end_itlist CONJ %s' % self.listof(a[1], self.thm)
    return self.applied(a)

  def applied(self, a):
    """a rule applied to its arguments, the last of which is the
       theorem (HOL4 writes GEN_ALL foo as well as foo |> GEN_ALL)"""
    if len(a) < 2: raise No('not an application')
    return self.step(sum(a[:-1], []), self.thm(a[-1]))

  def step(self, toks, acc):
    """a step of a pipeline, applied to what came before it"""
    inner = unbracket(toks)
    if inner is not None: toks = inner
    a = app(toks)
    if not a: raise No('empty step')
    if len(a[0]) != 1 or a[0][0][0] != 'id': raise No('odd step')
    f, args = a[0][0][1], a[1:]
    if acc is None:
      if not args: raise No('no theorem')
      acc, args = self.thm(args[-1]), args[:-1]
    if f in SIMPLE and not args:
      return '%s %s' % (f, par(acc))
    if f in TERM_RULE and len(args) == 1:
      return '%s %s %s' % (TERM_RULE[f], self.quotation(args[0]),
                           par(acc))
    if f in TERMS_RULE and len(args) == 1:
      return '%s %s %s' % (TERMS_RULE[f],
                           self.listof(args[0], self.quotation),
                           par(acc))
    if f in THM_RULE and len(args) == 1:
      return '%s %s %s' % (THM_RULE[f], par(self.thm(args[0])),
                           par(acc))
    if f in THMS_RULE and len(args) == 1:
      return '%s %s %s' % (THMS_RULE[f], self.thmlist(args[0]),
                           par(acc))
    if f in SS_RULE and len(args) == 2:
      # the simpset of HOL4 is not a thing the port has: the
      # rewrites that the source names are what it simplifies with
      return '%s %s %s' % (SS_RULE[f], self.thmlist(args[1]),
                           par(acc))
    # HOL4 evaluates the right-hand side of a definition by the
    # name of the definition, and what it evaluates with is the
    # compset of its whole development
    if (f == 'CONV_RULE' and len(args) == 1 and self.base_name and
        [t[1] for t in unbracket(args[0]) or []] ==
        ['RAND_CONV', 'EVAL']):
      d = self.evaldefs(self.base_name)
      if not d: raise No('EVAL of %s' % self.base_name)
      return 'CONV_RULE (RAND_CONV (CAKE_EVAL %s)) %s' % (d, par(acc))
    if f == 'Q.INST' and len(args) == 1:
      return 'INST %s %s' % (self.inst(args[0]), par(acc))
    if f == 'cj' and len(args) == 1 and args[0][0][0] == 'num':
      return 'el %d (CONJUNCTS %s)' % (int(args[0][0][1]) - 1,
                                       par(acc))
    raise No('rule %s/%d' % (f, len(args)))

  def inst(self, toks):
    """the substitution of a Q.INST, which HOL4 writes the other
       way round (`x` |-> `y` is y for x)"""
    inner = unbracket(toks, '[', ']')
    if inner is None: raise No('not a substitution')
    out = []
    for p in split(inner, 'punc', ','):
      ab = split(p, 'arrow')
      if len(ab) != 2: raise No('not a |->')
      out.append('%s,%s' % (self.quotation(ab[1]),
                            self.quotation(ab[0])))
    return '[%s]' % '; '.join(out)


HEAD = re.compile(r'^\s*(?:Theorem|val|Definition)\b[^=]*=', re.S)


def body(text):
  """the ML expression that a ThmValue block binds"""
  t = HEAD.sub('', text, count=1)
  return t.strip().rstrip(';').strip()


def translate(text, resolve, term, evalconv=None, evaldefs=None):
  """the HOL Light expression that computes the same theorem, or
     None with the reason why not"""
  try:
    toks = tokens(body(text))
  except No as e:
    return None, str(e)
  if not toks: return None, 'empty'
  try:
    return Derive(resolve, term, evalconv,
                  evaldefs).thm(toks), None
  except No as e:
    return None, str(e)
  except RecursionError:
    return None, 'too deep'
  except (IndexError, AttributeError, TypeError) as e:
    # a shape this does not read is no reason to lose the
    # pointer at the source, but it is one to say so
    return None, 'BUG %s: %s' % (type(e).__name__, e)
