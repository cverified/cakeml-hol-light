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
  'Q.SPEC': 'CAKE_SPEC', 'SPEC': 'CAKE_SPEC',
  'Q.GEN': 'CAKE_GEN', 'GEN': 'CAKE_GEN',
  'Q.ISPEC': 'ISPEC', 'ISPEC': 'ISPEC', 'DISCH': 'DISCH',
  'Q.AP_THM': 'AP_THM', 'AP_THM': 'AP_THM',
}

# the same with a list of terms
TERMS_RULE = {
  'Q.SPECL': 'CAKE_SPECL', 'SPECL': 'CAKE_SPECL',
  'Q.GENL': 'CAKE_GENL', 'GENL': 'CAKE_GENL',
  'Q.ISPECL': 'ISPECL', 'ISPECL': 'ISPECL',
}

# the rules that take another theorem and this one
THM_RULE = {
  'MATCH_MP': 'MATCH_MP', 'MP': 'MP', 'PROVE_HYP': 'PROVE_HYP',
  'CONJ': 'CONJ', 'EQ_MP': 'EQ_MP',
}

# the conversions that HOL4 applies to a term, and the number of
# arguments they take before it; the last of those is the list of
# theorems and a simpset in front of it is not one the port has
CONV = {
  'REWRITE_CONV': ('REWRITE_CONV', 1),
  'ONCE_REWRITE_CONV': ('ONCE_REWRITE_CONV', 1),
  'PURE_REWRITE_CONV': ('PURE_REWRITE_CONV', 1),
  'PURE_ONCE_REWRITE_CONV': ('PURE_ONCE_REWRITE_CONV', 1),
  'SIMP_CONV': ('SIMP_CONV', 2),
  'SCONV': ('SIMP_CONV', 1),
}

# the conversions that take a conversion and give one, which the
# two systems have under one name but for HOL4's RHS_CONV
CONV_WRAP = {
  'RAND_CONV': 'RAND_CONV', 'RATOR_CONV': 'RATOR_CONV',
  'LAND_CONV': 'LAND_CONV', 'ABS_CONV': 'ABS_CONV',
  'BINDER_CONV': 'BINDER_CONV', 'DEPTH_CONV': 'DEPTH_CONV',
  'TOP_DEPTH_CONV': 'TOP_DEPTH_CONV', 'RHS_CONV': 'RAND_CONV',
  'ONCE_DEPTH_CONV': 'ONCE_DEPTH_CONV',
  'REDEPTH_CONV': 'REDEPTH_CONV',
}

# the rules that take a list of theorems and this one
THMS_RULE = {
  'REWRITE_RULE': 'REWRITE_RULE',
  'ONCE_REWRITE_RULE': 'ONCE_REWRITE_RULE',
  'PURE_REWRITE_RULE': 'PURE_REWRITE_RULE',
  'PURE_ONCE_REWRITE_RULE': 'PURE_ONCE_REWRITE_RULE',
  'SRULE': 'SIMP_RULE',
}

# the functions on a theorem or on a list of them that the two
# systems share: HOL Light is OCaml and has the list functions
# of it, so a step that takes a theorem apart and puts the parts
# back together is written the way HOL4 writes it
LIST_FN = {
  'CONJUNCTS': 'CONJUNCTS', 'BODY_CONJUNCTS': 'BODY_CONJUNCTS',
  'CONJ_LIST': 'CONJUNCTS', 'LIST_CONJ': 'end_itlist CONJ',
  'hd': 'hd', 'tl': 'tl', 'last': 'last', 'rev': 'rev',
  'List.last': 'last', 'List.rev': 'rev', 'List.hd': 'hd',
  'List.tl': 'tl',
  # the steps that take a term out of a theorem and a term
  # apart, which the two systems also share.  A chain that ends
  # in one of these is a *term* and not a theorem, which is what
  # a source antiquotes into the body of a definition
  # (to_word64Prog's int_to_words is the right hand side of the
  # first clause of data_to_word's part_to_words)
  # the two helpers that every bootstrap source defines for
  # itself: spec32 = INST_TYPE[alpha|->``:32``] (and 64), which
  # instantiates the word width of a theorem of the backend
  'spec32': 'INST_TYPE [`:32`,`:A`]',
  'spec64': 'INST_TYPE [`:64`,`:A`]',
  'concl': 'concl', 'rhs': 'rhs', 'lhs': 'lhs',
  'rand': 'rand', 'rator': 'rator', 'dest_neg': 'dest_neg',
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
     and a list need no brackets round them and nothing else goes
     without"""
  if ATOM.match(e): return e
  if e.startswith('[') and e.endswith(']'): return e
  return '(%s)' % e


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
    inner = unbracket(toks)
    if inner is not None: toks = inner
    if len(toks) != 1 or toks[0][0] not in ('q1', 'q2', 'q3'):
      raise No('not a quotation')
    s = toks[0][1]
    s = s[2:-2] if s.startswith('``') else s[1:-1]
    # HOL4 writes an argument an abstraction does not use as `_`
    # (deBruijn_subst_ind |> Q.SPEC `\u03bb_ _ x. P x`), and HOL
    # Light's parser does not take `_` for a binder.  The two
    # terms are the same: the binder is not in the body
    def names(m):
      out, i = [m.group(1)], 0
      for w in m.group(2).split():
        if w == '_': out.append('uu%d' % i); i += 1
        else: out.append(w)
      return ' '.join(out) + '.'
    s = re.sub(r'(\\|\u03bb)((?:\s*(?:_|[A-Za-z][A-Za-z0-9_\']*))+)\s*\.',
               names, s)
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

  def conv(self, toks):
    """a conversion of HOL4 that HOL Light has as well, without
       the term it is applied to and without the simpset that
       HOL4 writes in front of its list of theorems"""
    a = app(toks)
    if not a or len(a[0]) != 1 or a[0][0][0] != 'id': raise No('conv')
    f, args = a[0][0][1], a[1:]
    if f not in CONV: raise No('conv %s' % f)
    nm, k = CONV[f]
    if len(args) != k: raise No('conv %s/%d' % (f, len(args)))
    return '%s %s' % (nm, self.thmlist(args[-1]))

  def convexpr(self, toks):
    """a conversion that HOL4 builds out of conversions, where
       HOL Light has every one of them"""
    inner = unbracket(toks)
    if inner is not None: toks = inner
    a = app(toks)
    if a and len(a[0]) == 1 and a[0][0][0] == 'id' and \
       a[0][0][1] in CONV_WRAP and len(a) == 2:
      return '%s %s' % (CONV_WRAP[a[0][0][1]],
                        par(self.convexpr(a[1])))
    return self.conv(toks)

  def term_first(self, parts):
    """what a pipeline whose first part is a term computes: HOL4
       applies a conversion or its EVAL to the term and the
       theorem comes from there"""
    if len(parts) < 2: raise No('a term')
    if parts[1] == [('id', 'EVAL')]:
      return self.evaluated(parts[0])
    return '%s %s' % (self.conv(parts[1]), self.quotation(parts[0]))

  def thm(self, toks):
    """a token list that computes a theorem"""
    parts = split(toks, 'pipe')
    if not parts[0]: raise No('empty')
    a = app(parts[0])
    # HOL4's EVAL and its conversions take a term and not a
    # theorem, so one of those is where the theorem comes from
    if self.quoted(parts[0]):
      out, parts = self.term_first(parts), parts[1:]
    elif (len(a) == 2 and a[0] and len(a[0]) == 1 and
          a[0][0] == ('id', 'ASSUME') and self.quoted(a[1])):
      out = 'ASSUME %s' % self.quotation(a[1])
    elif (len(a) == 2 and a[0] and len(a[0]) == 1 and
          a[0][0] == ('id', 'EVAL') and self.quoted(a[1])):
      out = self.evaluated(a[1])
    elif (len(a) > 1 and a[0] and len(a[0]) == 1 and
          a[0][0][0] == 'id' and a[0][0][1] in CONV and
          self.quoted(a[-1])):
      out = '%s %s' % (self.conv(sum(a[:-1], [])),
                       self.quotation(a[-1]))
    else:
      if len(parts[0]) == 1 and parts[0][0][0] == 'id':
        self.base_name = parts[0][0][1]
      out = self.base(parts[0])
    for p in parts[1:]:
      out = self.step(p, out)
    return out

  def thmlistexpr(self, toks):
    """an expression that computes a list of theorems"""
    inner = unbracket(toks)
    if inner is not None: toks = inner
    ps = split(toks, 'punc', '$')
    if len(ps) > 1:
      return self.thmlistexpr(ps[0] + [('punc', '(')] +
                              sum(ps[1:], []) + [('punc', ')')])
    if toks and toks[0][1] == '[': return self.thmlist(toks)
    a = app(toks)
    if not a: raise No('empty list')
    f = a[0][0][1] if len(a[0]) == 1 and a[0][0][0] == 'id' else None
    if f in ('CONJUNCTS', 'BODY_CONJUNCTS', 'CONJ_LIST') and \
       len(a) == 2:
      return '%s %s' % (LIST_FN[f], par(self.thm(a[1])))
    if f in ('rev', 'tl', 'List.rev', 'List.tl') and len(a) == 2:
      return '%s %s' % (LIST_FN[f], par(self.thmlistexpr(a[1])))
    if f in ('map', 'List.map') and len(a) == 3:
      return 'map %s %s' % (par(self.rulefun(a[1])),
                            par(self.thmlistexpr(a[2])))
    raise No('a list of theorems')

  def base(self, toks):
    if not toks: raise No('empty')
    inner = unbracket(toks)
    if inner is not None: return self.thm(inner)
    ps = split(toks, 'punc', '$')
    if len(ps) > 1:
      # HOL4's $ is application that binds least of all
      return self.thm(ps[0] + [('punc', '(')] +
                      sum(ps[1:], []) + [('punc', ')')])
    a = app(toks)
    if not a: raise No('empty')
    if len(a) == 1: return self.name(a[0])
    head = a[0][0][1] if len(a[0]) == 1 and a[0][0][0] == 'id' else None
    if head == 'LIST_CONJ' and len(a) == 2:
      return 'end_itlist CONJ %s' % par(self.thmlistexpr(a[1]))
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
    if f in LIST_FN and not args:
      return '%s %s' % (LIST_FN[f], par(acc))
    # a step that applies a rule to every theorem of a list: HOL
    # Light's map, with the rule as a function of its own
    if f in ('map', 'List.map') and len(args) == 1:
      return 'map %s %s' % (par(self.rulefun(args[0])), par(acc))
    # HOL4 counts the conjuncts of a theorem from one
    if f == 'el' and len(args) == 1 and args[0][0][0] == 'num':
      return 'el %d %s' % (int(args[0][0][1]) - 1, par(acc))
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
    if f == 'CONV_RULE' and len(args) == 1:
      return 'CONV_RULE %s %s' % (par(self.convexpr(args[0])),
                                  par(acc))
    if f == 'Q.INST' and len(args) == 1:
      return 'CAKE_INST %s %s' % (self.inst(args[0]), par(acc))
    if f == 'cj' and len(args) == 1 and args[0][0][0] == 'num':
      return 'el %d (CONJUNCTS %s)' % (int(args[0][0][1]) - 1,
                                       par(acc))
    raise No('rule %s/%d' % (f, len(args)))

  def rulefun(self, toks):
    """a rule as a function of its own, for a step that applies
       it to every theorem of a list: a composition of rules, or
       one with the arguments that come before the theorem"""
    inner = unbracket(toks)
    if inner is not None: toks = inner
    ps = split(toks, 'id', 'o')
    if len(ps) > 1:
      return ' o '.join(self.rulefun(p) for p in ps)
    a = app(toks)
    if not a or len(a[0]) != 1 or a[0][0][0] != 'id':
      raise No('rule function')
    f, args = a[0][0][1], a[1:]
    if f in SIMPLE and not args: return f
    if f in LIST_FN and not args: return LIST_FN[f]
    if f in TERM_RULE and len(args) == 1:
      return '%s %s' % (TERM_RULE[f], self.quotation(args[0]))
    if f in TERMS_RULE and len(args) == 1:
      return '%s %s' % (TERMS_RULE[f],
                        self.listof(args[0], self.quotation))
    if f in THMS_RULE and len(args) == 1:
      return '%s %s' % (THMS_RULE[f], self.thmlist(args[0]))
    if f in SS_RULE and len(args) == 2:
      return '%s %s' % (SS_RULE[f], self.thmlist(args[1]))
    if f == 'Q.INST' and len(args) == 1:
      return 'CAKE_INST %s' % self.inst(args[0])
    raise No('rule function %s/%d' % (f, len(args)))

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
