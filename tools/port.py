"""Translate a CakeML HOL4 script file to a HOL Light file.

  python3 -I tools/port.py <theory>

writes ml/<path>/<theory>.ml and reports what it could not do.
"""
import sys, os, re, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, overrides, grammardef
import fieldvars, strategies, unstated
import proofstore, derive

# every theorem that the port states, as (theory, HOL4 name,
# binding), in the order of the files, and every definition as
# (theory, constant, binding): tools/dryport.py dumps both, so
# that the proof store can name a theorem or a definition by the
# binding it has in the file that makes it
EMITTED = []
EMITTED_DEFS = []
# the binding and the HOL4 body of every definition that is not
# recursive, by the constant it defines: a term that HOL4 gives to
# its EVAL is computed in HOL Light by unfolding the definitions
# that the term reaches, and these are what it reaches
DEF_BODY = {}

# the definitions whose termination the first pass assumes: the
# port writes CHEAT_TAC in the place of the Termination tactic of
# HOL4 for these, so that what is left to do is visible in the
# file and local to it (tools/mkcheats.py makes the list from
# ml/CHEATS.md, which a run writes)
# The name in an entry is the name of the block of the HOL4 source
# (`Definition compile_def:` of bvi_to_data is `bvi_to_data
# compile_def`), which is what the port looks a definition up by.
# An entry may name the binding that the port makes of it instead
# (`bvi_to_data bvi_to_data_compile_def`), because tools/mkcheats.py
# reads ml/CHEATS.md, which has the constants of the port and not
# the names of the source: the theory in front of such a name comes
# off, so that both spellings find the definition.  Twenty entries
# were the second kind and found nothing, which left their
# definitions to the machinery -- the measure of one of them timed
# out for thirty seconds and the definition was assumed in the end
# all the same, with "timeout in measure" for a reason.
def _cheat_set():
  f = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   'cheats.txt')
  out = set()
  try:
    rows = [l.split() for l in open(f) if l.split()]
  except OSError:
    return out
  for r in rows:
    out.add(tuple(r))
    if len(r) == 2 and r[1].startswith(r[0] + '_'):
      out.add((r[0], r[1][len(r[0]) + 1:]))
  return out

CHEATS = _cheat_set()


# the definitions that a run could not make at all, with the reason
# it gave (ml/CHEATS.md, which a run writes).  These say so at the
# call site, with assume_definition, because that is what they are;
# a cheat for the termination cannot help, as it cannot introduce a
# constant.
def _assumed_set():
  f = os.path.join(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), 'ml', 'CHEATS.md')
  out = {}
  try: rows = open(f)
  except OSError: return out
  for l in rows:
    m = re.match(r'\| `([^`]*)` \| `([^`]*)` \| (.*) \|', l)
    if m: out.setdefault(m.group(1), m.group(3).strip())
  return out

ASSUMED = _assumed_set()

# which way of the old chain of strategies means that the
# definition recurses, which is what says whether it has an
# induction theorem to give
NOT_RECURSIVE = {'new_definition', 'new_recursive_definition',
                 'define_single', 'general'}
RECURSIVE = {'prim_rec', 'nested', 'maplist', 'cond_bool', 'sing',
             'cases', 'match', 'lift_if', 'measure', 'guess'}

# the strategies that are a rewriting of the clauses, because HOL
# Light's machinery does not take them as HOL4 writes them.  The
# word stands at the call site (define_shaped "cases" ...), so that
# the file is as plain about those as about the rest.
SHAPES = {'nested', 'maplist', 'cond_bool', 'sing', 'cases',
          'match', 'lift_if'}

# three of the rewritings hand what comes out back to a way of
# making a definition, and the harvest records both names as one
# word ("sing>nested").  What the way is called goes by the first
# of them; the whole word is what the call site says.
def head_way(strat):
  return strat.split('>')[0]


def recursive_text(text, names):
  """whether the clauses recurse: a name that the definition
     defines occurs in them more often than it heads a clause"""
  heads = 0
  for m in re.finditer(r"(?:`|/\\)\s*(?:\(\s*)?"
                       r"(?:!\s*[^.]*?\.\s*)?(?:\(\s*)?"
                       r"([A-Za-z_][A-Za-z0-9_']*)", text):
    if m.group(1) in names: heads += 1
  uses = sum(len(re.findall(r"\b%s\b" % re.escape(nm), text))
             for nm in names)
  return uses > heads
hterm.NAME_MAP = overrides.NAME_MAP
hterm.TYPE_MAP = overrides.TYPE_MAP
hterm.TYPE_ABBREV = overrides.TYPE_ABBREV

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'
SRC = hol4.SRC

HEAD = '''(* ======================================================== *)
(*  %s: ported from HOL4's
%s  *)
(* ======================================================== *)
'''

# the theories that the second part of the first pass ports (the
# proof theories, of which it takes the definitions)
PROOFTHYS = set(l.split('\t')[0]
                for l in open(T + 'order1b.txt').read().split('\n')
                if l)


# HOL4 declarations that only configure its parser or its
# simplifier, and that the port does not need
IGNORE_ML = [
  r'numLib\.', r'ParseExtras\.', r'diminish_srw_ss', r'Parse\.',
  r'monadsyntax', r'temp_', r'hide ', r'export_theory',
  r'bring_to_front_overload', r'Globals\.', r'computeLib',
  r'set_grammar_ancestry', r'type_abbrev', r'overload_on',
  r'Datatype\.', r'val _ = TeX', r'remove_ovl_mapping',
]


def lay(pre, words, width=75):
  """lay out the words in lines of at most width characters, the
     first line starting with pre and the others indented like it,
     with two spaces after a full stop"""
  lines = []
  cur = pre
  for w in words:
    sep = '' if cur == pre else '  ' if cur.endswith('.') else ' '
    if len(cur) + len(sep) + len(w) <= width or cur == pre:
      cur += sep + w
    else:
      lines.append(cur)
      cur = pre + w
  lines.append(cur)
  return lines


def fill(pre, words, width=77, tight=False):
  """lay out the words in lines of at most width characters, the
     first line starting with pre and the others indented by 3.
     With tight the first word follows pre with no space, which is
     what a quotation wants (`:num, not `: num)"""
  lines = []
  cur = pre
  for w in words:
    if cur == pre and (tight or pre.endswith('"') or
                       pre.endswith(' ')):
      cur += w
    elif len(cur) + 1 + len(w) <= width:
      cur += ' ' + w
    else:
      lines.append(cur)
      cur = '   ' + w
  lines.append(cur)
  return lines


# where the needs of a file go (they are known at the end of a run)
NEEDS = '(*__NEEDS__*)'


def strip_ml(text, strings=True):
  """the text without its comments (and, with strings, without its
     strings), which is what the needs of a file are computed from;
     a quotation is code, and a (* in one is not a comment, but a
     // in one is (that is what HOL Light reads it as), so the
     words of a comment of the source are no names of the port"""
  out = []
  i = 0
  n = len(text)
  depth = 0
  while i < n:
    c = text[i]
    if depth:
      if text.startswith('(*', i): depth += 1; i += 2
      elif text.startswith('*)', i): depth -= 1; i += 2
      else: i += 1
      continue
    if text.startswith('(*', i):
      depth = 1; i += 2; continue
    if c == '`':
      j = text.find('`', i + 1)
      if j < 0: j = n
      out.append(re.sub(r'(?m)//.*$', '', text[i+1:j]))
      i = j + 1; continue
    if c == '"' and strings:
      i += 1
      while i < n and text[i] != '"':
        i += 2 if text[i] == '\\' else 1
      i += 1; continue
    out.append(c); i += 1
  return ''.join(out)


DEBUG_NAMES = os.environ.get('CAKE_DEBUG_NAMES')
# with RETRY=1 the table of the statements that HOL Light does not
# read is ignored, so that a harvest of the port it writes says
# which of them the port reads now: an entry that a run does not
# bear out any more is a statement won back
RETRY_UNSTATED = os.environ.get('RETRY') == '1'


def dbg(where, old, new):
  """with CAKE_DEBUG_NAMES set, say which pass of the port wrote
     a name out, which is how a wrong one is found"""
  if DEBUG_NAMES and old != new:
    print('%-12s %s -> %s' % (where, old, new))
  return new


def ocaml_name(n):
  """the name of the OCaml binding of a definition: HOL Light's
     parser takes an identifier of capitals as a value name, but
     not one that starts with a capital and has small letters"""
  if n[:1].isupper() and not any(c.isupper() for c in n[1:]):
    return n[0].lower() + n[1:]
  return n


QUOTE = chr(34)


def nquotes(text):
  """the quotes that OCaml sees: an escaped one is part of a
     string and does not open or close one (lexer_fun has a
     comment with a HOL4 string with \\" in it)"""
  return len(re.findall(r'(?<!\\)' + QUOTE, text))


def balance_quotes(text):
  """OCaml reads a " in a comment as the start of a string, so a
     comment with an odd number of them does not lex (CakeML's
     compilerScript has a quote of its own in a comment, to
     balance the ones of SML's lexer).  One more is added at the
     end, where it is still inside the comment."""
  return text if nquotes(text) % 2 == 0 else text + ' ' + QUOTE


def verbatim(text):
  """a comment of a HOL4 source, as it stands.  The comments of
     the sources are kept unaltered, whatever they are about, so
     the lines of one may be longer than the port's own are (the
     one thing that has to be put right is a quote that OCaml
     would read as the start of a string)"""
  out = '\n'.join(l.rstrip() for l in text.split('\n'))
  if nquotes(out) % 2 == 0: return out
  i = out.rfind('*)')
  return out[:i] + QUOTE + ' ' + out[i:] if i >= 0 else out + ' ' + QUOTE


def shorten(text, width=79):
  """break the lines of a comment of the port's own that are too
     long; a line that opens the comment is continued under its (* """
  out = '\n'.join(wrap(l.rstrip(), 0, width,
                       3 if l.lstrip().startswith('(*') else 2,
                       hard=True)
                  for l in text.split('\n'))
  if nquotes(out) % 2 == 0: return out
  # the quote goes inside the comment, before it closes
  i = out.rfind('*)')
  return out[:i] + QUOTE + ' ' + out[i:] if i >= 0 else out + ' ' + QUOTE


UNRESOLVED = {}   # theory -> name -> how often it stayed bare


class Porter:
  def __init__(self, db, thy):
    self.db = db
    self.thy = thy
    self.path = db.thy_of_file[thy]
    self.kind = db.kind_of_thy[thy]
    names = db.names_for(thy)
    # a name that means another constant in this theory than it
    # does elsewhere in the port
    for (t, nm), new in overrides.LOCAL_NAMES.items():
      if t == thy: names[(thy, nm)] = new
    # the size function of a type that the scope resolves to
    # another one than HOL4 means
    tynames0 = db.names_for(thy, True)
    for nm, t in overrides.SIZE_OF.get(thy, {}).items():
      base = nm[:-len('_size')]
      names[(thy, nm)] = tynames0.get((t, base), base) + '_size'
    fields, amb = db.fields_for(thy)
    self.amb = amb
    flds = {f: t for f, t in fields.items() if t}
    flds.update(overrides.FIELD_OF.get(thy, {}))
    # the type abbreviations in scope, and the ones of them that
    # the port declares with new_type_abbrev: a type is written
    # with those rather than expanded, as the source writes it
    # (flatLang's pat has (ctor_id # type_group_id) option)
    self.abbrevs, self.declared_abbrevs = db.abbrevs_for(thy)
    # the names that mean one theory's constant everywhere in
    # this file (overrides.CON_FILE)
    cf = overrides.CON_FILE.get(thy, {})
    # a name whose theory depends on how many arguments it takes
    # (clos_to_bvlProof's Var is bvl's where it takes a number
    # and closLang's where it takes a trace and a number)
    self.con_file_ar = {k: v for k, v in cf.items()
                        if isinstance(v, dict)}
    self.con_file = {k: v for k, v in cf.items()
                     if not isinstance(v, dict)}
    # the names that the port gives the constants, so that a size
    # function is not made for a name that is one of them
    self.constnames = set(db.names_for(thy).values())
    self.fieldvar = overrides.FIELD_VAR.get(thy, {})
    self.ctx = hterm.Ctx(names=names, fields=flds,
                         tynames=db.names_for(thy, True),
                         overloaded=db.overloaded_for(thy),
                         recs=db.recs_for(thy), thy=thy,
                         rectys=db.rectys_for(thy),
                         accessors=overrides.ACCESSORS.get(thy, {}),
                         updaters=overrides.UPDATERS.get(thy, {}),
                         cons=db.cons_for(thy), abbrevs=self.abbrevs,
                         ambfields=db.ambiguous_fields(),
                         con_argty=db.con_argty_for(thy),
                         defnames=db.defnames_for(thy))
    self.ctx.arm_thys = self.arm_thys
    self.ctx.body_pr = self.pr_body
    # HOL4's auxiliary size functions of a datatype family
    # (exp1_size, exp2_size, ...), as the term the port writes
    # for each (overrides.AUX_SIZE)
    self.ctx.auxsize = dict(
      (nm, txt) for (t2, nm), txt in overrides.AUX_SIZE.items()
      if t2 == thy)
    # a name HOL4 overloads is written out as the constant it
    # means in this theory, so that HOL Light has one name per
    # constant and nothing is resolved while a file loads
    self.ctx.resolve = self.resolve_overload
    self.ctx.accessor_names = {}
    # the record types that the blocks of this file have named so
    # far (two_pass), and the record arguments of the constants
    # that this file defines (note_ownrec)
    self.filerecs = set()
    self.ownrec = {}
    self.ctx.fieldvar = self.fieldvar
    self.ctx.recdflt = dict(overrides.FIELD_DEFAULT)
    # a name that LOCAL_NAMES gives this theory is written as that
    # name, also where the port overloads it (word_bignumProof's
    # Eval is an overload of its own relation, and ast has an Eval
    # as well, which the overload does not keep apart)
    for (t, nm) in overrides.LOCAL_NAMES:
      if t == thy: self.ctx.overloaded.discard(nm)
    # the names that are types, so that the parser knows where a
    # type that is not in parentheses ends
    self.ctx.tyops = (
      {k[1] if isinstance(k, tuple) else k
       for k in self.ctx.tynames} |
      set(self.ctx.tynames.values()) | set(self.abbrevs) |
      db.types_in_scope(thy) |
      dbmod.hl_types() | set(overrides.TYPE_MAP))
    self.out = []
    self.warn = []
    # which entries of overrides.FILE_PATCH this file has used, so
    # that one that matches nowhere in it is reported and the
    # table does not rot
    self.filepatched = set()
    # the proofs of phase three: a theorem of proofs/<path>.prf
    # gets the tactic that stands there, one that is not in it
    # keeps its CHEAT_TAC (tools/proofstore.py)
    # phase three has not started: the proof store is kept and
    # not spliced in, so every theorem is the CHEAT_TAC that
    # phase two leaves (overrides.PHASE_THREE)
    self.proofs = (proofstore.load(db.mlpath_of(thy))
                   if overrides.PHASE_THREE else {})
    self.proved = set()
    # how often a theorem name has been stated, for a source that
    # states two theorems of the same name (HOL4's allow_rebind):
    # the second one's proof is the section <name>#2
    self.thmseen = {}
    self.head = None
    self.deps = []
    self.anc_comments = {}  # a comment of the Ancestors block
    self.restore = set()   # the infixes to put back at the end
    self.conof_said = {}   # the theory an override gives a name
    self.front_thy = {}    # and the one a bring_to_front gives it
    self.conof_arities = {}  # the theory per number of arguments
    self.conof_wild = False  # did the override use the wildcard?
    self.conbody = {}      # the constructors of the body only
    self.defkey = None     # the definition that is being ported
    self.defnames_was = {}  # the names DEF_NAMES took the place of
    self.defnames_ovl = set()
    self.rec_src = {}      # record type -> [(field, type)]
    self.annotated = {}    # the terms a pattern resolved
    self.intargs = set()   # arguments that hold an integer
    self.intresult = False # is the result an integer?
    self.argtypes = {}     # the type an override gives an argument
    self.ml_skip = None    # the last ML block that OCaml replaces
    self.arrflds = []      # the array fields of the monadic state
    self.bound = set()
    self.contys = set()
    # the size functions this file has made (size_prelude)
    self.sizes_made = set()
    self._con_ovl = None
    self.conof = {}
    self.iffeq = False
    # an overload of an ancestor does not shadow a constant that
    # this theory defines itself (semanticPrimitives defines
    # num_cmp, which comparison has as an overload of num_compare)
    # the term grammar of the theory, before the bodies of its
    # overloads are read below: with the one that the file before
    # it left, a token that another theory overloads too would be
    # read as that theory's (parmove's RTC of its own step read as
    # the Cons of backend_common)
    db.base_grammar(thy)
    raw = {nm: txt for nm, txt in db.overloads_for(thy).items()
           if not any(t == thy and k in ('def', 'con', 'rel')
                      for t, k in db.defs.get(nm, []))
           and not self.is_overloaded(nm, txt)}
    self.raw_overloads = raw
    # which theory declares every overload: its body is read with
    # the record fields of that theory, where the field it
    # mentions is the one that HOL4 means (labSem's read_reg is
    # s.regs of a labSem state, also in a theory that has
    # stackSem's regs in scope as well)
    self.ovl_thy = db.overload_thy_for(thy)
    for _ in range(3):
      for nm, txt in raw.items():
        # the name of the overload itself is the constant in its
        # own body (stack_to_lab overloads Asm with
        # \a. Asm (Asmi a), whose Asm is labLang's)
        old = self.ctx.overloads.pop(nm, None)
        # the accessor of a field in the body is written out: a
        # statement that is read with the overloads of the field
        # names taken away would read the name as its own variable
        # (labSem's read_reg is \r s. s.regs r, and
        # stack_to_labProof's compile_jump_correct has a variable
        # regs).  Where the body of one overload reads a field of
        # two records in one statement, that is one record too few
        # (PENDING.md: lab_to_targetProof's word_cmp_lemma)
        self.ctx.qualfields = self.ovl_thy.get(nm) or ''
        try: self.ctx.overloads[nm] = self.in_thy(
                 self.ovl_thy.get(nm), lambda: self.term(txt))
        except Exception:
          if old is not None: self.ctx.overloads[nm] = old
        finally:
          self.ctx.qualfields = ''
    self.bound = set()

  # -- helpers ---------------------------------------------------

  def is_overloaded(self, nm, txt):
    """is this HOL4 overload one that the port declares as an
       overload of HOL Light instead of expanding it?  (the name of
       a constant of another theory of the port, which expanding
       would resolve the wrong way there)"""
    return (bool(re.match(r"^[A-Za-z][A-Za-z0-9_']*$", txt.strip())) and
            len({t for t, _ in self.db.defs.get(nm, [])}) > 1)

  def theorem(self, b):
    """a theorem of a source: its name, its attributes and its
       statement, with CHEAT_TAC where HOL4 has its proof (phase
       two; phase three puts a proof there)"""
    # HOL4's Triviality is a Theorem with the attribute local
    at = list(b.attrs)
    if b.kind == 'Triviality' and 'local' not in at:
      at.append('local')
    self.state(b, b.name, at, b.body)

  def extra_wanted(self, text):
    """is this block of the overrides one the port writes out?
       A block that introduces a constant always is; one that is
       there for a proof alone waits for phase three"""
    return overrides.PHASE_THREE or not overrides.proof_only(text)

  def prove_head(self, name):
    """the head of a theorem: `let foo = prove`, or the name and
       the prove on two lines where that does not fit"""
    head = 'let %s = prove' % name
    return head if len(head) <= 79 else 'let %s =\n  prove' % name

  def annot_vars(self, e, vs):
    """a statement that uses the name of a record accessor for a
       variable of its own says the type of that variable, so that
       HOL Light reads it as a variable and not as the accessor
       (tools/fieldvars.py)"""
    vs = dict(vs)
    if not vs or not isinstance(e, hterm.Node): return False
    done = set()

    def wrap(v):
      done.add(v.name)
      return hterm.Node('rawtyped', tok=v.tok, e=v,
                        tytext=vs[v.name])

    def go(n):
      for k, v in list(n.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node):
          if v.kind == 'id' and v.name in vs and v.name not in done:
            setattr(n, k, wrap(v))
          else:
            go(v)
        elif isinstance(v, list):
          for i, w in enumerate(v):
            if not isinstance(w, hterm.Node): continue
            if w.kind == 'id' and w.name in vs \
               and w.name not in done:
              v[i] = wrap(w)
            else:
              go(w)

    go(e)
    self.varannot |= done
    return bool(done)

  def state(self, b, nm, at, body):
    """the statement of a theorem of a source, with its name and
       its attributes; b is the block it comes from, which a
       pointer at the source needs"""
    # what the port puts before this theorem: the helpers that the
    # proofs of the file ask for and the source has not, where they
    # need something the file itself defines and so cannot stand at
    # its head (overrides.EXTRA_BEFORE)
    if (self.thy, nm) in overrides.EXTRA_BEFORE and \
       self.extra_wanted(overrides.EXTRA_BEFORE[(self.thy, nm)]):
      self.out.append(
        overrides.EXTRA_BEFORE[(self.thy, nm)].strip() + '\n')
    # a statement that HOL Light's parser rejects would stop the
    # file at that phrase, so the port writes the comment that
    # points at the source in its place, as it does for a
    # statement its own parser cannot read (tools/unstated.py,
    # which a harvest writes; every entry is one to win back)
    if (self.thy, nm) in unstated.NAMES and not RETRY_UNSTATED:
      self.warn.append('%s %s: HOL Light does not read the statement'
                       % (b.kind, nm))
      self.out.append(self.at(
        b, 'a theorem whose statement HOL Light does not read'
           ' (tools/unstated.py): %s' % nm))
      return
    name = self.bindname(nm)
    # HOL4's [simp] says the theorem belongs to the set that its
    # simplifier reaches for.  HOL Light says that with a call,
    # after the theorem, as Isabelle's [simp] and Lean's @[simp]
    # do (tactics/simpset.ml); the attributes that HOL Light has
    # no counterpart for stay in the comment that records what
    # the source said
    simp = 'simp' in at
    at = [a for a in at if a != 'simp']
    attrs = ('[' + ','.join(at) + ']') if at else ''
    self.ctx.defining = set()
    self.ctx.intnums = False
    self.ctx.intneg = False
    self.intargs = set()
    self.intresult = False
    # the record type and the theories of the constructors that
    # the last definition had are not the ones of this statement
    self.ctx.reclit = overrides.RECORD_OF.get((self.thy, nm))
    self.contys = set()
    # the variables of a statement that hold an integer, where
    # nothing in the statement says so (overrides.THM_INT_VARS)
    self.ctx.intvars = set(
      overrides.THM_INT_VARS.get((self.thy, nm), []))
    # a name that this statement means another constant by
    # (overrides.THM_NAMES)
    was = {}
    wasovl = set()
    for n, new in overrides.THM_NAMES.get((self.thy, nm), {}).items():
      # the entry of the theory as well: a name that the port
      # resolves for the whole file (an ambiguous constructor) has
      # one, and that one wins over the bare name
      for k in (n, (self.thy, n)):
        was[k] = self.ctx.names.get(k)
        self.ctx.names[k] = new
      # a name that the port overloads is written as it stands, so
      # a statement that means one constant of it has the overload
      # taken off for this statement (the Seq of data_simpProof's
      # evaluate_Seq_Skip is dataLang's, which nothing in the
      # statement says)
      if n in self.ctx.overloaded:
        self.ctx.overloaded.discard(n)
        wasovl.add(n)
    # the record type of a variable, for this statement only
    # (overrides.FIELD_VAR_DEF, which a definition takes the same
    # way): the env of source_to_flatProof is a sem_env in most of
    # its statements and an environment of flatSem in some
    fv = overrides.FIELD_VAR_DEF.get((self.thy, nm))
    if fv:
      self.ctx.fieldvar = dict(self.fieldvar)
      self.ctx.fieldvar.update(fv)
    # the record types of the literals of this statement, in the
    # order in which they stand in it (overrides.THM_RECLITS)
    self.ctx.reclits = list(
      overrides.THM_RECLITS.get((self.thy, nm), []))
    # the accessor of a record field for this statement only
    # (overrides.THM_ACCESSORS): a statement may use the name of a
    # field for a variable of its own and read the field of a
    # record as well (lab_to_targetProof's
    # asm_fetch_NOT_ffi_entry_pcs has a variable ffi_names and
    # reads mc_conf.ffi_names), and then the accessor cannot be
    # the overloaded name
    acc = overrides.THM_ACCESSORS.get((self.thy, nm))
    if acc:
      self.ctx.accessors = dict(self.ctx.accessors)
      self.ctx.accessors.update(acc)
    # a statement whose ~ is the complement of a word
    # (overrides.WORD_NOT, which a definition takes the same way:
    # word_bignumProof's evaluate_SeqTempImmNot is about Word (~w))
    self.ctx.wordnot = (self.thy, nm) in overrides.WORD_NOT
    # the theory whose constructor a name of this statement means
    # (overrides.CON_OF, which a definition takes the same way):
    # the Seq of data_simpProof's evaluate_Seq_Skip is dataLang's,
    # which the evaluate of the statement does not say
    conof = dict(overrides.CON_OF.get((self.thy, nm), {}))
    # a wildcard says the theory of every constructor name of it
    # that the port overloads, as it does for a definition: a
    # statement about one intermediate language has the If, the
    # Call and the Var of that language and of a dozen others
    if '*' in conof:
      t = conof.pop('*')
      for (t2, ty), (cons, _) in self.db.datatypes.items():
        if t2 != t: continue
        for c in cons:
          if c in self.ctx.overloaded: conof.setdefault(c, t)
    self.conof_arities = {k: v for k, v in conof.items()
                          if isinstance(v, dict)}
    for k in self.conof_arities: del conof[k]
    for k, v in self.con_file_ar.items():
      self.conof_arities.setdefault(k, v)
    self.conof_said = conof
    # no definition is being ported: this is a statement
    self.defkey = None
    try:
      # the statement is a quotation in a function, so that one
      # that does not typecheck is no error of the file but a
      # cheat of its own that the reports count (THEOREM_THUNK)
      hterm.ANTIQ_STRICT[0] = True
      hterm.DROP_TYVAR_ANNOT[0] = ((self.thy, nm)
                                   in overrides.THM_NO_TYVARS)
      hterm.UNIFY_TYVAR_ANNOT[0] = ((self.thy, nm)
                                    in overrides.THM_TYVARS)
      hterm.TYVAR_SEEN.clear()
      try:
        want = fieldvars.VARS.get(nm, [])
        self.varannot = set()
        stmt = fmt(self.term(body, defn=False, varty=want),
                   indent=3, width=79, last=2)
        vars_read = nm in fieldvars.READ or \
                    (bool(want) and
                     set(v for v, _ in want) - self.varannot)
        if vars_read:
          # the statement has to be read with the overloads taken
          # away, so it is rendered one indent deeper
          stmt = fmt(self.term(body, defn=False), indent=5,
                     width=79, last=2)
      finally:
        hterm.ANTIQ_STRICT[0] = False
        hterm.DROP_TYVAR_ANNOT[0] = False
        hterm.UNIFY_TYVAR_ANNOT[0] = False
        self.ctx.wordnot = False
        if fv: self.ctx.fieldvar = self.fieldvar
        if acc:
          self.ctx.accessors = overrides.ACCESSORS.get(self.thy, {})
        self.ctx.reclits = []
        self.conof_said = {}
        self.ctx.overloaded |= wasovl
        for k, old2 in was.items():
          if old2 is None: self.ctx.names.pop(k, None)
          else: self.ctx.names[k] = old2
    except Exception as ex:
      self.warn.append('%s %s: %s' % (b.kind, nm, ex))
      # a theorem that the ML code of a source states itself is one
      # of its ML, whatever the reason the port has for not stating
      # it, so the pointer at it says that (the lines it points at
      # are ML and no Theorem of the source)
      self.out.append(self.at(
        b, ('a theorem that HOL4 states as the value of an ML'
            ' expression: %s' % nm) if b.kind == 'ML' else
           ('a theorem whose statement the port cannot state yet:'
            ' %s' % nm)))
      return
    # phase three: the proof of this theorem, where there is one.
    # The proof store names a theorem by the binding it gets, which
    # is what a proof of the file names it by as well
    EMITTED.append((self.thy, nm, name))
    self.thmseen[name] = self.thmseen.get(name, 0) + 1
    key = '%s#%d' % (name, self.thmseen[name])
    tac = self.proofs.get(key)
    if tac is None: key, tac = name, self.proofs.get(name)
    if tac is not None: self.proved.add(key)
    # the attributes that HOL4 gives the theorem are part of what
    # the source says and nothing of the port acts on them, so
    # they stand in a comment over the theorem -- with the name of
    # the source where the binding is not that name itself (two
    # files that state a theorem of one name: the later one has
    # the name of its theory in front of it)
    head = self.size_prelude(stmt)
    if attrs or name != nm:
      head += ('(* %s%s *)\n'
              % (nm if name != nm else '', attrs)).replace('(*  *)',
                                                           '')
    # a spot of a statement that no rule can resolve: the Jump
    # inside a LabAsm of lab_to_targetProof is labLang's and the
    # Jump beside it asm's, and both take one argument, so nothing
    # but the place says which is which.  A patch that does not
    # apply is an error and not a silence
    stmt = patch_text(stmt, overrides.THM_PATCH.get((self.thy, nm), []),
                      'THM_PATCH')
    stmt = file_patch(self.thy, stmt, self.filepatched)
    if vars_read:
      # the statement uses the name of a record accessor for a
      # variable of its own and the port cannot say its type in
      # the statement (the type has a variable of its own, or the
      # statement is one that HOL4 computes): it is read with the
      # overloads of the field names taken away
      head += ('(* the names of record fields that this statement'
               ' uses for\n   variables of its own are read as'
               ' variables *)\n')
      self.out.append('%s%s\n (cake_as_vars (fun () ->\n'
                      '    `%s`),\n%s);;'
                      % (head, self.prove_head(name), stmt,
                         tac or '  CHEAT_TAC'))
    else:
      self.out.append('%s%s\n (`%s`,\n%s);;'
                      % (head, self.prove_head(name), stmt,
                         tac or '  CHEAT_TAC'))
    if simp: self.out.append('add_simp %s;;' % name)
    # the binding is there, so a source that states a theorem as
    # the value of this one (Theorem foo = bar) can use it
    dbmod.bind_thm(self.db, self.thy, nm, name)

  def front_overloads(self, b):
    """a source that brings an overload to the front (HOL4's
       bring_to_front_overload) says which constant a name means
       from there on: the port says the same with the
       hol4_overload of the name that it gives that constant.
       Without it the name means whatever theory overloaded it
       last, which is a statement about another constant and no
       check can see it (the name that it prints is the same)."""
    out = []
    for m in re.finditer(r'bring_to_front_overload\s*"([^"]+)"\s*'
                         r'(\{[^{}]*\})?', b.text, re.S):
      nm, blk = m.group(1), m.group(2) or ''
      n2 = re.search(r'Name\s*=\s*"([^"]+)"', blk)
      thy = re.search(r'Thy\s*=\s*"([^"]+)"', blk)
      new = None
      if n2 and thy:
        new = self.ctx.names.get((thy.group(1), n2.group(1)))
        if new is None and thy.group(1) == self.thy:
          new = n2.group(1)
      if new is None:
        self.warn.append('bring_to_front_overload %s: the port does'
                         ' not know which constant' % nm)
        out.append(self.at(b, 'an overload that the source brings to'
                              ' the front: %s' % nm))
      else:
        # the port writes the constant out wherever the name
        # stands, so what the source brings to the front is a
        # resolution of that name from here on and not a
        # declaration of HOL Light's
        self.front_thy[nm] = thy.group(1)
        out.append(self.at(
          b, 'an overload that the source brings to the front: %s,'
             ' written out as %s' % (nm, new)))
    return out

  def bindname(self, name):
    """the OCaml binding that a block of this theory gets: its own
       name, or the name with the theory in front of it where that
       name is one of HOL Light\'s or one that another theory of the
       port has already taken.  OCaml has one namespace, so two
       files that bind one name are whichever loaded last, and a
       proof that names it gets the wrong theorem or the wrong
       definition with no error -- which is what this prevents, for
       a theorem and for a definition alike (PORTING-GUIDE.md,
       entries 9 and 9a)"""
    nm = ocaml_name(name)
    if nm in self.db.hl or nm in self.db.hlids or \
       nm in self.db.thmnames:
      # the theory in front of it, by the prefix that the port
      # puts in front of a constant of that theory: the binding of
      # flatLang's pat_bindings_def is flat_pat_bindings_def,
      # beside the flat_pat_bindings that it defines
      nm = ocaml_name(dbmod.short_thy(self.thy) + '_' + name)
    self.db.thmnames.add(nm)
    return nm

  def resolve_thm(self, name):
    """the OCaml binding of the port for a theorem that a source
       names, where the port has it: the theorem of the theory
       that the source says (listTheory.oEL_def), or, where it
       says none, the one of this file before the one of another
       -- and nothing where two files of the port bind the name
       and the source does not say which is meant"""
    if '.' in name:
      thy, nm = name.rsplit('.', 1)
      if thy.endswith('Theory'): thy = thy[:-6]
      b = self.db.thmbind_thy.get((thy, nm))
      if b: return b
      if nm not in self.db.thmbind_many and nm in self.db.thmbind:
        return self.db.thmbind[nm]
      return (overrides.THM_MAP.get(name) or
              overrides.THM_MAP.get(nm) or
              (nm if nm in self.db.hlids else None))
    b = self.db.thmbind_thy.get((self.thy, name))
    if b: return b
    if name in self.db.thmbind_many:
      # the theory of the name is the closest one of the scope
      # that has it, as HOL4 resolves it to the one that the
      # ancestry of the file loads last (db.distance)
      d = self.db.distance(self.thy)
      cs = [(d[t], t) for t in self.db.thmbind_name.get(name, ())
            if t in d]
      if cs: return self.db.thmbind_name[name][min(cs)[1]]
    elif name in self.db.thmbind:
      return self.db.thmbind[name]
    # a theorem of HOL Light itself, which the two systems share
    # under one name (FUN_EQ_THM, MAP, LENGTH) or under two
    # (HOL4's LET_THM is HOL Light's LET_DEF)
    nm = overrides.THM_MAP.get(name)
    if nm: return nm
    # a theorem of HOL Light goes by a name with a capital in it
    # (FUN_EQ_THM, MAP, o_DEF); a short name without one is a
    # local of the ML of the source (HOL4's th), which the port
    # has nothing of
    return (name if len(name) > 2 and any(c.isupper() for c in name)
            and name in self.db.hlids else None)

  def eval_defs(self, text, skip=()):
    """the definitions that a term reaches, innermost last: what
       HOL4 has in the compset of its whole development and the
       port has to say"""
    seen, order, work = set(skip), [], [text]
    while work:
      t = work.pop()
      for w in re.findall(r"[A-Za-z_][A-Za-z_0-9']*", t):
        if w in seen or w not in DEF_BODY: continue
        seen.add(w)
        order.append(DEF_BODY[w][0])
        work.append(DEF_BODY[w][1])
    return order

  def evalconv(self, text):
    """the HOL Light expression that computes the value of a term,
       which HOL4 computes with the compset of its whole
       development: the port unfolds the definitions that the term
       reaches and reduces the arithmetic"""
    order = self.eval_defs(text)
    if not order: return None
    try:
      tm = self.term(text, defn=False)
    except Exception:
      return None
    return 'CAKE_EVAL [%s] `%s`' % ('; '.join(order), tm)

  def evaldefs(self, name):
    """the same for the right-hand side of a definition, which a
       source evaluates by its name (CONV_RULE (RAND_CONV EVAL)
       x64_names_def): the definition itself is not one to unfold,
       because its own left-hand side is what is evaluated"""
    nm = name.split('.')[-1]
    if nm.endswith('_def'): nm = nm[:-4]
    if nm not in DEF_BODY: return None
    body = DEF_BODY[nm][1]
    order = self.eval_defs(body, dbmod.definition_names(body))
    return '[%s]' % '; '.join(order) if order else None

  def derived(self, b):
    """a theorem that HOL4 states as the value of an ML
       expression of the derived rules: the port computes it the
       same way, so the theorem is there with a proof"""
    key = (self.thy, b.name)
    if key in overrides.NO_DERIVE: return None
    e, why = derive.translate(b.text, self.resolve_thm,
                              lambda t: self.term(t, defn=False),
                              self.evalconv, self.evaldefs)
    if not e:
      self.warn.append('derive %s: %s' % (b.name, why))
      return None
    return e

  def srcname(self):
    """the path of the HOL4 source, over as many lines as it
       takes to stay within the line length"""
    p = re.sub(r'^.*/(cakeml-src|hol4-src)/', '', self.path)
    out = ''
    line = '    '
    for part in p.split('/'):
      part = part + ('' if part.endswith('.sml') else '/')
      if len(line) + len(part) > 77 and line.strip():
        out += line + '\n'
        line = '      '
      line += part
    return out + line

  def at(self, b, what, kw=None):
    """a comment that points at a block of the HOL4 source.  The
       port holds no HOL4 code, not even in a comment, so where it
       cannot say what the source says it says where to read it:
       the file and the lines of the block, or of the part of it
       that starts at the line kw (Termination, Proof)"""
    f = re.sub(r'^.*/', '', self.path)
    a = getattr(b, 'src', 0) or 0
    z = getattr(b, 'src_end', 0) or a
    if kw is not None and b.text:
      for i, l in enumerate(b.text.split('\n')):
        if l.strip() == kw:
          a = a + i
          break
    where = '%s:%d' % (f, a) if z <= a else '%s:%d-%d' % (f, a, z)
    return '\n'.join(fill('(* HOL4 %s:' % where,
                          what.split(), 76)) + ' *)'

  def nm(self, n):
    return self.ctx.name(n)

  def tnm(self, n):
    return self.ctx.tyname(n)

  def expand_syms(self, text):
    """a symbolic name that a source overloads and that is not an
       infix of its grammar (parmove's turnstile for wf) is not a
       token that the term grammar of the port reads, so the body
       of the overload takes its place before the text is read"""
    for nm in sorted(self.raw_overloads, key=len, reverse=True):
      if (IDENT.match(nm) or nm in hterm.INFIX or nm in hterm.SYMS
          or nm not in text):
        continue
      body = dbmod.strip_quote(self.raw_overloads[nm])
      text = text.replace(nm, ' (' + body + ') ')
    return text

  def left_comments(self, toks, text, pos=False):
    """the comments of these tokens that the text has not: one at
       the end of a term, and one before a token that the port
       writes out without a token of its own (the brace of a set),
       has nothing to stand before, so it goes at the end
       (word_copy's copy_prop_prog ends in (* impossible? *))"""
    out = []
    for t in toks:
      for c in (t.comments or ()):
        if any(q in c for q in hterm.QUOTES): continue
        ls = hterm.comment_text(c)
        if all(('// ' + l) in text for l in ls): continue
        out += [(t.pos, l) for l in ls] if pos else ls
    return out

  def term(self, text, annotate=False, defn=True,
           varty=None):
    text = self.expand_syms(text)
    toks = hterm.tokenize(text)
    p = hterm.Parser(toks, self.ctx)
    e = p.parse()
    if p.peek().kind != 'eof':
      t = p.peek()
      raise SyntaxError(f'unparsed input at {t.pos}: {t.text!r}')
    e = self.conof_arity(
          self.arg_cons(self.arm_intvars(self.lambda_cons(e))))
    if not defn:
      e = self.beta_overloads(e)
    old = self.ctx.vars
    oldint = self.ctx.intvars
    oldfv = self.ctx.fieldvar
    # a statement says nowhere which of its variables hold an
    # integer, so the types of the constants of the port say it
    if not defn:
      self.ctx.intvars = oldint | self.int_vars_by_type(e)
    # an annotation of a variable says which record its fields are
    # of, wherever the term reads one of them, and so does the
    # type of a constant that it stands in an argument of -- which
    # the overrides and an annotation of the term come before
    fv = dict((k, v) for k, v in self.recarg_fieldvars(e).items()
              if k not in self.ctx.fieldvar)
    fv.update(self.annot_fieldvars(e))
    if fv:
      self.ctx.fieldvar = dict(self.ctx.fieldvar)
      self.ctx.fieldvar.update(fv)
    # a variable whose name the port overloads with a record
    # accessor says its type, so that HOL Light reads a variable
    if varty: self.annot_vars(e, varty)
    self.ctx.vars = self.shadowing(e, defn)
    # the patterns of the first clause of every function carry the
    # type of their constructor where its name is one that several
    # theories in scope have, so that it is resolved as HOL4 does
    seen = set()
    for cl in hterm.conjuncts_of(e):
      try:
        h = hterm.strip_app(hterm.clauses_of(cl)[0][0])[0]
        nm = h.name if h.kind == 'id' else None
      except Exception:
        nm = None
      if nm is None or nm in seen: continue
      seen.add(nm)
      self.annotate(cl, not annotate)
    oldloose = self.ctx.loose_rhs
    self.ctx.loose_rhs = hterm.lone_eqn(e)
    try:
      out = self.two_pass(lambda: hterm.Printer(self.ctx).pr(e, 0))
      if defn: self.note_ownrec(e)
      for l in self.left_comments(toks, out):
        out += '\n  // ' + l
      return out
    finally:
      self.ctx.vars = old
      self.ctx.intvars = oldint
      self.ctx.fieldvar = oldfv
      self.ctx.loose_rhs = oldloose

  def two_pass(self, f):
    """print a term, and where it reads a field of a record type
       that several theories have (the refs of a state) and
       nothing says which of them it is, print it again with the
       record that the rest of the term settles on.  HOL4 reads
       such a field by the type of what it is of, and the port has
       no types: what it has is the other fields of the term, and
       a term that names one record is about that one"""
    self.ctx.recseen = set()
    self.ctx.recamb = set()
    self.ctx.recpick = {}
    self.ctx.recvar = {}
    oldfv = self.ctx.fieldvar
    wild = self.ctx.wild
    out = f()
    self.filerecs |= self.ctx.recseen
    pick = {}
    for fld in self.ctx.recamb:
      cands = [r for r in self.ctx.recseen
               if fld in self.ctx.recs.get(r, ())]
      # a block that says nothing about the record itself is read
      # with what the file says: one file is about the states of
      # one language, and the one that is about two (a proof that
      # relates a pass to its source) names both and settles
      # nothing, which is what the overrides are for
      if not cands:
        cands = [r for r in self.filerecs
                 if fld in self.ctx.recs.get(r, ())]
      if len(cands) == 1: pick[fld] = cands[0]
    # and the records that the block settled the variables on
    fv2 = dict((v, r) for v, r in self.ctx.recvar.items()
               if v not in self.ctx.fieldvar)
    if not pick and not fv2: return out
    # the second pass starts where the first did: the wildcards of
    # a term are numbered as they are printed, and a term that is
    # printed twice would number them on from the first pass
    self.ctx.recpick = pick
    if fv2:
      self.ctx.fieldvar = dict(self.ctx.fieldvar)
      self.ctx.fieldvar.update(fv2)
    self.ctx.wild = wild
    self.ctx.head_for = None
    try:
      return f()
    finally:
      self.ctx.recpick = {}
      self.ctx.fieldvar = oldfv

  def ovl_lambdas(self):
    """the overloads whose body is a lambda that reads a record
       field, as (the variables it binds, the body): the record
       of such a field is the one of the argument that the
       application has, which is not the same in every statement
       (the read_reg of lab_to_targetProof's word_cmp_lemma is the
       regs of a labSem state on one side of the equation and of
       an asm_state on the other)"""
    if getattr(self, '_ovllam', None) is not None: return self._ovllam
    out = {}
    for nm, txt in self.raw_overloads.items():
      try:
        e = hterm.Parser(hterm.tokenize(dbmod.strip_quote(txt)),
                         self.ctx).parse()
      except Exception:
        continue
      while e.kind == 'paren': e = e.e
      if e.kind != 'quant' or e.q != '\\': continue
      if not all(v.kind == 'id' for v in e.vs): continue
      if not self.has_field(e.body): continue
      out[nm] = ([v.name for v in e.vs], e.body)
    self._ovllam = out
    return out

  def has_field(self, e):
    """does this term read a record field?"""
    if not isinstance(e, hterm.Node): return False
    if e.kind in ('field', 'recupd'): return True
    for k, v in e.__dict__.items():
      if k == 'tok': continue
      if isinstance(v, hterm.Node):
        if self.has_field(v): return True
      elif isinstance(v, (tuple, list)):
        for x in v:
          if isinstance(x, hterm.Node) and self.has_field(x):
            return True
          if isinstance(x, (tuple, list)):
            for y in x:
              if isinstance(y, hterm.Node) and self.has_field(y):
                return True
    return False

  def subst_node(self, e, sub):
    """a copy of a term with the variables of sub replaced"""
    if not isinstance(e, hterm.Node): return e
    if e.kind == 'id' and e.name in sub: return sub[e.name]
    # a binder of the body that binds one of them keeps it
    if e.kind == 'quant':
      sub = {k: v for k, v in sub.items()
             if k not in [x.name for x in e.vs if x.kind == 'id']}
      if not sub: return e
    d = {}
    for k, v in e.__dict__.items():
      if k == 'tok': d[k] = v
      elif isinstance(v, hterm.Node): d[k] = self.subst_node(v, sub)
      elif isinstance(v, list):
        d[k] = [self.subst_node(x, sub) if isinstance(x, hterm.Node)
                else ([self.subst_node(y, sub)
                       if isinstance(y, hterm.Node) else y
                       for y in x] if isinstance(x, (tuple, list))
                      else x) for x in v]
      elif isinstance(v, tuple):
        d[k] = tuple(self.subst_node(x, sub)
                     if isinstance(x, hterm.Node) else x for x in v)
      else: d[k] = v
    n = hterm.Node(e.kind, **{k: v for k, v in d.items()
                              if k != 'kind'})
    return n

  def beta_overloads(self, e):
    """the applications of such an overload with the arguments put
       in, so that the field of its body is read with the record of
       the argument that is there"""
    lam = self.ovl_lambdas()
    if not lam: return e

    def go(x):
      if not isinstance(x, hterm.Node): return x
      for k, v in list(x.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): setattr(x, k, go(v))
        elif isinstance(v, list):
          setattr(x, k, [go(y) if isinstance(y, hterm.Node) else
                         (tuple(go(z) if isinstance(z, hterm.Node)
                                else z for z in y)
                          if isinstance(y, tuple) else y)
                         for y in v])
      if x.kind != 'app': return x
      h, args = hterm.strip_app(x)
      if h.kind != 'id' or h.name not in lam: return x
      vs, body = lam[h.name]
      if len(args) < len(vs): return x
      sub = dict(zip(vs, args[:len(vs)]))
      out = self.subst_node(body, sub)
      for a in args[len(vs):]:
        out = hterm.Node('app', tok=x.tok, fn=out, arg=a)
      return out

    return go(e)

  def int_vars_by_type(self, e):
    """the variables of a term that stand where a constant takes an
       integer (tools/intargs.txt), so that a numeral beside one of
       them is an integer too (linear_scanProof's 0 <= beg, whose
       beg is the beginning of an interval)"""
    out = set()
    nums = set()

    def intpos(nm):
      """the int arguments of a constant, also where the name is
         one that the port overloads: every constant of that name
         has to take an int there"""
      ps = hterm.int_arg_pos(nm)
      if ps: return ps
      cands = [self.db.rename.get((t, nm), nm)
               for t, k in self.db.defs.get(nm, [])
               if k in ('con', 'def', 'rel')]
      sets = [hterm.int_arg_pos(c) for c in cands]
      return (set.intersection(*sets) if sets and all(sets)
              else set())

    def go(n):
      # a variable under the & of HOL4 is a number and not an
      # integer, whatever another part of the statement does with
      # the name (bvlSem's do_int_app_eq_some has an n that one
      # conjunct gives to Const, which takes an int, and another
      # to & )
      if n.kind == 'prefix' and n.op == '&':
        b = n.e
        while b.kind == 'paren': b = b.e
        if b.kind == 'id': nums.add(b.name)
      if n.kind == 'app':
        h, args = hterm.strip_app(n)
        if h.kind == 'id':
          nm = self.ctx.name(h.name)
          for i in intpos(nm):
            if i < len(args):
              a = args[i]
              while a.kind == 'paren': a = a.e
              if a.kind == 'id': out.add(a.name)
          # and the variables that a lambda in such a place binds
          for i, js in hterm.int_fn_arg_pos(nm).items():
            if i >= len(args): continue
            a = args[i]
            while a.kind == 'paren': a = a.e
            if a.kind != 'quant' or a.q != '\\': continue
            for j in js:
              if j < len(a.vs) and a.vs[j].kind == 'id':
                out.add(a.vs[j].name)
      for t in hterm.subnodes(n): go(t)

    go(e)
    return out - nums

  def recarg_fieldvars(self, e):
    """the record of a variable that stands where a constant of the
       port takes one (tools/recargs.txt): the s of bvlSem's
       evaluate (xs,env,s) is a state of bvlSem, and that is how a
       reader of the source knows which refs the s.refs of the
       same statement is -- HOL4 knows it from the type"""
    out = {}

    def bare(a):
      while a.kind in ('paren', 'typed', 'rawtyped'): a = a.e
      return a.name if a.kind == 'id' else None

    def parts(a):
      """the components of a tuple, which HOL4 writes with , at
         the loosest precedence"""
      while a.kind == 'paren': a = a.e
      ps = []
      while a.kind == 'infix' and a.op == ',':
        ps.append(a.l); a = a.r
      ps.append(a)
      return ps

    def res_pos(a):
      """the record components of the result of a term that is an
         application of a constant of the port"""
      while a.kind in ('paren', 'typed', 'rawtyped'): a = a.e
      h, args = hterm.strip_app(a)
      if h.kind != 'id': return {}
      return hterm.rec_res_pos(self.ctx.name(h.name), len(args))

    def go(n):
      if n.kind == 'app':
        h, args = hterm.strip_app(n)
        if h.kind == 'id':
          nm = self.ctx.name(h.name)
          pos = hterm.rec_arg_pos(nm) or self.ownrec.get(nm, {})
          for (i, j), rec in pos.items():
            if i >= len(args): continue
            a = args[i]
            if j is not None:
              ps = parts(a)
              if len(ps) < 2 or j >= len(ps): continue
              a = ps[j]
            v = bare(a)
            if v: out.setdefault(v, rec)
      # and the variables that the result of such a constant is
      # bound to: 'evaluate (xs,env,s) = (res,s1)' says that the
      # s1 of it is a state of the same language as the s, and so
      # does the let that binds it
      pairs = []
      if n.kind == 'infix' and n.op == '=':
        pairs = [(n.l, n.r), (n.r, n.l)]
      elif n.kind == 'let':
        pairs = [(v, pt) for pt, v in n.binds]
      for a, b in pairs:
        pos = res_pos(a)
        if not pos: continue
        for j, rec in pos.items():
          if j is None:
            v = bare(b)
            if v: out.setdefault(v, rec)
          else:
            ps = parts(b)
            if len(ps) > 1 and j < len(ps):
              v = bare(ps[j])
              if v: out.setdefault(v, rec)
      for t in hterm.subnodes(n): go(t)

    go(e)
    return out

  def note_ownrec(self, e):
    """the record arguments of a constant that this file defines,
       read off its definition: the port resolved the s and the t
       of 'state_rel b s t' from what the definition of state_rel
       says of them, and a statement after it that applies
       state_rel says the same of its own variables, which is how
       a reader of the source reads it (recarg_fieldvars).  The
       table of tools/recargs.txt comes from a session, so a file
       that does not load yet is not in it, and these are exactly
       the files that need it"""

    def head(cl):
      n = cl
      while True:
        if n.kind == 'paren': n = n.e
        elif n.kind == 'quant' and n.q == '!': n = n.body
        elif n.kind == 'infix' and n.op == '==>': n = n.r
        elif n.kind == 'infix' and n.op in ('=', '<=>'): n = n.l
        elif n.kind in ('typed', 'rawtyped'): n = n.e
        else: return hterm.strip_app(n)

    for cl in hterm.conjuncts_of(e):
      try:
        h, args = head(cl)
      except Exception:
        continue
      if h.kind != 'id': continue
      nm = self.ctx.name(h.name)
      if hterm.rec_arg_pos(nm): continue
      d = self.ownrec.setdefault(nm, {})
      for i, a in enumerate(args):
        while a.kind in ('paren', 'typed', 'rawtyped'): a = a.e
        if a.kind != 'id': continue
        rec = self.ctx.fieldvar.get(a.name)
        if rec: d.setdefault((i, None), rec)

  def annot_fieldvars(self, e):
    """the record of a variable that the term says the type of: a
       statement that writes (s:('a,'c,'ffi)labSem$state) means the
       fields of a state of labSem wherever it reads a field of s,
       also where the theory means another record by that name
       (stack_to_labProof's s is a state of stackSem in most of its
       statements and one of labSem in two of them)"""
    out = {}
    pr = hterm.Printer(self.ctx)

    def go(n):
      if n.kind == 'typed':
        v = n.e
        while v.kind == 'paren': v = v.e
        if v.kind == 'id':
          rec = pr.annot_rec(n)
          if rec: out.setdefault(v.name, rec)
          # a variable that two annotations of the statement give
          # two records says nothing (the port keeps the first)
      for t in hterm.subnodes(n): go(t)

    go(e)
    return out

  def shadowing(self, e, defn=True):
    """HOL4 lets a variable shadow a constant, HOL Light does not,
       so a bound variable whose name is a constant of the port or of
       HOL Light is renamed.  Without defn the term is not a
       definition, so the arguments of its left hand side are not
       bound by it (the SND of a statement about MAP (SND o SND) is
       the constant)"""
    # an overload of HOL4 whose value is a constructor is a
    # constant, not a variable, where it occurs in a pattern; an
    # overload of a function cannot stand in a pattern, so there
    # it is a variable (word_copy matches on Shift shift r1 r2 n,
    # and wordLang overloads shift with backend_common's
    # word_shift)
    names = hterm.bound_names(e, self.ctx.cons | self.con_overloads(),
                              defn)
    # a bound variable is not a reference to a constant, so it does
    # not make the file need the theory of a constant of that name
    self.bound |= names
    return {n: n + "'" for n in names if self.is_const(n)}

  def con_overloads(self):
    """the names that HOL4 overloads with a constructor"""
    if self._con_ovl is None:
      cons = set()
      for (thy, ty), (cs, flds) in self.db.datatypes.items():
        for c in cs:
          cons.add(self.ctx.names.get((thy, c), c))
          cons.add(c)
      out = {n for n, t in self.ctx.overloads.items()
             if t.strip() in cons}
      # an overload that the port declares as an overload of HOL
      # Light instead of expanding it is not in ctx.overloads,
      # and its name is a constructor all the same: comparison
      # overloads Less with the LESS of ternaryComparisons, and
      # a pattern Less is that constructor, not a variable
      anc = self.db.scope(self.thy) | {self.thy}
      for (t, nm), (txt, local) in self.db.overloads.items():
        if t in anc and txt.strip() in cons: out.add(nm)
      self._con_ovl = out
    return self._con_ovl

  def keeps_name(self, thy, n):
    """whether the port gives a definition of a theory the name
       that the HOL4 source gives it.  A name that every theory
       defining it renames away is the name of no constant of the
       port, so a variable of that name clashes with nothing and
       keeps its own name -- which is what the port is after,
       because HOL4 writes that name.  One definition of prog in
       the whole distribution (backend_x64_eval's, which is the
       empty program of a cv_compute experiment) would otherwise
       put a prime on six hundred variables of the compiler's
       proofs"""
    return ((thy, n) not in self.db.rename and
            overrides.RENAME_CONST.get((thy, n), n) == n)

  def is_const(self, n):
    # a name that the port overloads the accessors of a record
    # field with is a constant of HOL Light as well
    return (n in self.db.hl or n in self.db.provided or
            n in set(self.db.ambiguous_fields().values()) or
            any(k not in ('type', 'tyabbrev') and self.keeps_name(t, n)
                for t, k in self.db.defs.get(n, [])))

  def typ(self, text, keep=False):
    ty = hterm.parse_type_text(text)
    ty = hterm.expand_type(ty, self.abbrevs,
                           self.declared_abbrevs if keep else None)
    return hterm.print_type(ty, self.ctx)

  # -- the blocks ------------------------------------------------

  def run(self):
    blocks = hol4.parse(self.path)
    # the names that HOL4 reads as variables in this theory,
    # because no theory in its ancestry defines them; of a HOL4
    # library theory the port has the definitions and no
    # statement, so it needs no list
    hide, hideconsts = (([], []) if self.kind == 'lib'
                        else self.db.hidden_for(self.thy, blocks))
    self.ctx.hidden = set(hide)
    self.hideconsts = hideconsts
    # the theories that the source of this file can see, which the
    # library closes over the lists of those theories themselves
    # (tools/db.py, announce).  A HOL4 library theory of the library
    # layer registers its overloads before any file of the port
    # announces a theory, so it is in the scope of every file and is
    # not in the list
    self.anc_scope = ([] if self.kind == 'lib'
                      else self.db.announce(self.thy))
    self.hidmore = False
    self.hidnames = set()
    self.varannot = set()
    self.db.base_grammar(self.thy)
    # an infix that an ancestor overloads with a constant is written
    # as an application of that constant
    anc = self.db.ancestors(self.thy)
    for (thy, tok), (txt, loc) in self.db.ovl_infix.items():
      # a token that this theory overloads itself is what its own
      # Overload says, not what an ancestor says (parmove's ▷ is
      # its step, and backend_common overloads the same token
      # with its Cons)
      if (self.thy, tok) in self.db.ovl_infix and thy != self.thy:
        continue
      if (thy in anc and not loc and tok in hterm.OWN_INFIX
          and IDENT.match(txt)):
        hterm.set_infix_name(tok, self.ctx.name(txt))
    # an infix that the ML code of an ancestor maps to a constant
    # (pegTheory's ~> is ignoreL), with the name of the port
    for t in sorted(anc):
      for tok, nm, temp in self.db.fixname.get(t, []):
        if not temp: hterm.set_infix_name(tok, self.ctx.name(nm))
    chunks = []                 # (blank lines before, text)
    for b in blocks:
      before = len(self.out)
      try:
        # a loose_equality or tight_equality declaration changes the
        # precedence of = from here on
        mode = hol4.equality_mode(b.text) if b.kind == 'ML' else None
        if mode: hterm.set_equality(mode == 'loose')
        if b.kind == 'ML':
          for tok, prec, ass, _ in hol4.fixities(b.text):
            hterm.add_infix(tok, prec, ass)
          for tok, nm, _ in hol4.mapped_names(b.text):
            hterm.set_infix_name(tok, self.ctx.name(nm))
          if hol4.pmatch_mode(b.text): hterm.enable_pmatch(True)
          self.enable_monad(b.text)
          # the ML values that the file antiquotes into its terms
          for nm, v in hol4.ml_terms(b.text):
            hterm.ANTIQ[nm] = v
          # a variable that the ML code makes with the type of a
          # value of an earlier block (data_to_word_gcProof's s1
          # has the type of its s, which is in another block)
          for nm, var, other in hol4.ml_var_types(b.text):
            m = re.match(r"^\(?\s*[A-Za-z0-9_']+\s*:\s*(.*?)\)?$",
                         (hterm.ANTIQ.get(other) or '').strip(),
                         re.S)
            if m:
              hterm.ANTIQ[nm] = '(%s:%s)' % (var, m.group(1))
          # and the ones that ML code computes, which the
          # overrides give as the expression that HOL4 evaluates
          for (t, nm), v in overrides.ANTIQUOTE.items():
            if t == self.thy: hterm.ANTIQ[nm] = v
        self.block(b)
      except Exception as ex:
        self.warn.append(f'{b.kind} {b.name}: {ex}')
        # the port holds no HOL4 code, so what it could not
        # translate is a pointer at the source, as everything
        # else it cannot say is
        self.out.append(
          '\n'.join(fill('(* PORT FAILED: %s %s:' % (b.kind, b.name),
                          str(ex).split(), 76)) + ' *)\n'
          # "the ml" is no English and no pointer that
          # tools/nohol4.py can test; an ML block that the port
          # could not read is ML code like any other
          + self.at(b, 'the ML code' if b.kind == 'ML'
                       else 'the %s' % b.kind.lower()))
      new = self.out[before:]
      if new:
        # the needs of the port start a paragraph of their own
        blanks = max(1, b.blanks) if b.kind == 'Ancestors' else b.blanks
        chunks.append((blanks, '\n'.join(new)))
    # the blank lines of the HOL4 source are kept between the blocks,
    # so that a comment stays with what it belongs to
    text = ''
    for i, (blanks, c) in enumerate(chunks):
      if i: text += '\n' * (1 + min(blanks, 2))
      text += c
    # the head of the file goes where the Ancestors block of the
    # source put the marker; a source that has no Ancestors block
    # of its own (location, ternaryComparisons, errorMonad) gets it
    # under the banner, or the file would have no needs lines and
    # no line to say that it is of no theory of the port -- and the
    # overloads it registers would go down as the theory of the
    # file whose needs loaded it
    if NEEDS not in text:
      text = NEEDS + '\n\n' + text
    text = (self.head + '\n' + text if self.head else text) + '\n'
    # an infix that this file overloads with an append of its own is
    # the one of HOL Light again for the files that come after
    if self.restore:
      # hol4_only, because the overload of this file would
      # otherwise still be there for the files after it, where an
      # infix between two variables has nothing to resolve it
      # (semantics' prelude ++ prog)
      text += '\n' + ''.join(
          'hol4_only "%s" "%s";;\n'
          % (tok, overrides.BASE_INFIX_CONST[tok])
          for tok in sorted(self.restore))
    # a hide list stays in the session until the next one, so a
    # file that makes one takes it back at the end of itself --
    # also where the list is one that a Parse.hide of the source
    # added to (bvlSem hides str and labProps mem, and neither has
    # a list of its own)
    if hide or self.hidmore:
      text += ('\n(* and the names it reads as variables are'
               ' constants again *)\n'
               'let _ = do_list unhide_constant\n  [' +
               ';\n   '.join('"%s"' % n for n in
                              sorted(set(hide) | self.hidnames)) +
               '];;\n')
    # every file that said which theories it can see puts the
    # interface back, a file whose source has no CakeML ancestor as
    # well: it cut the interface down to nothing of the port
    # and the interface it cut down to its own scope goes back
    if self.hideconsts or self.kind != 'lib':
      text += '\n(* and the interface *)\nlet _ = unhide_overloads ();;\n'
    # the lemmas that the port adds to this theory, which a proof
    # of phase three asks for and the source has not: they are in
    # tools/extra/<theory>.ml, so that a re-port keeps them (a
    # block written into the generated file by hand is thrown away
    # the next time the port runs)
    xp = T + 'extra/' + self.thy + '.ml'
    if os.path.exists(xp):
      text += '\n' + open(xp).read().rstrip() + '\n'
    # and the ones this port takes from LightCake, the other HOL
    # Light port of CakeML, whose HOL4 library layer is proved
    # (tools/lightcake.py writes them; README.md says where the
    # clone comes from)
    lp = T + 'lightcake/' + self.thy + '.ml'
    if os.path.exists(lp):
      text += '\n' + open(lp).read().rstrip() + '\n'
    # the files that the translation needs
    deps = sorted(set(self.deps) |
                  self.db.providers(self.thy, strip_ml(text),
                                    self.bound))
    needs = sorted(set('needs "%s";;' % self.db.mlpath_of(d)
                       for d in deps if d in self.db.thy_of_file))
    # a comment that the Ancestors block of the source has after an
    # ancestor stands after the needs line of that one
    cmt = dict((('needs "%s";;' % self.db.mlpath_of(t)), cs)
               for t, cs in self.anc_comments.items()
               if t in self.db.thy_of_file)
    lines = []
    for n in needs:
      lines.append(n)
      lines += cmt.pop(n, [])
    for cs in cmt.values():
      lines += cs
    needs = lines
    head = '\n'.join(needs) if needs else \
           '(* this file needs nothing of the port *)'
    # the theories whose names the source of this file can read:
    # the overloads of all the others come out of the interface
    # while the file loads, so that a name that no type pins down
    # is the constant that HOL4 reads there and not the one of the
    # theory that the load order registered last (ml/lib/theorem.ml,
    # cake_theory; ISSUES.md "A statement that means another
    # theory's constant")
    # every file of the port says it, a file whose source has no
    # ancestor of its own as well: the line is what says which
    # theory the overloads that the file registers are of, and
    # without it they would go down as the theory of the file
    # before it (misc, mllist, backend_common, db_vars and
    # gc_shared have no CakeML ancestor)
    if self.kind == 'lib':
      # a HOL4 library theory is of no theory of the port: the
      # overloads it registers are in the scope of every file, and
      # a needs of it stands inside a file that is a theory
      head += ('\n\n(* of no theory of the port: what it registers'
               ' is in the scope of every file *)\n'
               'let _ = cake_library ();;')
    if self.kind != 'lib':
      lines = ['  ["' + self.anc_scope[0] + '"'] if self.anc_scope \
              else []
      for n in self.anc_scope[1:]:
        # the last line of the list carries the ];; as well
        if len(lines[-1]) + len(n) + 7 > 79:
          lines.append('   "' + n + '"')
        else:
          lines[-1] += '; "' + n + '"'
      head += ('\n\n(* the theory of this file, and the ones its'
               ' statements read *)\nlet _ = cake_theory "%s"'
               % self.thy
               + ('\n' + ';\n'.join(lines) + '];;' if lines
                  else ' [];;'))
    if hide:
      # a Parse.hide of the source: the name is a variable in this
      # file and a constant again at the end of it, which is what
      # HOL Light's hide_constant says
      lines = ['let _ = do_list hide_constant ["' + hide[0] + '"']
      for n in hide[1:]:
        if len(lines[-1]) + len(n) + 4 > 77:
          lines.append('       "' + n + '"')
        else:
          lines[-1] += '; "' + n + '"'
      head += '\n\n' + ';\n'.join(lines) + '];;'
    # the constants of a name that the accessors of a record field
    # have as well, which only the file that cannot see them takes
    # out of the interface
    if self.hideconsts:
      head += ('\n\n(* this file reads the name of a record field as'
               ' a variable and\n   needs the accessors of that field'
               ' as well, so only these\n   pairs come out of the'
               ' interface *)\nlet _ = hide_overloads\n  [' +
               ';\n   '.join('"%s","%s"' % (n, c)
                              for n, c in self.hideconsts) + '];;')
    # an entry of overrides.FILE_PATCH that matched nowhere in
    # this file is one the port no longer needs, or one that was
    # written for text the port does not say any more
    for i, (was, _) in enumerate(overrides.FILE_PATCH.get(self.thy, [])):
      if i not in self.filepatched:
        self.warn.append('FILE_PATCH matches nothing: %s' % was)
    return text.replace(NEEDS, head)

  def wanted(self, b):
    """of a HOL4 library theory only the needed definitions are ported"""
    if self.kind != 'lib': return True
    # and none of its theorems: the theorems of the port are
    # CakeML's, and what it needs of a HOL4 library is what phase
    # three takes from it
    if b.kind in ('Theorem', 'Triviality', 'ThmValue'): return False
    if b.kind == 'Datatype':
      names = []
      for ty, cons, flds in hol4.datatype_names(b.body):
        names += [ty] + cons + flds
    elif b.kind in ('Definition', 'Inductive', 'CoInductive'):
      names = dbmod.definition_names(b.body)
      # the rules of an inductive definition are not equations, so
      # the names of the relations come from their conclusions
      if not names: names = dbmod.rule_names(b.body)
    elif b.kind in ('Type', 'Overload'):
      names = [b.name]
    else:
      return True
    return self.db.is_needed(self.thy, names)

  def block(self, b):
    k = b.kind
    if self.kind == 'lib' and k in ('Comment', 'ML'):
      # the comments and the ML code of a library theory are not
      # in the port, but a grammar that its ML code makes is a
      # datatype and a definition (simpleSexp's sexpNT and sexpG)
      if k == 'ML' and 'mk_grammar_def' in b.text:
        self.grammar_block(b)
      elif k == 'ML' and 'tailrec_define "' in b.text:
        self.tailrec_block(b)
      elif k == 'ML':
        self.numeral_form(b)
      return
    if not self.wanted(b):
      return
    # the ML code that the port has in OCaml: it is written where
    # the source has its ML, and the blocks that it covers are
    # dropped (they are ported, so there is no reason to keep them
    # in a comment)
    if k in ('ML', 'Comment') and self.ml_ported(b):
      # a comment inside the ML that the port has in OCaml holds
      # HOL4 code as well (word_bignum has a line of its ML
      # commented out), so a pointer says where that code is
      if k == 'Comment' and commented_code(b.text):
        self.out.append(self.at(b, 'code that the source has in a'
                                   ' comment'))
      return
    if k == 'Comment':
      # a comment block of the source can have ML code after the
      # comment (word_bignum's get_exp has '(* Var *) let' on one
      # line), and that code is not OCaml
      if commented_code(b.text):
        self.out.append(self.at(b, 'code that the source has in a'
                                   ' comment'))
      elif comment_only(b.text):
        self.out.append(verbatim(b.text))
      else:
        self.out.append(self.at(b, 'a comment with ML code after it,'
                                   ' which the port does not have'))
    elif k == 'Theory':
      # the header of the port comes first, before the comments that
      # the HOL4 file has before its Theory line
      self.head = HEAD % (b.name, self.srcname())
    elif k == 'Ancestors':
      # an ancestor may be marked as [qualified]; a comment of the
      # block names no ancestor (dataSem's says "semantics
      # shouldn't depend on compiler", whose words are theories of
      # the port)
      deps = [re.sub(r'\[.*\]', '', w)
              for w in hol4.strip_comments(b.body).split()] + \
             overrides.EXTRA_NEEDS.get(self.thy, [])
      # a comment of the block is about the ancestor before it, so
      # it goes after the needs line of that one
      last = None
      # an ancestor may be marked, and the mark is no name
      # (wordSem's "ffi[qualified] (* for call_FFI *)")
      for m in re.finditer(r"\(\*.*?\*\)|[A-Za-z][A-Za-z0-9_']*",
                           re.sub(r'\[[^\]]*\]', '', b.body or ''),
                           re.S):
        if m.group(0).startswith('(*'):
          if last:
            self.anc_comments.setdefault(last, []).append(
              ' '.join(m.group(0).split()))
        else:
          last = m.group(0)
      # the needs are computed from the translation, which uses the
      # names that the port gives the constants, so they are filled
      # in at the end of the run.  A source may have a second
      # Ancestors block (word_to_stackProof's
      # Ancestors[ignore_grammar]), whose ancestors the port needs
      # as well and which is no second needs block
      self.deps = sorted(set(self.deps) | set(deps))
      if NEEDS not in self.out:
        self.out.append(NEEDS)
      ext = [d for d in deps if d not in self.db.thy_of_file]
      if ext:
        self.out.append('\n'.join(
          fill('(* HOL4 ancestors outside the port:', ext, 76)) + ' *)')
      # a comment of the source about an ancestor that the port
      # does not have stands after that line (wordSem's "for
      # call_FFI"), which is where the ancestor itself is
      for d in ext:
        for c in self.anc_comments.pop(d, []):
          self.out.append(c)
      # definitions that HOL4 generates with ML code, and that the
      # port has by hand
      if self.thy in overrides.EXTRA_HEAD and \
         self.extra_wanted(overrides.EXTRA_HEAD[self.thy]):
        self.out.append('\n' + overrides.EXTRA_HEAD[self.thy].strip())
    elif k == 'Libs':
      pass
    elif k == 'Datatype':
      self.datatype(b)
    elif k == 'Definition':
      self.definition(b)
    elif k == 'Type':
      self.typeabbrev(b)
    elif k == 'Overload':
      self.overload(b)
    elif k in ('Inductive', 'CoInductive'):
      self.inductive(b)
    elif k in ('Theorem', 'Triviality'):
      self.theorem(b)
    elif k == 'ThmValue':
      # where the value is a prover applied to a quotation, that
      # quotation is the statement, and phase two states it
      stmt = hol4.thmvalue_statement(b.text)
      if stmt and b.name:
        self.state(b, b.name, b.attrs, stmt)
        return
      # where the value is a prove of a quotation and nothing but
      # check_thm is applied to it, that quotation is the
      # statement as well (compilerProof's compile_correct, the
      # main correctness theorem of CakeML)
      stmt = hol4.thmvalue_prove(b.text)
      if stmt and b.name:
        self.state(b, b.name, b.attrs, stmt)
        # a comment inside the quotation of the statement: the
        # statement of the port is a quotation of HOL Light, where
        # (* is no comment, so it goes after the statement
        for c in getattr(b, 'incomments', []):
          self.out.append(verbatim(c))
        return
      # where the value is another theorem of a source, and the
      # port has that theorem, the name is that theorem of the
      # port (HOL4's Theorem foo = bar)
      alias = hol4.thmvalue_alias(b.text)
      # the theorem of the file itself before the one of another:
      # HOL4's Theorem foo[allow_rebind] = foo binds the name to
      # what it already stands for here, and a dozen theories of
      # the port have a compile_correct
      abind = self.resolve_thm(alias) if alias else None
      if alias and b.name and abind:
        nm = self.bindname(b.name)
        simp = 'simp' in b.attrs
        ats = [a for a in b.attrs if a != 'simp']
        at = ('[' + ','.join(ats) + ']') if ats else ''
        text = (('(* %s *)\n' % at) if at else '') + \
               ('let %s = %s;;' % (nm, abind))
        if max(len(l) for l in text.split('\n')) > 79:
          text = (('(* %s *)\n' % at) if at else '') + \
                 ('let %s =\n  %s;;' % (nm, abind))
        self.out.append(text + ('\nadd_simp %s;;' % nm if simp else ''))
        dbmod.bind_thm(self.db, self.thy, b.name, nm)
        return
      # a theorem that HOL4 states as the value of an expression
      # of the derived rules of the logic, which HOL Light has as
      # well: the port computes the theorem the same way, so it
      # is there with a proof and not with a pointer
      e = self.derived(b)
      if e and b.name:
        nm = self.bindname(b.name)
        simp = 'simp' in b.attrs
        ats = [a for a in b.attrs if a != 'simp']
        at = ('(* [%s] *)\n' % ','.join(ats)) if ats else ''
        text = at + 'let %s = %s;;' % (nm, e)
        if max(len(l) for l in text.split('\n')) > 79:
          text = at + 'let %s =\n  %s;;' % (nm, wrap(e, 2, 77))
        self.out.append(text + ('\nadd_simp %s;;' % nm
                                if simp else ''))
        dbmod.bind_thm(self.db, self.thy, b.name, nm)
        return
      # a theorem that HOL4 binds to the value of an ML
      # expression, where phase three has worked out what that
      # expression computes and overrides.THM_VALUE says it (in
      # HOL4's own notation, which this file translates as it
      # does every other statement): the statement is the
      # source's, and the proof is the one of the proof store
      stmt = overrides.THM_VALUE.get((self.thy, b.name))
      if stmt and b.name:
        self.state(b, b.name, b.attrs, stmt)
        return
      # a theorem that HOL4 binds to the value of an ML
      # expression: the statement is what that expression
      # computes, which the port cannot
      self.out.append(self.at(b, 'a theorem that HOL4 states as'
                                 ' the value of an ML expression:'
                                 ' %s' % b.name))
    elif k == 'ML':
      # Parse.hide of a source hides a name from there on, which
      # the port says where the source says it: the statements
      # after it read that name as a variable, as HOL4 does
      hid = self.PARSE_HIDE.findall(b.text)
      if hid:
        self.ctx.hidden |= set(hid)
        self.hidmore = True
        self.hidnames |= set(hid)
        self.out.append('let _ = do_list hide_constant [%s];;'
                        % '; '.join('"%s"' % h for h in hid))
      # the bookkeeping of HOL4 (a parse option, a temp_, an
      # export_theory) says nothing that the port can have -- but a
      # block that states a theorem is no bookkeeping block,
      # whatever it mentions (asmProps saves all_pcs as the
      # numLib.SUC_RULE of its definition)
      if any(re.search(pat, b.text) for pat in IGNORE_ML) and \
         not hol4.ml_theorems(b.text):
        # an overload that the source brings to the front is not
        # configuration that the port can do without: it says
        # which constant a name means from there on
        for l in self.front_overloads(b): self.out.append(l)
        return
      if self.numeral_form(b):
        return
      if self.hol_reln(b):
        return
      if self.monadic(b):
        return
      if self.grammar_block(b):
        return
      # a theorem that the ML code of a source states itself (HOL4's
      # val foo = Q.prove(`...`, tactic) is a theorem named foo):
      # phase two states it as it states a Theorem of the source
      ths = hol4.ml_theorems(b.text)
      if ths:
        for nm, stmt, whole in ths:
          if whole:
            self.state(b, nm, [], stmt)
          else:
            self.out.append(self.at(b, 'a theorem that HOL4 states'
                                       ' as the value of an ML'
                                       ' expression: %s' % nm))
        if hol4.ml_terms(b.text):
          self.out.append(self.at(
            b, 'the ML values that the definitions below antiquote'))
        return
      self.warn.append('ML code skipped: ' + b.text.strip()[:60])
      # the ML of a source that binds a term is not lost: the
      # definitions that antiquote it have the term in them
      self.out.append(self.at(
        b, 'the ML values that the definitions below antiquote'
           if hol4.ml_terms(b.text) else
           'a proof' if PROOF_ML.search(b.text) else
           'ML code, not ported'))
    else:
      self.warn.append('unknown block ' + k)

  # -- datatypes -------------------------------------------------

  def datatype(self, b):
    # the comments of the body are kept: one that stands before an
    # alternative is written as the // comment of HOL Light before
    # it, which the parser of the specification skips
    # (ml/lib/define.ml's strip_dslash)
    specs = hol4.split_top(b.body, ';')
    # the names of this block are the ones of its own constants
    self.ctx.defining = set()
    for ty, cons, flds in hol4.datatype_names(b.body):
      self.ctx.defining |= set([ty] + cons + flds)
    parts = []
    for part in specs:
      if not part.strip(): continue
      # a comment of the source before the name of the type
      pre_cs = []
      while True:
        mm = re.match(r"\s*(\(\*.*?\*\))", part, re.S)
        if not mm: break
        pre_cs.append(hterm.comment_text(mm.group(1)))
        part = part[mm.end():]
      m = re.match(r"\s*([A-Za-z][A-Za-z0-9_']*)\s*", part, re.S)
      if not m: raise SyntaxError('datatype: ' + part[:40])
      ty, rest = m.group(1), part[m.end():]
      # a comment between the name of the type and the = is about
      # the first alternative, as one before the name is
      # (holSyntax's update says there what a ConstSpec is,
      # caml_lex's token that the first group are the keywords)
      while True:
        mm = re.match(r"\s*(\(\*.*?\*\))\s*", rest, re.S)
        if not mm: break
        pre_cs.append(hterm.comment_text(mm.group(1)))
        rest = rest[mm.end():]
      if not rest.startswith('='):
        raise SyntaxError('datatype: ' + part[:40])
      rhs = rest[1:].strip()
      if rhs.startswith('<|'):
        self.record(ty, rhs)
        continue
      cons = []
      # a comment of the source stands before the | of the
      # alternative that it is about, so one that follows the
      # constructor of an alternative belongs to the next
      carry = list(pre_cs)
      for alt in hol4.split_top(rhs, '|'):
        alt = alt.strip()
        if not alt: continue
        # a comment on the line of the constructor before it is
        # about that one (ast's op_class has EvalOp (* Eval
        # primitive *)); one that starts a line of its own is
        # about the alternative after it
        cs, same, nxt, seen = list(carry), [], [], False
        carry = []
        i = 0
        while i < len(alt):
          mm = re.compile(r'\(\*.*?\*\)', re.S).match(alt, i)
          if mm:
            txt = hterm.comment_text(mm.group(0))
            if not seen: cs.append(txt)
            else:
              j = mm.start() - 1
              while j >= 0 and alt[j] in ' \t': j -= 1
              (same if j >= 0 and alt[j] != '\n' else nxt).append(txt)
            i = mm.end(); continue
          if not alt[i].isspace(): seen = True
          i += 1
        carry = nxt
        alt = hol4.strip_comments(alt).strip()
        if not alt:
          carry = cs + carry
          continue
        toks = hterm.tokenize(alt)
        cname = toks[0].text
        tp = hterm.TypeParser(toks[1:-1])
        argtys = []
        while tp.i < len(tp.toks):
          argtys.append(tp.parse_dtarg())
        cons.append((cname, argtys, cs, same))
      # a comment that stands after the last alternative has no
      # next one to belong to, so it stays where it is: after the
      # last constructor (reg_alloc's clash_tree)
      if carry and cons:
        c0, a0, cs0, sm0 = cons[-1]
        cons[-1] = (c0, a0, cs0, sm0 + carry)
      parts.append((ty, cons))
    if not parts: return
    def argstr(a):
      # an argument that is one identifier needs no brackets: the
      # parser of a type takes an identifier after it for an
      # operator only where that one is a type of arity above
      # zero (parser.ml's type_constructor), which no argument of
      # a constructor is
      s = self.typ_ast(a, keep=True)
      return s if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", s) \
             else '(%s)' % s

    def esc(l):
      """a quote or a backslash of a comment of the source, which
         stands in an OCaml string here: what OCaml reads is the
         text of the source unaltered (lexer_fun's symbol has
         '["Foo";"Bar"] "<" is Foo.Bar.<')"""
      return l.replace('\\', '\\\\').replace('"', '\\"')

    # the specification without its comments, for the type
    # variables of it.  HOL Light gives the type the type
    # variables of the whole specification, in the order in which
    # it sorts them, so the port knows how to write the type of a
    # constructor; the apostrophe of a comment ("the function's
    # name" of ast's exp) is not one of them
    spec = ';\n'.join(
      '%s = %s' % (self.tnm(ty),
                   ' | '.join(' '.join([self.nm(c)] +
                                       [argstr(a) for a in args])
                              for c, args, _, _ in cons))
      for ty, cons in parts)
    params = sorted(set(re.findall(r"'[A-Za-z][A-Za-z0-9_']*", spec)))
    for ty, _ in parts:
      self.db.ty_params[(self.thy, self.tnm(ty))] = params
    names = [ocaml_name(self.tnm(ty)) for ty, _ in parts]
    lhs = ','.join('%s_INDUCT' % n for n in names[:1]) + ',' + \
          ','.join('%s_RECURSION' % n for n in names[:1])

    # the specification is laid out as the source lays it out: the
    # name of the type, then one constructor to a line under it,
    # and a comment of the source on its own line before the
    # constructor it belongs to.  An OCaml string holds the line
    # breaks themselves -- a break is a space to the parser of the
    # specification, and it is what ends a // comment of it
    # (ml/lib/define.ml's strip_dslash)
    def lay(head, t):
      out, cur = [], head
      for w in t.split(' '):
        if cur == head: cur += w
        elif len(cur) + 1 + len(w) <= 79: cur += ' ' + w
        else:
          out.append(cur)
          cur = '       ' + w
      out.append(cur)
      return out

    lines = []
    for pi, (ty, cons) in enumerate(parts):
      if pi: lines[-1] += ';'
      lines.append(('  "' if not pi else '   ') + self.tnm(ty) + ' =')
      for ci, (c, args, cs, af) in enumerate(cons):
        for cm in cs:
          lines += ['     // ' + esc(l) for l in cm]
        lines += lay('     ' if not ci else '   | ',
                     ' '.join([self.nm(c)] + [argstr(a) for a in args]))
        for cm in af:
          lines += ['     // ' + esc(l) for l in cm]
    # a comment is ended by the line break, so the quote that ends
    # the specification cannot stand on the line of one
    if lines[-1].lstrip().startswith('//'): lines.append('  ')
    text = '\n'.join(lines)
    overloads = self.overloads_of(
      [c for _, cons in parts for c, _, _, _ in cons])
    head = 'let %s = define_datatype' % lhs
    if len(head) > 79:
      head = 'let %s =\n  define_datatype' % lhs
      if max(len(l) for l in head.split('\n')) > 79:
        head = ('let %s,\n    %s =\n  define_datatype'
                % tuple(lhs.split(',')))
    self.out.append('%s\n%s";;' % (head, text))
    if overloads: self.out.append('\n'.join(overloads))
    self.ctx.defining = set()

  def ml_ported(self, b):
    """the ML of a source that the port has in OCaml (ML_PORTED):
       the OCaml takes the place of the run of blocks from the one
       that the key names to the one that the value names"""
    if self.ml_skip:
      if self.ml_skip in b.text: self.ml_skip = None
      return True
    for (t, key), (last, code) in overrides.ML_PORTED.items():
      if t == self.thy and key in b.text:
        self.out.append(code.strip())
        self.ml_skip = last
        return True
    return False

  def tailrec_block(self, b):
    """a function of a HOL4 library theory that ML code defines
       from its step function: mc_multiword builds the routines of
       the bignum library with mc_tailrecLib's
       tailrec_define_from_step, and the port calls its own
       tailrec_define (ml/lib/mc_tailrec.ml) with the same step.
       The port takes all of them: they are the routines that the
       deep embedding of word_bignum is generated from, and one
       of them is the step of another"""
    for m in hol4.TAILREC_ML.finditer(b.text):
      nm, step = m.group(1), m.group(2)
      self.ctx.defining = {nm, nm + '_pre'}
      # the registers of the step function are machine words, so a
      # ~ of one of them is the complement of a word, not the
      # negation of a proposition (which ~ is of the rest)
      self.ctx.wordnotvars = set(re.findall(r"\br[0-9]+\b", step))
      try:
        term = fmt(self.term(step))
      except Exception as ex:
        self.warn.append('tailrec_define %s: %s' % (nm, ex))
        continue
      self.ctx.defining = set()
      self.ctx.wordnotvars = set()
      new = self.nm_defined(nm)
      self.out.append('let %s_def,%s_pre_def =\n'
                      '  tailrec_define "%s"\n  `%s`;;'
                      % (new, new, new, term))

  def grammar_block(self, b):
    """HOL4's mk_grammar_def (of grammarLib) takes a grammar in
       BNF and makes the datatype of its nonterminals and the
       grammar itself; gram makes CakeML's cmlG with it"""
    if 'mk_grammar_def' not in b.text: return False
    info = grammardef.parse_ml(open(self.path).read())
    i = b.text.index('mk_grammar_def')
    j = b.text.index('`', i)
    k = b.text.rindex('`')
    rules = grammardef.parse_bnf(b.text[j + 1:k])
    dt, gr = grammardef.generate(rules, info, self, hterm)
    self.out.append(
      '(* HOL4 makes the datatype of the nonterminals and the\n'
      '   grammar itself with the ML code of grammarLib\n'
      '   (mk_grammar_def); the port writes out what it makes *)')
    self.emit_datatype('\n' + dt)
    self.out.append('\nlet %s_def = new_definition\n  `%s`;;'
                    % (info['gname'], fmt(gr)))
    return True

  def emit_datatype(self, spec):
    """a datatype specification, as define_datatype takes it"""
    pre, spec = ('\n', spec[1:]) if spec.startswith('\n') else ('', spec)
    params = sorted(set(re.findall(r"'[A-Za-z][A-Za-z0-9_']*",
                                   re.sub(r'(?m)//.*$', '', spec))))
    for part in spec.split(';\n'):
      ty = part.split('=')[0].strip()
      self.db.ty_params[(self.thy, ty)] = params
    names = [ocaml_name(part.split('=')[0].strip())
             for part in spec.split(';\n')]
    lhs = '%s_INDUCT,%s_RECURSION' % (names[0], names[0])
    text = '\n'.join(
      ' \\\n'.join(fill('  "' if m == 0 else '   ', part.split(), 76))
      for m, part in enumerate(spec.split('\n')))
    self.out.append('%slet %s = define_datatype\n%s";;'
                    % (pre, lhs, text))

  def typ_ast(self, ty, keep=False):
    ty = hterm.expand_type(ty, self.abbrevs,
                           self.declared_abbrevs if keep else None)
    return hterm.print_type(ty, self.ctx)

  def record(self, ty, rhs):
    inner = rhs[2:rhs.rindex('|>')]
    flds = []
    src = []
    # a comment that stands before the first field belongs to no
    # field, so it goes before the list (reg_alloc's ra_state)
    lead = []
    for f in hol4.split_top(inner, ';'):
      if not f.strip(): continue
      # a comment of the source stands after the field that it is
      # about, before or after the ; that follows it, so the ones
      # before the name of a field belong to the field before it
      before, after, seen = [], [], False
      i2 = 0
      while i2 < len(f):
        mm = re.compile(r'\(\*.*?\*\)', re.S).match(f, i2)
        if mm:
          (after if seen else before).append(mm.group(0))
          i2 = mm.end(); continue
        if not f[i2].isspace(): seen = True
        i2 += 1
      f = hol4.strip_comments(f)
      if not f.strip():
        (flds[-1][2] if flds else lead).extend(before + after)
        continue
      (flds[-1][2] if flds else lead).extend(before)
      name, tytext = f.split(':', 1)
      flds.append([name.strip(), self.typ(tytext.strip()), after])
      try:
        src.append((name.strip(),
                    hterm.expand_type(
                      hterm.parse_type_text(tytext.strip()),
                      self.abbrevs)))
      except Exception:
        src.append((name.strip(), None))
    # the monadic machinery of ml_monadBaseLib needs the fields of
    # the state record and their types
    self.rec_src[self.tnm(ty)] = src
    flds2 = [(f, t) for f, t, _ in flds]
    # a comment of the source stands after the field that it is
    # about, where the fields of the port are a list of strings of
    # OCaml: it goes after the entry of that field, unaltered
    body = ''
    for c in lead:
      body += ('  [' if not body else '   ') + \
              ' '.join(c.split()) + '\n'
    for i, (f, t, cs) in enumerate(flds):
      pre = '  [' if i == 0 and not lead else '   '
      body += ' \\\n'.join(
        fill(pre + '"%s","' % f, t.split(' '), 77)) + '"'
      if i < len(flds) - 1: body += ';'
      for c in cs:
        body += '\n   ' + ' '.join(c.split())
      body += '\n'
    body = body.rstrip('\n')
    # where the last field has a comment of the source after it,
    # the bracket that closes the list goes on a line of its own
    if flds and flds[-1][2]: body += '\n  '
    head = ('let %s_FIELDS = define_record "%s"'
            % (ocaml_name(self.tnm(ty)), self.tnm(ty)))
    if len(head) > 79:
      head = ('let %s_FIELDS =\n  define_record "%s"'
              % (ocaml_name(self.tnm(ty)), self.tnm(ty)))
    self.out.append('%s\n%s];;' % (head, body))
    # the accessor and the update of a field that several record
    # types have become overloads of the name of the field
    amb = self.db.ambiguous_fields()
    for f, _ in flds2:
      if f not in amb: continue
      for n, c in ((amb[f], f), (amb[f] + '_fupd', f + '_fupd')):
        # the overload of a field name is one that HOL4 does not
        # have (there r.stack is syntax and a bare stack is a
        # variable), so the port keeps a list of them: a statement
        # that uses such a name for a variable of its own is read
        # with them taken away (ml/lib/theorem.ml).  The overload
        # of the name that HOL4 gives the accessor itself
        # (state_clock, where every record of the name is a state)
        # is not one of them: HOL4 has that constant, and a
        # statement that reads such a field through it would lose
        # it with the others (stack_to_labProof's
        # flatten_call_correct has the ffi of a state of stackSem)
        # the port writes the accessor out wherever its name
        # stands, so this is a resolution of that name from here
        # on and not a declaration of HOL Light's.  A field name
        # that HOL4 has no constant of (there r.stack is syntax)
        # is in the same map: what it means is the accessor
        self.ctx.accessor_names[n] = '%s_%s' % (self.tnm(ty), c)

  def size_prelude(self, text):
    """a measure or a theorem that uses the size function of a
       datatype needs it to be there; the port makes the size
       functions when a definition first needs one, which is too
       late for a theorem or a measure that stands before any such
       definition.  Making them with the datatype instead takes the
       name that the theory wants (balanced_map calls a constant of
       its own size) and puts every datatype's size lemmas in the
       way of every termination proof, so the file asks for them
       where it needs them"""
    anc = self.db.scope(self.thy) | {self.thy}
    # the name that the port gives the type of that theory, not
    # the one that the name means in this theory's scope
    types = set(self.tnm(t2 + '$' + ty)
                for (t2, ty) in self.db.datatypes if t2 in anc)
    out = ''
    for ty in sorted(set(re.findall(r"([A-Za-z0-9_']+?)_size\d*\b",
                                    text))):
      # a constant whose name happens to end in _size is not the
      # size function of a datatype (sptree's size is sptree_size
      # in the port)
      # the size function of a type of the library layer is in
      # ml/lib/hol4.ml, and making one here would be a second
      # constant that no lemma is about
      if ty not in types: continue
      # a constant of the port that happens to be called after
      # the size of a type is not that size function
      # (balanced_map's size is balanced_map_size in the port)
      if ty + '_size' in self.constnames: continue
      # and a file says it once: a theorem that uses a size
      # function stands after the one that made it
      if ty in self.sizes_made: continue
      self.sizes_made.add(ty)
      out += 'make_size "%s";;\n' % ty
    return out

  PARSE_HIDE = re.compile(r'Parse\.hide\s*"([^"]+)"')

  NUMERAL_FORM = re.compile(r'add_numeral_form\s*\(\s*#"."\s*,'
                           r'\s*SOME\s*"([A-Za-z0-9_\']+)"')

  def numeral_form(self, b):
    """HOL4's add_numeral_form makes & an injection of the type of
       the constant it names as well (simpleSexp's &n is the
       s-expression of the number n), which is an overload of HOL
       Light's & (an injection of the numbers too)"""
    m = self.NUMERAL_FORM.search(b.text)
    if not m: return False
    self.out.append('hol4_numeral_form "%s";;'
                    % self.ctx.name(m.group(1)))
    return True

  def overloads_of(self, names):
    """the declarations that make the names of a block the overloads
       that HOL4 has for them"""
    out = []
    for nm in names:
      # the declaration is global, so it is made for every name
      # that the port renames anywhere, not only for the ones that
      # are ambiguous in the scope of this theory
      if nm not in self.db.overloaded(): continue
      new = self.nm_defined(nm)
      # the declaration is made even where the port keeps the
      # name (the theory walk defines walk, and pattern_comp
      # defines one too): without it the name of the constant is
      # not in the interface of HOL Light, and the overload that
      # another theory declares for its own constant hides it
      if new == nm and not self.is_const(nm): continue
      # nothing: the port writes the constant out wherever the
      # name stands, so HOL Light needs no overload of it
      _ = new
    return out

  def in_thy(self, thy, f):
    """run f with the record fields of another theory, which is
       what the body of an overload that that theory declares
       means (db.overload_thy_for)"""
    if not thy or thy == self.thy: return f()
    fields, amb = self.db.fields_for(thy)
    was = (self.ctx.fields, self.ctx.accessors, self.ctx.updaters,
           self.ctx.fieldvar, self.ctx.recs, self.ctx.rectys)
    flds = {k: v for k, v in fields.items() if v}
    flds.update(overrides.FIELD_OF.get(thy, {}))
    self.ctx.fields = flds
    self.ctx.accessors = overrides.ACCESSORS.get(thy, {})
    self.ctx.updaters = overrides.UPDATERS.get(thy, {})
    self.ctx.fieldvar = overrides.FIELD_VAR.get(thy, {})
    self.ctx.recs = self.db.recs_for(thy)
    self.ctx.rectys = self.db.rectys_for(thy)
    try:
      return f()
    finally:
      (self.ctx.fields, self.ctx.accessors, self.ctx.updaters,
       self.ctx.fieldvar, self.ctx.recs, self.ctx.rectys) = was

  def nm_defined(self, n):
    """the name of the constant that a block defines"""
    old = self.ctx.defining
    self.ctx.defining = {n}
    try:
      return self.ctx.name(n)
    finally:
      self.ctx.defining = old

  # -- definitions -----------------------------------------------

  def schematic(self, b):
    """the schematic variables of a definition are its first
       arguments: HOL4's Definition foo[schematic] takes the free
       variables of the body into the constant, and the port has
       to write them (overrides.SCHEMATIC)"""
    sch = overrides.SCHEMATIC.get((self.thy, b.name))
    if not sch: return
    args = ' '.join(sch)
    for nm in dbmod.definition_names(b.body):
      b.body = re.sub(r"\b%s\b(?!')" % re.escape(nm),
                      nm + ' ' + args, b.body)

  def definition(self, b):
    self.schematic(b)
    name = ocaml_name(b.name)
    key = (self.thy, name)
    # what goes before the block goes there whether the block
    # itself is ported or not (a declaration takes the place of a
    # definition that the port does not make)
    if key in overrides.EXTRA_BEFORE and \
       self.extra_wanted(overrides.EXTRA_BEFORE[key]):
      self.out.append(overrides.EXTRA_BEFORE[key].strip() + '\n')
    key = (self.thy, b.name)
    if key in overrides.NOT_YET:
      self.warn.append('%s: PENDING (%s)'
                       % (b.name, overrides.NOT_YET[key].split('\n')[0]))
      self.out.append(
        '\n'.join(fill('(* PENDING:',
                       overrides.NOT_YET[key].split(), 76)) + ' *)\n'
        + self.at(b, 'the definition'))
      return
    key = (self.thy, name)
    if key in overrides.REPLACE:
      self.out.append(overrides.REPLACE[key].strip())
      return
    body = b.body
    # the binding of the definition in the file: the name of the
    # source, or that name with the theory in front of it where
    # another file of the port has the name already
    bind = self.bindname(b.name)
    dbmod.bind_thm(self.db, self.thy, b.name, bind)
    self.ctx.defining = set(dbmod.definition_names(body))
    self.ctx.intnums = key in overrides.INT_NUMERALS
    self.ctx.intneg = key in overrides.INT_NEG
    self.intargs = (set(overrides.INT_ARGS.get(key, []))
                    | self.int_annotated(body))
    self.intresult = key in overrides.INT_RESULT
    self.argtypes = overrides.ARG_TYPES.get(key, {})
    self.iffeq = key in overrides.IFF_EQ
    self.ctx.intvars = self.int_vars(body) | self.intargs
    self.ctx.reclit = overrides.RECORD_OF.get(key)
    self.ctx.wordnot = key in overrides.WORD_NOT
    self.ctx.append = overrides.PLAIN_APPEND.get(key, False)
    self.ctx.iffeq = key in overrides.IFF_IS_EQ
    # the map from the body of a match arm to its integer
    # variables is for this definition only (a node of another
    # one can have the same id once it is gone)
    self.ctx.armvars = {}
    # and so are the theories that the patterns of the block say
    # (clause_clash sets them where the definition has clauses):
    # without this a definition that the port prints as one term
    # is resolved with the theories of the one before it
    self.contys = set()
    # the theory whose constructor a name means here
    conof = dict(overrides.CON_OF.get(key, {}))
    # a name that the override gives a theory itself, rather than
    # through the wildcard, means that theory everywhere in the
    # definition, also where another pass of the port would
    # resolve it (stackSem's dest_Seq matches on stackLang's Seq)
    # an entry whose value is a dict says the theory per number of
    # arguments: the same name is two constants in one definition
    # (stack_to_lab's compile_no_stubs maps stack_remove's
    # prog_comp over what stack_alloc's prog_comp gives)
    # the constructors that the body of a clause means, where
    # its pattern means another one of that name
    conbody = dict(overrides.CON_BODY.get(key, {}))
    if '*' in conbody:
      t = conbody.pop('*')
      for (t2, ty), (cons, _) in self.db.datatypes.items():
        if t2 != t: continue
        for c in cons:
          if c in self.ctx.overloaded: conbody.setdefault(c, t)
    self.conbody = conbody
    self.defkey = key
    self.conof_wild = '*' in conof
    self.conof_arities = {k: v for k, v in conof.items()
                          if isinstance(v, dict)}
    for k in self.conof_arities: del conof[k]
    for k, v in self.con_file_ar.items():
      self.conof_arities.setdefault(k, v)
    self.conof_said = {k: v for k, v in conof.items() if k != '*'}
    if '*' in conof:
      # every constructor name of that theory
      t = conof.pop('*')
      for (t2, ty), (cons, _) in self.db.datatypes.items():
        if t2 != t: continue
        for c in cons:
          if c in self.ctx.overloaded: conof.setdefault(c, t)
    # the right hand side of a clause is printed with these, the
    # pattern with the names as they are (the pattern of
    # source_to_flat's compile_exp is a constructor of ast and
    # the body builds the one of flatLang with the same name)
    self.conof = conof
    # what the names and the overloads were, so that the block
    # after this one has them again
    self.conof_was = dict((nm, (self.ctx.names.get((self.thy, nm)),
                                nm in self.ctx.overloaded))
                          for nm in conof)
    for nm, t in conof.items():
      if '*' in overrides.CON_OF.get(key, {}): continue
      self.ctx.overloaded.discard(nm)
      # the size function of a datatype is called after the type,
      # so the override names the theory of the type
      if nm.endswith('_size') and (t, nm) not in self.ctx.names:
        self.ctx.names[(self.thy, nm)] = (
            self.ctx.tyname(t + '$' + nm[:-len('_size')]) + '_size')
      else:
        self.ctx.names[(self.thy, nm)] = self.ctx.names.get((t, nm),
                                                            nm)
    # a name that this definition means another constant by
    # (overrides.DEF_NAMES): HOL4's toString is num_to_str of a
    # number and mlint's toString of an integer, and presLang has
    # a definition of each
    self.defnames_was = {}
    self.defnames_ovl = set()
    for n, new2 in overrides.DEF_NAMES.get(key, {}).items():
      for k in (n, (self.thy, n)):
        self.defnames_was[k] = self.ctx.names.get(k)
        self.ctx.names[k] = new2
      if n in self.ctx.overloaded:
        self.defnames_ovl.add(n)
        self.ctx.overloaded.discard(n)
    # the record type of a variable, for this definition only
    fv = overrides.FIELD_VAR_DEF.get(key)
    if fv:
      self.ctx.fieldvar = dict(self.fieldvar)
      self.ctx.fieldvar.update(fv)
      # the body of an overload may read a field of the variable
      self.ovl_was = dict(self.ctx.overloads)
      for nm, txt in self.raw_overloads.items():
        try: self.ctx.overloads[nm] = self.term(txt)
        except Exception: pass
    rawterm = None
    if key in overrides.MATCH_CLAUSES:
      # a family in which one function has the overlapping clauses:
      # the clauses of that function are one quotation with a match
      term = None
      clauses = self.clause_form(
                  body, overrides.MATCH_CLAUSES[key][0])
    elif key in overrides.CLAUSE_FORM:
      # the clauses in separate quotations because the override
      # says so, where what clashes only shows in the right hand
      # sides and clause_clash does not look there
      term = None
      clauses = self.clause_form(body, split=True)
    elif (key in overrides.MATCH_FORM or self.overlapping(body) or
          self.multi_pattern(body)):
      # one clause with a match, which HOL Light handles far better
      # than a definition by patterns on several arguments
      rawterm = self.match_form(body)
      term = fmt(rawterm)
    elif (self.several_clauses(body) and
          key not in overrides.ONE_QUOTATION):
      # HOL4 typechecks every clause of a definition on its own, so
      # the port writes them as separate quotations, with the type
      # of the pattern on each
      term = None
      clauses = self.clause_form(body)
    elif key in overrides.ANNOTATE:
      rawterm = self.term(body, annotate=True)
      term = fmt(rawterm)
    else:
      rawterm = self.term(body)
      term = fmt(rawterm)
    rel = overrides.MEASURE.get(key)
    # a relation that the port writes by hand is a decision and
    # stands; every other one is what a run recorded
    handrel = rel is not None
    if rel is not None: rel = fmt(' '.join(rel.split()), last=1)
    # the relation that HOL4's Termination gives is for the whole
    # definition, whether its clauses are a quotation each or one
    # quotation together
    termnote = ''
    if rel is None and b.extra:
      wf, rest = wf_relation(b.extra)
      if wf is not None:
        rel = fmt(self.term(wf), last=1)
        termnote = '' if not rest.split() else \
                   self.at(b, 'the tactic that proves the'
                              ' termination', 'Termination') + '\n'


    # the size function of a datatype that the definition itself
    # uses has to be there as well (closSem's exp_alt_size adds the
    # size of the op of closLang)
    sizes = self.size_prelude((rel or '') + ' ' +
                              (term if term else clauses))
    # where the source gives a termination its text is kept, as
    # it is for a relation that the port takes from it
    relnote = ('(* the termination relation is not in the HOL4 '
               'source *)\n')
    if rel is not None and b.extra and b.extra.strip():
      relnote = ('(* the termination relation that HOL4 gives, with\n'
                 '   the names that the port gives the constants *)\n')
    # the first pass assumes the termination of this one: the
    # port writes CHEAT_TAC where HOL4 has its tactic, and the
    # definition is made all the same
    cheat = (self.thy, name) in CHEATS
    # the tactic that proves the termination condition, written by
    # hand (phase three: overrides.TERMINATION).  It goes where
    # the CHEAT_TAC of the first pass goes, and the definition is
    # then made for real -- the next run says so, because the
    # cheat list comes out of ml/CHEATS.md, which a run writes
    tac = overrides.TERMINATION.get((self.thy, name))
    if tac: cheat = True
    tactext = tac or 'CHEAT_TAC'
    cheatnote = ('(* the first pass assumes the termination:\n'
                 '   replacing the CHEAT_TAC is all that is left *)\n'
                 if cheat and not tac else '')
    # why the clauses stand in several quotations
    splitnote = ''
    if term is None and getattr(self, 'clause_list', False) \
       and getattr(self, 'clause_split', None) \
       and getattr(self, 'clause_why', None):
      n = len(self.clause_split or [])
      splitnote = '\n'.join(fill(
        '(* the clauses in %s quotations:'
        % ('two' if n == 2 else 'three' if n == 3 else str(n)),
        ('; '.join(self.clause_why) +
         ', which one quotation cannot typecheck *)').split())) + '\n'
    # why the clauses of one function of a family are a match
    matchnote = (overrides.MATCH_CLAUSES[key][1].strip() + '\n'
                 if key in overrides.MATCH_CLAUSES else '')
    # the pointer at HOL4's Termination tactic belongs in the file
    # whatever way the definition is made: the port does not write
    # the tactic, so the file says where it stands
    if b.extra and b.extra.strip() and not termnote:
      if wf_relation(b.extra)[1].split():
        termnote = self.at(b, 'the tactic that proves the'
                              ' termination', 'Termination') + '\n'
    # ---- the way the definition is made ---------------------------
    # The file says the way, and nothing is searched for while it
    # loads.  Which way each definition needed is harvested from a
    # run (tools/strategies.py); where no run has seen one yet its
    # shape says what to write, and the next run says whether that
    # was right.  overrides.WAY has the ones the harvest gets
    # wrong -- a relation it found holds in the session of a run,
    # where every theory's names are in scope, and a file has only
    # its own.
    portname = lambda c: self.ctx.names.get((self.thy, c), c)
    names = set(map(portname, self.ctx.defining))
    way = None
    for c in sorted(self.ctx.defining):
      for k in ((self.thy, portname(c)), (self.thy, c)):
        if k in overrides.WAY: way = overrides.WAY[k]
        elif k in strategies.WAY: way = strategies.WAY[k]
      if way: break
    strat, assumed_term, found_rel = way if way else ('', False, '')
    # Whether the port could make the definition at all is what
    # ml/CHEATS.md says, and not what the harvest says: the
    # strategy recorded for a definition that nothing made is
    # whatever the last attempt left behind, so it means nothing.
    # A reason that starts with "termination" is the other kind,
    # where the definition is made and only its condition assumed.
    why = next((ASSUMED[nm] for nm in sorted(names)
                if nm in ASSUMED), None)
    # a definition that nothing made is what the harvest says by
    # having no strategy for it, which is what the give-up path
    # of the old chain leaves behind.  ml/CHEATS.md says so too,
    # but it calls the reason "termination (CHEAT_TAC)" where the
    # cheat tactic was offered and the chain failed all the same,
    # which reads like the other kind.
    assumed = (way is not None and strat == '') or \
              (why is not None and not why.startswith('termination'))
    if assumed:
      strat, found_rel, assumed_term = '', '', False
    elif why is not None:
      cheat = True
    why = why or 'the port cannot make this definition'
    # and a run says whether the termination really was assumed,
    # which is more than ml/CHEATS.md says: a definition is in
    # there when the run needed a cheat somewhere, and the cheat
    # may have been for something else
    if way is not None and not tac and not assumed:
      cheat = assumed_term
    # the clauses, as the one quotation that every way takes
    body = (clauses if term is None
            else '`%s`' % fmt(rawterm, last=4))
    head = head_way(strat)
    if assumed: recursive = recursive_text(body, names)
    elif head in NOT_RECURSIVE: recursive = False
    elif head in RECURSIVE: recursive = True
    else: recursive = recursive_text(body, names)
    # the induction theorem that a recursive definition gives, under
    # the name HOL4 gives it (foo_def comes with foo_ind)
    indbind = (bind[:-4] if bind.endswith('_def') else bind) + '_ind'
    # the relation that the file writes is the one a run used,
    # because that is the one that is known to work.  HOL4's
    # Termination gives one too and the port translates it, but
    # the two are not always the same: HOL4's machinery is not
    # HOL Light's and the relation it wants may be of no use
    # here.  A relation that does not work makes the definition
    # fail over it whether its conditions are proved or assumed,
    # so where the two differ the source's stays in the comment
    # above and the one that works is written down.  Where a run
    # recorded none the file says none, and the way lets HOL
    # Light's own machinery find one.
    hol4rel = rel
    if recursive and (found_rel or not handrel):
      # a relation the port writes by hand stands where a run
      # recorded none; where a run recorded one, that is the
      # record of what worked and it wins, and an override that
      # says otherwise has gone stale and is reported
      if handrel and found_rel and \
         ' '.join(fmt(found_rel, last=1).split()) != \
         ' '.join(rel.split()):
        self.warn.append('a MEASURE override that a run does not '
                         'bear out: ' + name)
      rel = fmt(found_rel, last=1) if found_rel else None
      # a measure that uses the size function of a datatype needs
      # it to be there, and this relation was not there when the
      # prelude was made
      sizes = self.size_prelude((rel or '') + ' ' +
                                (term if term else clauses))
      def inset(r):
        return '\n'.join('     ' + l for l in r.split('\n')).lstrip()
      if rel is not None and hol4rel is None:
        relnote = ('(* the termination relation is not in the HOL4 '
                   'source; this one is\n   what the port found for '
                   'it *)\n')
      elif hol4rel is not None and rel is not None and \
           ' '.join(rel.split()) != ' '.join(hol4rel.split()):
        relnote = ('(* the termination relation that HOL4 gives is\n'
                   '     %s\n   which is not one that HOL Light '
                   'takes here; the one\n   below is what the port '
                   'found for it *)\n' % inset(hol4rel))
      elif hol4rel is not None and rel is None:
        relnote = ('(* the termination relation that HOL4 gives is\n'
                   '     %s\n   which is not one that HOL Light '
                   'takes here, so the\n   port lets its own '
                   'machinery find one *)\n' % inset(hol4rel))
    binding = '%s,%s' % (bind, indbind) if recursive else bind
    # what a term that HOL4 evaluates unfolds to: a recursive
    # definition is not one to unfold, because rewriting with it
    # does not stop
    if not recursive:
      for c in dbmod.definition_names(b.body):
        DEF_BODY[c] = (bind, b.body)
    # the induction theorem is bound only where the definition is
    # recursive, so a block that names it finds it only then
    if recursive and b.name.endswith('_def'):
      dbmod.bind_thm(self.db, self.thy, b.name[:-4] + '_ind', indbind)
    # a comment of the source that cannot stand in the quotation
    sizes += getattr(self, 'clause_pre', '') or ''
    sizes += splitnote
    self.clause_pre = ''
    # where the clauses are separate quotations, the way that makes
    # the definition is the one whose name ends in _clauses
    listed = term is None and getattr(self, 'clause_list', False)
    def way(how):
      return how + '_clauses' if listed else how
    if assumed:
      how = 'assume_definition_rec' if recursive \
            else 'assume_definition'
      text = sizes + matchnote + letline(binding, way(how),
                                         '"%s"\n  %s' % (why, body))
    elif not recursive:
      if head in SHAPES:
        text = sizes + matchnote + letline(
                 bind, way('define_shaped'),
                 '"%s"\n  %s' % (strat, body))
      elif head in ('define_single', 'general'):
        text = sizes + matchnote + letline(
                   bind, way('define_general%s'
                             % ('_cheat' if cheat else '')), body)
      elif term is not None and key not in overrides.ONE_QUOTATION \
           and strat != 'new_recursive_definition':
        text = sizes + 'let %s = new_definition\n  `%s`;;' % (bind,
                                                              term)
      else:
        text = sizes + matchnote + letline(bind, way('define_cases'),
                                           body)
    else:
      # {one function, a family} x {a rewriting of the clauses or
      # none} x {a relation, the measure of the arguments matched
      # on, HOL Light's own guess} x {proved, assumed, a tactic}
      shape = strat if head in SHAPES else ''
      # the harvest says the way, and the presence of a relation
      # does not: a definition that the recursion theorem of its
      # type makes needs none even where HOL4's Termination gives
      # one, and asking for a relation there is asking for the
      # slow way round that the recursion theorem is the way out
      # of.  Where the termination was assumed the relation of the
      # source is written down all the same, so that phase three
      # has only to put its tactic in the place of the cheat.
      if not found_rel and not ((cheat or tac) and rel is not None):
        rel = None
      if shape: kind = '_wf' if rel is not None else '_rec'
      elif head == 'prim_rec': kind, rel = '_rec', None
      elif rel is not None: kind = '_wf'
      else: kind = '_guess'
      # a definition by the recursion theorem of its type leaves
      # no condition, so there is nothing there to assume; where
      # it is a rewriting of the clauses, the tactic is still the
      # one the induction theorem needs
      if not shape and kind == '_rec': suffix = ''
      elif kind == '_guess': suffix = '_cheat' if cheat else ''
      else: suffix = '_tac' if tac else ('_cheat' if cheat else '')
      # a definition of several functions that recurse through
      # one another is made the way one of them is: the clauses
      # say which it is, and a name that only said `mutual' said
      # nothing the clauses do not
      how = way('define' + ('_shaped' if shape else '') +
                kind + suffix)
      args = ('"%s"\n  ' % shape) if shape else ''
      if rel is not None: args += '`%s`\n  ' % rel
      if suffix == '_tac': args += tactext + '\n  '
      text = (sizes + (relnote if rel is not None or
                       hol4rel is not None else '') +
              termnote + (cheatnote if cheat and not tac else '') +
              matchnote + letline(binding, how, args + body))
    # the definition is followed by the overloads of HOL4, where the
    # name it gives a constant is one that other theories use too
    overloads = self.overloads_of(sorted(self.ctx.defining))
    # the constants this block defines, under the binding of the
    # block, for tools/bindrefs.py; the names are the ones the
    # block has already computed, so that recording them cannot
    # change what the block ports
    for c in sorted(self.ctx.defining):
      EMITTED_DEFS.append((self.thy,
                           self.ctx.names.get((self.thy, c), c),
                           bind))
    # a spot of a definition that no rule can resolve: the second
    # component of the result of bvl_handle's compile is a
    # db_var_set and the first a list of bvl expressions, and
    # bvl's Var and db_vars' Var both take one argument, so
    # nothing but the place says which is which.  A patch that
    # does not apply is an error and not a silence
    if os.environ.get('PATCHDBG') and key in overrides.DEF_PATCH:
      print('PATCHDBG', text[:900], file=sys.stderr)
    text = patch_text(text, overrides.DEF_PATCH.get(key, []))
    text = file_patch(self.thy, text, self.filepatched)
    # HOL4's [simp] on a definition says that its equations belong
    # to the set that its simplifier reaches for, which the port
    # says with a call after the definition, as it does for a
    # theorem (tactics/simpset.ml)
    if 'simp' in (b.attrs or []):
      text += '\nadd_simp %s;;' % bind
    self.out.append(text if not overloads else
                    text + '\n' + '\n'.join(overloads))
    # a definition that the port writes by hand and that goes
    # where the source has the one that HOL4 makes with ML code
    # (unifDef's unify, which HOL4 makes with new_specification
    # out of a theorem about the tail recursive tunify)
    extra = overrides.EXTRA_AFTER.get((self.thy, key[1]))
    if extra and self.extra_wanted(extra):
      self.out.append('\n' + extra.strip())
    for nm in conof:
      if '*' in overrides.CON_OF.get(key, {}): continue
      was, ovl = self.conof_was.get(nm, (None, True))
      if ovl: self.ctx.overloaded.add(nm)
      if was is None: self.ctx.names.pop((self.thy, nm), None)
      else: self.ctx.names[(self.thy, nm)] = was
    for k, old2 in self.defnames_was.items():
      if old2 is None: self.ctx.names.pop(k, None)
      else: self.ctx.names[k] = old2
    self.ctx.overloaded |= self.defnames_ovl
    self.defnames_was = {}
    self.defnames_ovl = set()
    self.conof = {}
    self.conbody = {}
    if self.ctx.fieldvar is not self.fieldvar:
      self.ctx.overloads = self.ovl_was
    self.ctx.fieldvar = self.fieldvar
    self.ctx.intnums = False
    self.ctx.append = False
    self.ctx.wordnot = False
    self.ctx.intneg = False
    self.ctx.defining = set()

  def arm_intvars(self, e):
    """the variables of a match arm that hold an integer: an arm
       binds its own, and one arm can have an integer where
       another has a natural number (closSem's do_app matches on
       [Number i] and on (MemOp (ElemAt i)))"""
    def go(x):
      if not isinstance(x, hterm.Node): return
      if x.kind == 'case':
        for p, b in x.arms:
          vs = self.int_vars_node(p)
          if vs: self.ctx.armvars[id(b)] = vs
      for k, v in list(x.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): go(v)
        elif isinstance(v, (list, tuple)):
          for y in v:
            if isinstance(y, hterm.Node): go(y)
            elif isinstance(y, (list, tuple)):
              for z in y:
                if isinstance(z, hterm.Node): go(z)
    go(e)
    return e

  def lambda_cons(self, e):
    """a HOL4 overload whose name is a constructor as well and
       whose value is a lambda is ambiguous, and HOL4 resolves it
       by the type: stack_to_lab overloads Asm with
       \\a. Asm (Asmi a), and writes Asm (ShareMem op r ad), whose
       argument is an asm_or_cbw already.  Where the argument has
       the type that the constructor itself takes, the occurrence
       is the constructor, so the port writes it out"""
    def go(x):
      if not isinstance(x, hterm.Node): return
      if x.kind == 'app':
        h, args = hterm.strip_app(x)
        if (h.kind == 'id' and args and '$' not in h.name
            and h.name in self.ctx.overloads
            and h.name in self.ctx.cons):
          txt = self.ctx.overloads[h.name].strip()
          if txt.startswith('\\'):
            want = self.ctx.con_argty.get((h.name, 0)) or ''
            a = args[0]
            while a.kind in ('paren', 'typed'): a = a.e
            ah = hterm.strip_app(a)[0] if a.kind == 'app' else a
            if ah.kind == 'id' and iscon(ah.name):
              nm = ah.name.split('$')[-1]
              t2 = self.con_thy(ah.name)
              base = [ty for (t3, ty), (cs, _)
                      in self.db.datatypes.items()
                      if t3 == t2 and nm in cs]
              try:
                w = hterm.parse_type_text(want)
                w = w[1].split('$')[-1] if w[0] == 'op' else None
              except Exception:
                w = None
              if base and w == base[0]:
                t = self.con_thy(h.name)
                if t: h.name = dbg('lambda_cons', h.name,
                                   t + '$' + h.name)
      for k, v in list(x.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): go(v)
        elif isinstance(v, (list, tuple)):
          for y in v:
            if isinstance(y, hterm.Node): go(y)
            elif isinstance(y, (list, tuple)):
              for z in y:
                if isinstance(z, hterm.Node): go(z)
    go(e)
    return e

  def arm_thys(self, names):
    """the theories that have every one of these constructors,
       which is what the patterns of a match say about its
       scrutinee (tools/hterm.py prints the arms with it)"""
    ts = None
    for n in names:
      s = {t for t, k in self.db.defs.get(n, []) if k == 'con'}
      if not s: continue
      ts = s if ts is None else ts & s
    return ts or set()

  def con_thy(self, nm, kinds=('con',), arity=None):
    """the theory whose constant of this name is meant.  Where the
       name is ambiguous it is the theory whose constructor takes
       the arguments that are there, and of those the one that
       comes last among the ones in scope, which is the one HOL4's
       overload resolution takes"""
    t, n = nm.split('$') if '$' in nm else (None, nm)
    # with CONDBG=<name> the two overrides that decide before
    # anything else say what they have, which is how an entry
    # that went into the wrong table is found
    if os.environ.get('CONDBG') == n:
      print('CONDBG0 %s %s con_of=%s con_file=%s' %
            (self.thy, nm, self.conof_said.get(n),
             self.con_file.get(n)), file=sys.stderr)
    if n in self.conof_said: return self.conof_said[n]
    # a name that the source qualifies says its theory itself,
    # which is the strongest thing there is and beats the
    # file-wide override: data_to_word_gcProof means wordSem's
    # dec_clock everywhere but in the one theorem that writes
    # dataSem$dec_clock and wordSem$dec_clock side by side
    # (PORTING-GUIDE.md entry 118 puts it first too)
    if t: return t
    # a name that means one theory's constant everywhere in this
    # file (overrides.CON_FILE)
    if n in self.con_file: return self.con_file[n]
    if n in self.front_thy: return self.front_thy[n]
    anc = self.db.scope(self.thy) | {self.thy}
    ts = [x for x, k in self.db.defs.get(n, [])
          if k in kinds and x in anc]
    # the arguments that are there say more than the types that
    # the other clauses of the definition use
    if arity is not None:
      # the arity of a constructor, and of a constant that is no
      # constructor the arity that the port's own gives
      # (tools/arity.txt): sptree's insert takes three arguments
      # and balanced_map's four, and word_cse uses both
      def ar_of(x):
        a = self.db.con_arity(x, n)
        if a: return a
        nm2 = self.ctx.names.get((x, n))
        if nm2 is None and x == self.thy:
          nm2 = self.ctx.names.get(n)
        return hterm.const_arity(nm2 or n)
      ars = [ar_of(x) for x in ts]
      # and only where the arity of every candidate is known: a
      # table that has one of them and not the other would let the
      # one it has win on nothing
      if all(a is not None for a in ars):
        ts = [x for x, a in zip(ts, ars) if a == arity] or ts
    # the patterns of the match that is being printed say the
    # theory more precisely than the block does, so they come
    # first; the block narrows what is left where it can
    if kinds == ('con',) and self.ctx.armtys:
      ts = [x for x in ts if x in self.ctx.armtys] or ts
    if kinds == ('con',) and self.contys:
      narrow = [x for x in ts if x in self.contys]
      if narrow: ts = narrow
    if not ts: return None
    # a file is about a language and its name says which one:
    # CakeML calls a pass after the language it reads (bvl_const,
    # clos_annotate, word_alloc), so a constructor that several
    # theories have is that language's.  A pass that builds
    # another language says so for its bodies
    # (overrides.CON_BODY), and where the name of the file does
    # not say it the override does (overrides.MAIN_THEORY:
    # word_alloc is about wordLang)
    pref = [x for x in ts
            if x == self.thy or self.thy.startswith(x + '_')]
    if pref: ts = pref
    main = overrides.MAIN_THEORY.get(self.thy)
    if os.environ.get('CONDBG') == n:
      print('CONDBG', self.thy, n, arity, ts, main, file=sys.stderr)
    if main and len(ts) > 1 and main in ts: ts = [main]
    # a constructor of a datatype whose name several theories have
    # is the one of the type that the theory means by that name:
    # the v of data_to_word_memoryProof is dataSem's, so its
    # Number is dataSem's as well
    if kinds == ('con',) and len(ts) > 1:
      same = [t for t in ts
              if any(ty for (t2, ty), (cons, _)
                     in self.db.datatypes.items()
                     if t2 == t and n in cons and
                     self.db.rename.get((t, ty), ty) ==
                     self.ctx.tyname(ty))]
      ts = same or ts
    # of the theories that are left, the one closest to this one
    # in the ancestry (the Loc of data_to_word_gcProof is
    # wordLang's, one step away, and not semanticPrimitives',
    # three steps away), and of those the last of the order, which
    # is the one HOL4's overload resolution takes
    dist = self.db.distance(self.thy)
    near = min(dist.get(x, 99) for x in ts)
    ts = [x for x in ts if dist.get(x, 99) == near] or ts
    rank = {thy: i for i, (thy, _, _) in enumerate(self.db.order)}
    return max(ts, key=lambda x: rank.get(x, -1))

  def resolve_overload(self, nm):
    """the constant that an overloaded name means here: the
       one HOL4's own resolution would take, which con_thy
       works out.  None where this port cannot tell, and the
       name is then left as it stands"""
    try:
      # a constructor first, and only that, so that con_thy can
      # narrow by the types the block is about (its contys): with
      # the wider set that filter is off and Var of db_vars wins
      # over the Var of bvl that the clause means
      ar = self.ctx.arity
      t = self.con_thy(nm, arity=ar)
      if t is None:
        t = self.con_thy(nm, ('con', 'def', 'rel'), arity=ar)
    except Exception:
      t = None
    # the accessor of a record field, which the record block of
    # the theory that defines the record put in the map
    if nm in self.ctx.accessor_names:
      return self.ctx.accessor_names[nm]
    if not t: return None
    # the map keys a name of this theory itself without the
    # theory in front of it, as hterm.Ctx.name reads it
    r = self.ctx.names.get((t, nm))
    if r is None and t == self.thy: r = self.ctx.names.get(nm)
    if r is None:
      UNRESOLVED[self.thy][nm] = UNRESOLVED.setdefault(
        self.thy, {}).get(nm, 0) + 1
    return r

  def const_name(self, nm):
    """the name that the port gives the constant that a name of a
       CakeML source means, also where that name is overloaded"""
    n = nm.split('$')[-1]
    t = self.con_thy(nm, ('con', 'def', 'rel'))
    return self.ctx.names.get((t, n), n) if t else self.ctx.name(nm)

  def con_name(self, nm, arity=None):
    """the name that the port gives the constructor that an
       ambiguous name means; writing it out resolves the overload
       without a type annotation, which HOL Light cannot leave
       general (a type variable that the user writes is rigid)"""
    t = self.con_thy(nm, arity=arity)
    n = nm.split('$')[-1]
    return self.ctx.names.get((t, n)) if t else None

  def con_type(self, nm, arity=None):
    """the type of a constructor, as the port writes it"""
    t = self.con_thy(nm, arity=arity)
    n = nm.split('$')[-1]
    if not t: return None
    for (t2, ty), (cons, _) in self.db.datatypes.items():
      if t2 == t and n in cons:
        # the name of the type of that theory, not of whichever
        # theory in scope has a type of the same name
        nm = self.ctx.tyname(t2 + '$' + ty)
        ps = self.db.ty_params.get((t2, nm))
        return '(%s)%s' % (','.join(ps), nm) if ps else nm
    return None

  def ambiguous_con(self, nm):
    """is this the name of a constructor of more than one theory of
       the port, so that only the type says which one it is?  The
       theories need not be in scope: HOL4 resolves a name in the
       scope of the theory, HOL Light in the one namespace of the
       whole port, where the overload of a theory that is loaded
       before this one but is not an ancestor of it is in the way
       (word_simp's strip_const matches on the Const of wordLang,
       and word_depth, which is not an ancestor of it, has a Const
       of its own)"""
    if '$' in nm: return False
    return len([x for x, k in self.db.defs.get(nm, [])
                if k == 'con']) > 1

  def annotate_pat(self, p, ambiguous=False):
    """the pattern with the type of its constructor on it"""
    done = [False]
    def go(p):
      if done[0]: return p
      while p.kind == 'paren': p = p.e
      if p.kind in ('app', 'id'):
        # a constructor without arguments is a pattern of its own
        h, args0 = (hterm.strip_app(p) if p.kind == 'app'
                    else (p, []))
        if h.kind == 'id' and (h.name in self.ctx.cons or
                               '$' in h.name):
          if ambiguous and not self.ambiguous_con(h.name):
            return p
          ty = self.con_type(h.name, len(args0))
          # a type with parameters is not written in an
          # annotation (below), so it is not carried to the body
          # of the clause either
          if ty and not ty.startswith('('):
            self.annotated[hterm.Printer(self.ctx).pr(p, 0)] = ty
          # the name of the constructor says which type it is of,
          # because the port writes every constant out: an
          # annotation beside it would say it twice (and a type
          # with parameters cannot be written in one at all, as a
          # type variable that the port writes is rigid in HOL
          # Light)
          if ambiguous and ty:
            nm = self.con_name(h.name, len(args0))
            if nm:
              done[0] = True
              h.name = dbg('annotate_pat', h.name, nm)
              return p
          # a type with parameters cannot be written in an
          # annotation at all, whether the name is ambiguous or
          # not: a type variable that the port writes is rigid in
          # HOL Light, so ((ByteArray b bl):'a bvlSem_ref) says
          # that the clause gives back a ref over the same values
          # it reads, where the clauses beside it say it does not
          if ty and ty.startswith('('):
            return p
          if ty:
            done[0] = True
            return hterm.Node('paren', tok=p.tok,
                     e=hterm.Node('typed', tok=p.tok, e=p,
                                  ty=hterm.tokenize(ty)))
        return p
      if p.kind == 'list':
        p.items = [go(a) for a in p.items]
        return p
      if p.kind == 'infix' and p.op in ('::', ','):
        p.l = go(p.l); p.r = go(p.r)
        return p
      return p
    return go(p)

  def arg_types(self, cls):
    """the type that one clause of a function puts on one of its
       arguments is put on that argument of its other clauses as
       well, where they have a variable there: a clause of its
       own says nothing else about the type
       (semanticPrimitives' num_cmp says (j:num) in one clause,
       and mlstring overloads < and <= as well)"""
    aty = {}

    def collect(x):
      if not isinstance(x, hterm.Node): return
      if x.kind == 'typed':
        b = x.e
        while b.kind == 'paren': b = b.e
        if b.kind == 'id' and not iscon(b.name):
          aty.setdefault(b.name, x.ty)
      for k, v in list(x.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): collect(v)
        elif isinstance(v, (list, tuple)):
          for y in v:
            if isinstance(y, hterm.Node): collect(y)
            elif isinstance(y, (list, tuple)):
              for z in y:
                if isinstance(z, hterm.Node): collect(z)

    for cl in cls: collect(cl)
    if not aty: return
    for cl in cls:
      e = cl
      while e.kind == 'paren': e = e.e
      if not (e.kind == 'infix' and e.op in ('=', '<=>')): continue
      h, args = hterm.strip_app(e.l)
      if h.kind != 'id': continue
      e.l = h
      for i, a in enumerate(args):
        b = a
        while b.kind == 'paren': b = b.e
        if b.kind == 'id' and b.name in aty:
          a = hterm.Node('paren', tok=b.tok,
                e=hterm.Node('typed', tok=b.tok, e=b,
                             ty=aty[b.name]))
        e.l = hterm.Node('app', tok=e.l.tok, fn=e.l, arg=a)

  def result_types(self, cls):
    """the type that one clause of a function puts on its right
       hand side is put on the right hand side of its other
       clauses as well: a clause of its own says nothing else
       about the type, and an ambiguous constructor in it would
       be resolved another way (data_to_word's MemEqList gives a
       wordLang program, which only its first clause says)"""
    rty = {}
    for cl in cls:
      e = cl
      while e.kind == 'paren': e = e.e
      if not (e.kind == 'infix' and e.op in ('=', '<=>')): continue
      h, _ = hterm.strip_app(e.l)
      if h.kind != 'id': continue
      r = e.r
      while r.kind == 'paren': r = r.e
      if r.kind == 'typed': rty.setdefault(h.name, r.ty)
    if not rty: return
    for cl in cls:
      e = cl
      while e.kind == 'paren': e = e.e
      if not (e.kind == 'infix' and e.op in ('=', '<=>')): continue
      h, _ = hterm.strip_app(e.l)
      if h.kind != 'id' or h.name not in rty: continue
      r = e.r
      while r.kind == 'paren': r = r.e
      if r.kind == 'typed': continue
      e.r = hterm.Node('typed', tok=e.r.tok,
                       e=hterm.Node('paren', tok=e.r.tok, e=e.r),
                       ty=rty[h.name])

  def pat_types(self, cls):
    """the theories of the types that the source itself puts on a
       pattern, per argument position: those say which theory an
       ambiguous constructor of another clause is from
       (source_to_flat's compile_exp matches on the If of ast,
       which only the clauses with an :ast_exp on them say)"""
    out = {}

    def parts(args):
      """the arguments of a clause, and the components of the
         ones that are a tuple: a definition of a semantics takes
         the program and the state as one pair, and the type that
         says which language it is of is on the program
         (stackSem's evaluate matches on the Halt of stackLang
         and gives the Halt of stackSem)"""
      for i, a in enumerate(args):
        while a.kind == 'paren': a = a.e
        if a.kind == 'infix' and a.op == ',':
          cs = []
          b = a
          while b.kind == 'infix' and b.op == ',':
            cs.append(b.l); b = b.r
            while b.kind == 'paren': b = b.e
          cs.append(b)
          for j, c in enumerate(cs): yield (i, j), c
        else:
          yield (i,), a

    for cl in cls:
      e = cl
      while e.kind == 'paren': e = e.e
      if not (e.kind == 'infix' and e.op in ('=', '<=>')): continue
      h, args = hterm.strip_app(e.l)
      if h.kind != 'id': continue
      for i, a in parts(args):
        while a.kind == 'paren': a = a.e
        if a.kind != 'typed': continue
        try:
          ty = hterm.parse_type_text(
                 ' '.join(t.text for t in a.ty))
        except Exception:
          continue
        if ty[0] != 'op': continue
        nm = ty[1].split('$')[-1]
        ts = {t for (t, ty2) in self.db.datatypes if ty2 == nm}
        if ts: out[(h.name, i)] = ts | out.get((h.name, i), set())
    # and the theories that can provide the constructor that
    # every clause has at that position: with those, an
    # ambiguous name is the one that fits the whole definition
    poss = {}
    for cl in cls:
      e = cl
      while e.kind == 'paren': e = e.e
      if not (e.kind == 'infix' and e.op in ('=', '<=>')): continue
      h, args = hterm.strip_app(e.l)
      if h.kind != 'id': continue
      for i, a in parts(args):
        while a.kind in ('paren', 'typed'): a = a.e
        c, _ = hterm.strip_app(a) if a.kind == 'app' else (a, [])
        if c.kind != 'id' or not iscon(c.name): continue
        nm = c.name.split('$')[-1]
        ts = ({c.name.split('$')[0]} if '$' in c.name else
              {t for t, k in self.db.defs.get(nm, []) if k == 'con'})
        key = (h.name, i)
        poss[key] = ts if key not in poss else (poss[key] & ts)
    for k, v in poss.items():
      if v: out.setdefault(k, v)
    return out

  def annotate(self, cl, ambiguous=False, atys=None):
    """the type of the pattern of a clause that is a quotation of
       its own: without it the clause can typecheck differently
       from the others (the name of a constructor is ambiguous)"""
    e = cl
    while e.kind == 'paren': e = e.e
    if not (e.kind == 'infix' and e.op in ('=', '<=>')): return cl
    head, args = hterm.strip_app(e.l)
    e.l = hterm.strip_app(e.l)[0]
    self.annotated = {}
    # the constant that the clause is about says which language
    # the constructors of its arguments belong to: the evaluate of
    # an equation about wordSem takes a prog of wordLang, and not
    # the Seq of reg_alloc's clash_tree, which comes later in the
    # order
    hthy = (self.con_thy(head.name, ('con', 'def', 'rel'))
            if head.kind == 'id' else None)
    base = self.contys or (self.db.ancestors(hthy) if hthy else None)
    for i, a in enumerate(args):
      # an argument that is a tuple has a type of its own per
      # component (a semantics takes the program and the state
      # as one pair, and only the program says which language
      # the clause is about)
      b = a
      while b.kind == 'paren': b = b.e
      if b.kind == 'infix' and b.op == ',':
        cs = []
        while b.kind == 'infix' and b.op == ',':
          cs.append(b.l); b = b.r
          while b.kind == 'paren': b = b.e
        cs.append(b)
        out = []
        hname = head.name if head.kind == 'id' else None
        for j, c in enumerate(cs):
          self.contys = ((atys or {}).get((hname, (i, j)))
                         if hname else None) or base
          out.append(self.annotate_pat(c, ambiguous))
          self.contys = base
        a = out[-1]
        for c in reversed(out[:-1]):
          a = hterm.Node('infix', tok=c.tok, op=',', l=c, r=a)
      else:
        if atys and head.kind == 'id':
          self.contys = atys.get((head.name, (i,))) or base
        a = self.annotate_pat(a, ambiguous)
        self.contys = base
      # an argument that holds an integer, where no clause says so
      b = a
      while b.kind == 'paren': b = b.e
      if b.kind == 'id' and b.name in self.intargs:
        a = hterm.Node('paren', tok=b.tok,
              e=hterm.Node('typed', tok=b.tok, e=b,
                           ty=hterm.tokenize('int')))
      # an argument whose type an override gives, because the
      # definition says it nowhere (stack_removeProof's state_rel
      # compares two states of stackSem, and the accessors that
      # it uses are overloaded)
      elif b.kind == 'id' and b.name in self.argtypes:
        a = hterm.Node('paren', tok=b.tok,
              e=hterm.Node('typed', tok=b.tok, e=b,
                   ty=hterm.tokenize(self.argtypes[b.name])))
      e.l = hterm.Node('app', tok=e.l.tok, fn=e.l, arg=a)
    # a constructor of the pattern that the right hand side uses
    # again gets the same resolution there: a clause of its own is
    # typechecked on its own, so nothing else would say which
    # constructor it is (bvl_inline's Force is bvl's, not db_vars')
    if ambiguous and self.annotated:
      e.r = self.annotate_again(e.r)
    # the result of the clause is an integer, where no clause of
    # the definition says so
    r = e.r
    while r.kind == 'paren': r = r.e
    if self.intresult and r.kind != 'typed':
      inner = (e.r if e.r.kind in ('paren', 'num', 'id')
               else hterm.Node('paren', tok=e.r.tok, e=e.r))
      e.r = hterm.Node('typed', tok=e.r.tok, e=inner,
              ty=hterm.tokenize('int'))
    return cl

  def annotate_again(self, e):
    """a term that the pattern of the clause resolved, resolved the
       same way where the body has it again.  Only the very same
       term: a compiler pass uses the name of a constructor of its
       source language in the pattern and the one of its target
       language in the body (bvi_to_data's If)"""
    pr = hterm.Printer(self.ctx)
    # a term that the body has twice may mean two things there
    # (bvl_handle's 'compile_sing l n (Var v) = (Var v,Var v,1,T)'
    # has bvl's Var and db_vars' Var in the body), so only a term
    # that the body has once carries the resolution over
    seen = {}

    def count(e):
      if not isinstance(e, hterm.Node): return
      # a term that the source itself annotates needs nothing
      if e.kind == 'typed': return
      if e.kind in ('app', 'id'):
        s = pr.pr(e, 0)
        if s in self.annotated: seen[s] = seen.get(s, 0) + 1
      for k, v in list(e.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): count(v)
        elif isinstance(v, (tuple, list)):
          for x in v:
            if isinstance(x, hterm.Node): count(x)
            elif isinstance(x, (tuple, list)):
              for y in x:
                if isinstance(y, hterm.Node): count(y)
    count(e)

    def resolved(h, i, n):
      """is the ith argument of this constructor of a type that
         says what the argument is?  Then it needs no annotation
         (data_to_word's lookup_word_op gives back Bitwise Xor,
         whose Xor is the one of asm).  A type variable says
         nothing (the k of wordSem's SOME (Break k))"""
      if h.kind != 'id' or h.name in self.ctx.defining: return False
      if not iscon(h.name): return False
      nm = h.name.split('$')[-1]
      t = self.con_thy(h.name, arity=n)
      ty = (self.db.con_argty_thy.get((t, nm, i)) if t else None) or \
           self.ctx.con_argty.get((nm, i))
      if not ty: return False
      try:
        t = hterm.parse_type_text(ty)
      except Exception:
        return False
      return t[0] == 'op'

    def go(e, top=True):
      if not isinstance(e, hterm.Node): return e
      if e.kind == 'typed': return e
      # parentheses do not make an argument a term of its own
      if e.kind == 'paren':
        e.e = go(e.e, top)
        return e
      if e.kind in ('app', 'id') and top:
        s = pr.pr(e, 0)
        ty = self.annotated.get(s) if seen.get(s) == 1 else None
        # where CON_OF says the body means a constructor of
        # another theory, the type of the pattern is not the one
        # of the body (word_to_stackProof's compile_result gives
        # back the result of stackSem)
        h = hterm.strip_app(e)[0] if e.kind == 'app' else e
        if (h.kind == 'id' and
            (h.name.split('$')[-1] in self.conof or
             h.name.split('$')[-1] in self.conbody)): ty = None
        if ty:
          return hterm.Node('paren', tok=e.tok,
                   e=hterm.Node('typed', tok=e.tok, e=e,
                                ty=hterm.tokenize(ty)))
      if e.kind == 'app':
        h, args = hterm.strip_app(e)
        if h.kind == 'id' and iscon(h.name):
          for i, a in enumerate(args):
            go(a, not resolved(h, i, len(args)))
          return e
      for k, v in list(e.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): setattr(e, k, go(v))
        elif isinstance(v, list):
          setattr(e, k, [go(x) if isinstance(x, hterm.Node)
                         else ([go(y) if isinstance(y, hterm.Node)
                                else y for y in x]
                               if isinstance(x, (list, tuple)) else x)
                         for x in v])
      return e
    return go(e)

  def int_vars(self, body):
    """the variables of a definition that hold an integer: the ones
       that are the argument of a constructor whose type there is
       int, as i is in clos_known's [Tuple _ xs; Int i]"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
    except Exception:
      return set()
    return self.int_vars_node(e)

  def int_annotated(self, body):
    """the variables that the source annotates with int somewhere
       in the definition: the clauses are typechecked on their own,
       so the ones that do not say it have to say it too
       (semanticPrimitives' int_cmp says it in one clause only)"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      hterm.Parser(toks, self.ctx).parse()
    except Exception:
      return set()
    out = set()
    for i, tk in enumerate(toks):
      # an id with int on it, where the id is not the argument of
      # an application (there the annotation is of the whole)
      if not (tk.kind == 'sym' and tk.text == ':' and i >= 2
              and toks[i-1].kind == 'id'
              and i + 1 < len(toks) and toks[i+1].kind == 'id'
              and toks[i+1].text == 'int'):
        continue
      before = toks[i-2]
      if before.kind in ('id', 'num') or before.text in (')', ']'):
        continue
      # the type has to be int and nothing more: in (P:int -> bool)
      # the variable is a predicate, not an integer
      after = toks[i+2] if i + 2 < len(toks) else None
      if after is None or after.kind != 'sym' or \
         after.text not in (')', ',', ']', ';'):
        continue
      out.add(toks[i-1].text)
    return out

  def int_vars_node(self, e):
    """the same of a term that is already parsed (the clauses of a
       definition in list form are typechecked on their own, so
       each of them has its own variables)"""
    out = set(); other = set()

    def arith_vars(n, acc):
      while n.kind == 'paren': n = n.e
      if n.kind == 'id': acc.add(n.name)
      elif n.kind == 'infix' and n.op in hterm.ARITH:
        arith_vars(n.l, acc); arith_vars(n.r, acc)
      elif n.kind == 'prefix' and n.op in ('-', '~'):
        arith_vars(n.e, acc)

    def go(n):
      if n is None or not isinstance(n, hterm.Node): return
      if n.kind == 'app':
        h, args = hterm.strip_app(n)
        if h.kind == 'id':
          # the type of the argument of the constructor that this
          # name means here; the name may be one that several
          # theories have (closSem's do_app matches on the Number
          # of closSem, whose argument is an integer)
          nm = h.name.split('$')[-1]
          t = self.con_thy(h.name, arity=len(args)) \
              if iscon(h.name) else None
          for i, a in enumerate(args):
            while a.kind == 'paren': a = a.e
            if a.kind != 'id': continue
            ty = (self.db.con_argty_thy.get((t, nm, i)) if t else
                  None) or self.ctx.con_argty.get((nm, i))
            if ty in ('int', 'real'): out.add(a.name)
            elif ty: other.add(a.name)
        # the argument of a function whose argument is an integer
        # (HOL4's Num) holds one, and so do the variables that a
        # sum or a product of it is made of
        if h.kind == 'id' and h.name in hterm.INT_FUNS:
          for a in args: arith_vars(a, out)

      for k, v in list(n.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): go(v)
        elif isinstance(v, (tuple, list)):
          for x in v:
            if isinstance(x, hterm.Node): go(x)
            elif isinstance(x, (tuple, list)):
              for y in x:
                if isinstance(y, hterm.Node): go(y)
    go(e)
    # a name that is the argument of a constructor whose type there
    # is not an integer as well says nothing
    return out - other

  def hl_pick(self, nm):
    """the theory whose constructor of this name HOL Light takes
       where the type does not say: the overload that was
       declared last, which is the one of the theory that comes
       last in the whole port"""
    ts = [t for t, k in self.db.defs.get(nm.split('$')[-1], [])
          if k == 'con']
    if not ts: return None
    rank = {t: i for i, (t, _, _) in enumerate(self.db.order)}
    return max(ts, key=lambda x: rank.get(x, -1))

  def ty_thy(self, text):
    """the theory of a type that a constructor argument has, from
       the text that the HOL4 source gives it"""
    try:
      ty = hterm.parse_type_text(text)
    except Exception:
      return None
    if ty[0] != 'op': return None
    nm = ty[1]
    if '$' in nm: return nm.split('$')[0]
    anc = self.db.scope(self.thy) | {self.thy}
    ts = [t for (t, ty2) in self.db.datatypes
          if ty2 == nm and t in anc]
    if not ts: return None
    rank = {t: i for i, (t, _, _) in enumerate(self.db.order)}
    return max(ts, key=lambda x: rank.get(x, -1))

  def arg_cons(self, e):
    """an ambiguous constructor that is the argument of another
       constructor whose argument type says which theory it is of
       (the Word64 in flat_to_closProof's Litv (Word64 w) is the
       one of ast, because the argument of Litv is an ast$lit)"""
    def go(x):
      if not isinstance(x, hterm.Node): return
      if x.kind == 'app':
        h, args = hterm.strip_app(x)
        if h.kind == 'id' and iscon(h.name):
          nm = h.name.split('$')[-1]
          # the theories whose constructor of that name the
          # occurrence can be: the type of the argument only says
          # something where they all give it the same one (the
          # argument of a Litv is an ast$lit, of whichever
          # theory the Litv is; the argument of an If is of the
          # language that the If is of, so it says nothing)
          if '$' in h.name:
            cands = [h.name.split('$')[0]]
          else:
            anc = self.db.scope(self.thy) | {self.thy}
            cands = [t for t, k in self.db.defs.get(nm, [])
                     if k == 'con' and t in anc
                     and self.db.con_arity(t, nm) == len(args)]
          def argthy(t, i):
            """the theory of the type of the ith argument of the
               constructor of theory t: a type name that is not
               qualified and that t has a datatype for is t's own
               (the exp of bvl's Let is bvl's, of bvi's Let
               bvi's)"""
            ty = self.db.con_argty_thy.get((t, nm, i))
            if not ty: return None
            try:
              p2 = hterm.parse_type_text(ty)
            except Exception:
              return None
            if (p2[0] == 'op' and '$' not in p2[1] and
                (t, p2[1]) in self.db.datatypes):
              return t
            return self.ty_thy(ty)

          for i, a in enumerate(args):
            tys = {argthy(t, i) for t in cands
                   if (t, nm, i) in self.db.con_argty_thy}
            tys.discard(None)
            if not cands:
              ty = self.ctx.con_argty.get((nm, i))
              tys = {self.ty_thy(ty)} if ty else set()
            t2 = tys.pop() if len(tys) == 1 else None
            if not t2: continue
            b = a
            while b.kind == 'paren': b = b.e
            bh, bargs = (hterm.strip_app(b) if b.kind == 'app'
                         else (b, []))
            if (bh.kind == 'id' and '$' not in bh.name
                and iscon(bh.name) and self.ambiguous_con(bh.name)
                and (t2, bh.name) in
                    [(t3, c) for (t3, _), (cs, _)
                     in self.db.datatypes.items() for c in cs]
                and self.db.con_arity(t2, bh.name) == len(bargs)
                and self.hl_pick(bh.name) != t2):
              bh.name = dbg('arg_cons[%s %d]' % (nm, i), bh.name,
                            t2 + '$' + bh.name)
        for a in args: go(a)
        return
      for k, v in list(x.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): go(v)
        elif isinstance(v, (tuple, list)):
          for y in v:
            if isinstance(y, hterm.Node): go(y)
            elif isinstance(y, (tuple, list)):
              for z in y:
                if isinstance(z, hterm.Node): go(z)
    go(e)
    return e

  def conof_arity(self, e):
    if not self.conof and not self.conof_arities: return e
    """the occurrences of a name of CON_OF that the theory it
       names has no constructor of that arity for, written with
       the theory that has one (word_alloc's ssa_cc_trans means
       wordLang's Store where it builds a program and asm's,
       which takes no arguments, where it compares a memop)"""
    def go(x):
      if not isinstance(x, hterm.Node): return
      # the arity is the one of the whole application, so the
      # function of an application is not looked at on its own
      if x.kind == 'app':
        h, args = hterm.strip_app(x)
        head(h, len(args))
        for a in args: go(a)
        return
      if x.kind == 'id':
        head(x, 0)
        return
      for k, v in list(x.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): go(v)
        elif isinstance(v, (tuple, list)):
          for y in v:
            if isinstance(y, hterm.Node): go(y)
            elif isinstance(y, (tuple, list)):
              for z in y:
                if isinstance(z, hterm.Node): go(z)

    def head(h, n):
      if h.kind != 'id' or '$' in h.name: return
      if h.name in self.conof_arities:
        t = self.conof_arities[h.name].get(n)
        if t: h.name = t + '$' + h.name
        return
      if h.name not in self.conof: return
      t = self.conof[h.name]
      if self.db.con_arity(t, h.name) == n: return
      t2 = self.con_thy(h.name, arity=n)
      if t2 and t2 != t and self.db.con_arity(t2, h.name) == n:
        h.name = dbg('conof_arity', h.name, t2 + '$' + h.name)
    go(e)
    return e

  def pr_body(self, pr, e, prec=2):
    """the right hand side of a match arm, with the constructors
       that CON_OF says this definition means: the arms of a
       definition in the match form are its clauses"""
    e = self.conof_arity(e)
    if not self.conof_wild and not self.conbody: return pr.pr(e, prec)
    old = {}
    was = {}
    body = dict(self.conof) if self.conof_wild else {}
    body.update(self.conbody)
    for nm, t in body.items():
      old[nm] = nm in self.ctx.overloaded
      self.ctx.overloaded.discard(nm)
      # what the name meant before: a CON_OF of the definition
      # has set it already, and popping it would take that with it
      was[nm] = self.ctx.names.get((self.thy, nm))
      self.ctx.names[(self.thy, nm)] = self.ctx.names.get((t, nm), nm)
    try:
      return pr.pr(e, prec)
    finally:
      for nm in body:
        if old[nm]: self.ctx.overloaded.add(nm)
        if was[nm] is None: self.ctx.names.pop((self.thy, nm), None)
        else: self.ctx.names[(self.thy, nm)] = was[nm]

  def clause_names(self, cl):
    """the names that the pattern of a clause uses, which is what
       says which clause an entry of overrides.CON_CLAUSE is
       about: a constructor of the pattern names its clause, where
       a number would move with every clause added before it"""
    e = cl
    while e.kind == 'paren': e = e.e
    if not (e.kind == 'infix' and e.op in ('=', '<=>')): return set()
    out = set()
    def go(x):
      if not isinstance(x, hterm.Node): return
      if x.kind == 'id': out.add(x.name.split('$')[-1])
      for k, v in list(x.__dict__.items()):
        if k == 'tok': continue
        if isinstance(v, hterm.Node): go(v)
        elif isinstance(v, (list, tuple)):
          for y in v:
            if isinstance(y, hterm.Node): go(y)
            elif isinstance(y, (list, tuple)):
              for z in y:
                if isinstance(z, hterm.Node): go(z)
    go(e.l)
    return out

  def pr_clause(self, p, cl):
    """a clause, with the right hand side printed with the
       constructors that CON_OF says this definition means"""
    if not self.conof and not self.conbody: return p.pr(cl, 0)
    e = cl
    while e.kind == 'paren': e = e.e
    if not (e.kind == 'infix' and e.op in ('=', '<=>')):
      return p.pr(cl, 0)
    # the right hand side of the clause ends the quotation, so a
    # conditional, a let or a match there needs no brackets
    rr = e.r
    while rr.kind == 'paren': rr = rr.e
    rp = 0 if rr.kind in ('cond', 'let', 'case') else 13
    lhs = p.pr(e.l, 13)
    # an override that names the constructors itself is in the
    # scope of the whole definition already; only the ones that
    # the wildcard gives are put in for the right hand side
    if not self.conof_wild and not self.conbody:
      return '%s %s %s' % (lhs, e.op,
                           p.pr(self.conof_arity(e.r), rp))
    old = {}
    was = {}
    body = dict(self.conof) if self.conof_wild else {}
    body.update(self.conbody)
    for nm, t in body.items():
      old[nm] = nm in self.ctx.overloaded
      self.ctx.overloaded.discard(nm)
      was[nm] = self.ctx.names.get((self.thy, nm))
      self.ctx.names[(self.thy, nm)] = self.ctx.names.get((t, nm), nm)
    try:
      rhs = p.pr(self.conof_arity(e.r), rp)
    finally:
      for nm in body:
        if old[nm]: self.ctx.overloaded.add(nm)
        if was[nm] is None: self.ctx.names.pop((self.thy, nm), None)
        else: self.ctx.names[(self.thy, nm)] = was[nm]
    return '%s %s %s' % (lhs, e.op, rhs)

  def iff_to_eq(self, e):
    """the <=> of a clause that does not give a truth value is
       the = of HOL Light (HOL4 writes <=> at any type)"""
    for cl in hterm.conjuncts_of(e):
      c = cl
      while c.kind == 'paren': c = c.e
      if c.kind == 'infix' and c.op == '<=>': c.op = '='
    return e

  def clause_form(self, body, matchcons=(), split=False):
    """the clauses of a definition, as one quotation with /\\
       between them -- which is how HOL4 writes them and how HOL
       Light's own define takes them.  Where a variable of the
       definition stands in two clauses in places whose types have
       nothing in common (clause_clash), one quotation cannot
       typecheck: those clauses are separate quotations and the way
       that makes the definition is the one whose name ends in
       _clauses.  The clauses of a constant of `matchcons' are one
       quotation with a match in it, where they overlap and HOL4
       takes the first that matches (overrides.MATCH_CLAUSES)"""
    self.match_names = set()
    self.clause_list = self.clause_clash(body) or split
    # a clause of its own for each, where the override says to
    # split: what clashes there does not show in the clauses, so
    # there is nothing to group them by either
    if split: self.clause_split = None
    # the comments of the body are kept: the tokenizer gives
    # every one of them to the token after it, and the printer
    # writes it there again
    toks = hterm.tokenize(body)
    e = self.arg_cons(self.arm_intvars(
          self.lambda_cons(hterm.Parser(toks, self.ctx).parse())))
    if self.iffeq: e = self.iff_to_eq(e)
    old = self.ctx.vars
    self.ctx.vars = self.shadowing(e)
    try:
      p = hterm.Printer(self.ctx)
      # the last clause of the list ends in `];; and the others
      # in `;, which is what the lines have to leave room for
      all = hterm.conjuncts_of(e)
      atys = self.pat_types(all)
      self.result_types(all)
      self.arg_types(all)
      # the clauses of a constant that overlap are one quotation
      # with a match: the run of clauses of that constant becomes
      # one entry of the list, whose text match_form writes
      groups = []
      # which clauses of the source each entry of the list covers,
      # so that the grouping of clause_clash can be read as a
      # grouping of the entries (a match entry covers a run of
      # them)
      covers = []
      i = 0
      while i < len(all):
        h = self.clause_head(all[i])
        if h in matchcons:
          j = i
          while j + 1 < len(all) and self.clause_head(all[j + 1]) == h:
            j += 1
          was = self.ctx.vars
          try: mt = self.match_form(body, only=h)
          finally: self.ctx.vars = was
          groups.append((all[i], mt))
          covers.append(list(range(i, j + 1)))
          i = j + 1
        else:
          groups.append((all[i], None))
          covers.append([i])
          i += 1
      cls = []
      # a comment with a quote in it cannot stand in the
      # quotation, so it stands before it, as a comment of OCaml
      # (bvi_let's compile)
      qcs = {}
      for i, (cl, mt) in enumerate(groups):
        # the last line of a clause has to leave room for the
        # bracket that closes it and for the /\ after it, or for
        # the quote and the ;; that end the phrase
        last = 5 if i == len(groups) - 1 else 4
        if mt is not None:
          cls.append(fmt(mt, indent=4, last=last, extra=4))
          continue
        q = hterm.pop_quoted_comments(cl)
        if q: qcs[i] = q
        # every clause has its own variables, so also its own ones
        # that hold an integer
        self.ctx.intvars = self.int_vars_node(cl) | self.intargs
        # a constructor that this clause means another theory's
        # than the rest of the body does (bvi_to_data's LetCall
        # clause compares its y with bvi's Return, where every
        # other Return of the definition is dataLang's)
        was = self.conbody
        per = overrides.CON_CLAUSE.get(self.defkey, {})
        if per:
          pats = self.clause_names(cl)
          self.conbody = dict(was)
          self.conbody.update(
            dict((n, t) for (c, n), t in per.items() if c in pats))
        # a clause stands in brackets of its own, which end it, so
        # a conditional, a let or a match on its right needs none
        oldl = self.ctx.loose_rhs
        self.ctx.loose_rhs = hterm.lone_eqn(cl)
        try:
          cls.append(fmt(self.pr_clause(p,
                           self.annotate(cl, True, atys)),
                         indent=4, last=last, extra=4))
        finally:
          self.conbody = was
          self.ctx.loose_rhs = oldl
      # a comment that has no token of the clause to stand before
      # (one at the end of it) goes at the end of that clause
      starts = [(hterm.first_tok(cl).pos
                 if hterm.first_tok(cl) is not None else 0)
                for cl, _ in groups]
      for q, l in self.left_comments(toks, '`'.join(cls), True):
        k = max([i for i, x in enumerate(starts) if x <= q] or [0])
        cls[k] += '\n    // ' + l
    finally:
      self.ctx.vars = old
    # the clauses of a definition are one quotation with /\ between
    # them, as HOL4 writes them and as HOL Light's own define takes
    # them.  A comment with a quote in it cannot stand in a
    # quotation, so it stands before the whole phrase, as a comment
    # of OCaml (self.clause_pre, which the caller writes out)
    self.clause_pre = ''
    # the clauses of a quotation, joined with /\\; a quotation
    # that stands in a list is one column further in
    def quot(idx, ind='   '):
      out = ''
      for k, i in enumerate(idx):
        for cm in qcs.get(i, []):
          self.clause_pre += '(* ' + '\n   '.join(cm) + ' *)\n'
        # a comment runs to the end of its line, so the /\ after a
        # clause that ends in one goes on a line of its own
        if k:
          if out.split('\n')[-1].lstrip().startswith('//'):
            out += '\n' + ind + '/\\\n' + ind
          else: out += ' /\\\n' + ind
        # a comment of the source that stands before the clause
        # stands before its bracket too, or the bracket would be
        # alone at the end of a line of comment
        lines = cls[i].split('\n')
        j = 0
        while j < len(lines) and lines[j].lstrip().startswith('//'):
          out += lines[j].lstrip() + '\n' + ind
          j += 1
        # and a comment at the end of the clause stands after its
        # bracket, or the bracket would be inside the comment
        k = len(lines)
        while k > j + 1 and lines[k - 1].lstrip().startswith('//'):
          k -= 1
        rest = '\n'.join(lines[j:k])
        if j: rest = rest.lstrip()
        # a quotation of one clause needs no brackets round it
        out += rest if len(idx) == 1 else '(' + rest + ')'
        for l in lines[k:]:
          out += '\n' + ind + l.lstrip()
      return '`' + out + '`'
    if self.clause_list and self.clause_split is None:
      groups2 = [[i] for i in range(len(cls))]
    elif self.clause_list:
      # the grouping of the clauses, as a grouping of the entries:
      # an entry that covers clauses of two groups joins them
      ent = {}
      for ei, idxs in enumerate(covers):
        for i in idxs: ent[i] = ei
      pos = {}
      for gi, g in enumerate(self.clause_split):
        for i in g:
          e = ent.get(i)
          if e is None: continue
          pos.setdefault(e, []).append(gi)
      merge = {}
      def root(x):
        while merge.get(x, x) != x: x = merge[x]
        return x
      for gs in pos.values():
        for gi in gs[1:]: merge[root(gi)] = root(gs[0])
      out = {}
      for e, gs in sorted(pos.items()):
        out.setdefault(root(gs[0]), []).append(e)
      groups2 = [sorted(v) for _, v in sorted(out.items())]
    else:
      groups2 = [list(range(len(cls)))]
    if len(groups2) < 2:
      self.clause_list = False
      return quot(groups2[0])
    return ('[' + ';\n   '.join(quot(g, '    ') for g in groups2)
            + ']')

  def clause_head(self, cl):
    """the name of the constant that a clause of a definition
       defines, or None where the clause is not an equation of an
       application of a name"""
    try:
      (h, _, _), = hterm.clauses_of(cl)
    except Exception:
      return None
    return h.name if h.kind == 'id' else None

  # -- a definition as one clause with a match -------------------

  def several_clauses(self, body):
    """has this definition more than one clause?  Then the clauses
       are quotations of their own, as in HOL4, where each of them
       is typechecked separately"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
      cls = hterm.clauses_of(e)
    except Exception as ex:
      # a body this cannot read goes into one quotation
      # whatever its clauses say, which is how a clash goes
      # unseen: it is a warning and not a silence
      self.warn.append('several_clauses cannot read the body: %s'
                       % str(ex)[:60])
      return False
    global CONS
    CONS = self.ctx.cons
    self.clause_clash(body)      # sets contys for the annotations
    return len(cls) > 1

  def clause_clash(self, body):
    """does a variable of a definition occur in two clauses in
       places where its type can differ (as x does in ast's
       every_exp, where one clause has Fun x e and another one
       Let x e1 e2)?  HOL4 typechecks every clause on its own, so
       the port then writes the clauses as separate quotations"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
      cls = hterm.clauses_of(e)
    except Exception as ex:
      # a body this cannot read goes into one quotation
      # whatever its clauses say, which is how a clash goes
      # unseen: it is a warning and not a silence
      self.warn.append('clause_clash cannot read the body: %s'
                       % str(ex)[:60])
      return False
    if len(cls) < 2: return False
    global CONS
    CONS = self.ctx.cons
    # the type of a variable in a pattern is the type of the
    # argument of the constructor it sits in; the clause form is
    # only needed where those types can differ
    # the theories that can provide all the constructors of the
    # patterns: with those, the type of the argument of a
    # constructor is known even where the name is ambiguous
    cons_in = []
    def cons_of(p):
      while p.kind in ('paren', 'typed'): p = p.e
      # a constructor without arguments is a pattern of its own
      # (presLang's opw_to_display matches on the Andw of
      # backend_common, which says that the Add of the clause
      # after it is the one of backend_common too)
      if p.kind == 'id' and iscon(p.name): cons_in.append(p.name)
      if p.kind == 'app':
        h, args = hterm.strip_app(p)
        if h.kind == 'id': cons_in.append(h.name)
        for a in args: cons_of(a)
      elif p.kind == 'list':
        for a in p.items: cons_of(a)
      elif p.kind == 'infix':
        cons_of(p.l); cons_of(p.r)
    for _, args, _ in cls:
      for a in args: cons_of(a)
    # a constructor that the source qualifies (bvi$Call) says the
    # theory itself
    def split_con(nm):
      if '$' in nm:
        t, n = nm.split('$')
        return t, n
      return None, nm
    thys = None
    for nm in cons_in:
      t, n = split_con(nm)
      ts = ({t} if t else
            {t for t, k in self.db.defs.get(n, []) if k == 'con'})
      if not ts: continue
      thys = ts if thys is None else thys & ts
    self.contys = thys or set()
    def argty(nm, j, ar=None):
      t, nm = split_con(nm)
      ts = {t} if t else thys
      if ts:
        out = {self.db.con_argty_thy[(t, nm, j)] for t in ts
               if (t, nm, j) in self.db.con_argty_thy}
        if out: return out
      # where the patterns name no one theory -- an argument of a
      # pattern is a constructor of another theory, as the Addr of
      # stackSem's ShMemOp is asm's -- the theory is the one the
      # port itself resolves the name to, which is the one it
      # writes into the file.  Without this the type of the
      # argument is every type that any theory gives it, which
      # says nothing, and the clash is not seen (the dest of
      # stackSem's evaluate is a num in JumpLower and a num + num
      # in Call)
      if not t:
        try: t2 = self.con_thy(nm, arity=ar)
        except Exception: t2 = None
        if t2 and (t2, nm, j) in self.db.con_argty_thy:
          return {self.db.con_argty_thy[(t2, nm, j)]}
      return self.db.con_argty.get((nm, j))
    where = {}
    clause = [0]
    def cons_parts(p):
      """the head and the tail of a cons pattern, however the
         source writes it"""
      if p.kind == 'infix' and p.op == '::': return p.l, p.r
      if p.kind == 'app':
        h, args = hterm.strip_app(p)
        if h.kind == 'id' and h.name == 'CONS' and len(args) == 2:
          return args[0], args[1]
      return None, None

    def list_element(t):
      """the element type of a list type, as the text of the type
         says it; the hole of the port stands for any type, so a
         list of holes says nothing of its elements"""
      def unwrap(x):
        x = x.strip()
        while x.startswith('(') and x.endswith(')'):
          d, whole = 0, True
          for i, c in enumerate(x):
            if c == '(': d += 1
            elif c == ')':
              d -= 1
              if d == 0 and i != len(x) - 1: whole = False; break
          if not whole: break
          x = x[1:-1].strip()
        return x
      x = unwrap(' '.join(t.split()))
      if not x.endswith('list'): return None
      e = unwrap(x[:-4])
      return None if not e or '_' in e else e

    def tuple_parts(t):
      """the component types of a tuple type, as the text of the
         type says them: a pattern that takes a value apart binds
         its components, and their types are not the type of the
         whole"""
      s = t.strip()
      while s.startswith('(') and s.endswith(')'):
        d, whole = 0, True
        for i, c in enumerate(s):
          if c == '(': d += 1
          elif c == ')':
            d -= 1
            if d == 0 and i != len(s) - 1: whole = False; break
        if not whole: break
        s = s[1:-1].strip()
      out, d, cur = [], 0, ''
      for c in s:
        if c == '(': d += 1
        elif c == ')': d -= 1
        if c == '#' and d == 0:
          out.append(cur); cur = ''
        else:
          cur += c
      out.append(cur)
      out = [x.strip() for x in out]
      return out if len(out) > 1 and all(out) else None

    def walk(p, tys, key=None):
      while p.kind in ('paren', 'typed'): p = p.e
      # the tail of a cons pattern is a list of the same elements
      # as the whole, and an element that is a tuple says that it
      # is a list of tuples (clos_fvs's remove_fvs_let takes a
      # list of (num # exp) where its remove_fvs_sing takes a
      # list of expressions)
      hd, tl = cons_parts(p)
      if tl is not None:
        el = hd
        while el.kind in ('paren', 'typed'): el = el.e
        t = None
        if el.kind == 'infix' and el.op == ',':
          n2, v2 = 1, el
          while v2.kind == 'infix' and v2.op == ',':
            n2 += 1; v2 = v2.r
            while v2.kind in ('paren', 'typed'): v2 = v2.e
          t = '(' + '#'.join(['_'] * n2) + ')list'
        # where the list itself says nothing of its elements,
        # the tail is a list of whatever the head is: a variable
        # that another clause gives a type makes the tail a list
        # of that type (closSem's exp_alt_size has an a0 that is
        # a tra in one clause and the head of a cons in another)
        hv = hd
        while hv.kind in ('paren', 'typed'): hv = hv.e
        t1 = next(iter(tys)) if tys and len(tys) == 1 else None
        hole = (t1 is None or not isinstance(t1, str) or
                not list_element(t1))
        tt = ({('lst', hv.name)} if hv.kind == 'id' and hole
              else tys)
        walk(tl, {t} if t else tt, key)
        # the head of a cons pattern is an element of the list
        # the function is defined on, which is not the type of
        # the list and not the type of a constructor argument
        # either (closSem's exp_alt_size has an a0 that is a tra
        # in one clause and the head of a cons in another)
        el = None
        t0 = next(iter(tys)) if tys and len(tys) == 1 else None
        if isinstance(t0, str):
          ps = list_element(t0)
          if ps: el = {ps}
        walk(hd, el)
        return
      if p.kind == 'id':
        # a wildcard is a fresh variable in every clause anyway, and
        # a position whose type is not known says nothing
        if (p.name == '_' or not tys or iscon(p.name) or
            p.name.split('$')[-1] in hterm.HLCONS): return
        where.setdefault(p.name, []).append((clause[0], tys))
        return
      if p.kind == 'app':
        h, args = hterm.strip_app(p)
        nm = h.name if h.kind == 'id' else '?'
        for j, a in enumerate(args):
          walk(a, argty(nm, j, len(args)))
        return
      if p.kind == 'list':
        for a in p.items: walk(a, None)
        return
      if p.kind == 'infix':
        # a pattern that takes a value apart as a tuple binds its
        # components, whose types are not the type of the whole:
        # a clause that binds the whole and one that binds a
        # component cannot stand in one quotation
        # (cmlPtreeConversion's ptree_Decl has Nd (nt,locs) args
        # where its ptree_Structure has Nd nt args)
        if p.op == ',':
          cs, b2 = [], p
          while b2.kind == 'infix' and b2.op == ',':
            cs.append(b2.l); b2 = b2.r
            while b2.kind in ('paren', 'typed'): b2 = b2.e
          cs.append(b2)
          parts = None
          t0 = next(iter(tys)) if tys and len(tys) == 1 else None
          if isinstance(t0, str):
            ps = tuple_parts(t0)
            if ps and len(ps) == len(cs): parts = ps
          for j, c in enumerate(cs):
            walk(c, {parts[j]} if parts else None)
          return
        walk(p.l, None); walk(p.r, None)
    # the type of each argument of the function, as a pattern of
    # some clause says it: without that, a variable at argument 1
    # of one clause and at argument 2 of another would look like a
    # clash, where HOL Light unifies the two argument types
    # (mergesort's merge has 'merge R [] l' and 'merge R l []')
    def hol4_ty(nm, arity):
      """the name HOL4 gives the type of a constructor, which is
         the vocabulary that con_argty above uses"""
      t = self.con_thy(nm, arity=arity)
      n = nm.split('$')[-1]
      if not t: return None
      for (t2, ty), (cons, _) in self.db.datatypes.items():
        if t2 == t and n in cons: return ty
      return None
    def pat_ty(a):
      while a.kind in ('paren', 'typed', 'rawtyped'): a = a.e
      if a.kind == 'list': return '(_)list'
      if a.kind == 'app':
        h, args0 = hterm.strip_app(a)
        if h.kind == 'id' and iscon(h.name):
          return hol4_ty(h.name, len(args0))
      elif a.kind == 'id' and iscon(a.name):
        return hol4_ty(a.name, 0)
      return None
    # keyed by the function too: a definition of a family has one
    # argument position per member, and the argument 1 of one of
    # them has nothing to do with the argument 1 of another
    # (clos_fvs's remove_fvs_sing takes an exp list where its
    # remove_fvs_letrec takes a (num # exp) list)
    def fname(h):
      return h.name if h.kind == 'id' else '?'
    argtys = {}
    for h, args, _ in cls:
      for i, a in enumerate(args):
        t = pat_ty(a)
        if t: argtys.setdefault((fname(h), i), t)
    # an argument that no clause patterns on has no type that the
    # clauses say, so the place stands for the argument itself: a
    # variable at argument 0 of one clause and at argument 1 of
    # another is a clash, because nothing says that the two
    # arguments are of one type (balanced_map's trim_help_middle
    # has its comparison and its low bound the other way round in
    # its second clause, which is why HOL4 gets away with it)
    def tuple_ty(f):
      """the type of the elements that a function takes apart as a
         tuple, as a list of holes: FST and SND take a pair, and a
         lambda that binds a tuple takes one of its own width"""
      while f.kind == 'paren': f = f.e
      if f.kind == 'id' and f.name in ('FST', 'SND'): return '(_#_)list'
      if f.kind == 'infix' and f.op == 'o':
        return tuple_ty(f.l) or tuple_ty(f.r)
      if f.kind != 'quant' or f.q != '\\' or len(f.vs) != 1: return None
      v = f.vs[0]
      while v.kind == 'paren': v = v.e
      if not (v.kind == 'infix' and v.op == ','): return None
      n = 1
      while v.kind == 'infix' and v.op == ',':
        n += 1; v = v.r
        while v.kind == 'paren': v = v.e
      return '(' + '#'.join(['_'] * n) + ')list'
    heads = set(fname(h) for h, _, _ in cls)
    def body(n, e):
      """a body that applies one of the functions being defined
         says the type of a variable in its arguments, as a
         pattern of a clause does (clos_fvs's remove_fvs_sing has
         an xs that its remove_fvs_let takes)"""
      if not isinstance(e, hterm.Node): return
      if e.kind == 'app':
        h, args = hterm.strip_app(e)
        if h.kind == 'id' and h.name in heads:
          for i, a in enumerate(args):
            k = (h.name, i)
            walk(a, {argtys[k]} if k in argtys else {('arg',) + k})
        # a MAP over a pair says that what it maps over is a list
        # of pairs, which is what tells the clauses of a pass from
        # the ones of the helper that walks the functions of a
        # Letrec apart (clos_fvs, presLang and five others)
        if h.kind == 'id' and h.name == 'MAP' and len(args) == 2:
          t = tuple_ty(args[0])
          if t: walk(args[1], {t})
      for t in hterm.subnodes(e): body(n, t)
    for n, (h, args, r) in enumerate(cls):
      clause[0] = n
      for i, a in enumerate(args):
        k = (fname(h), i)
        walk(a, {argtys[k]} if k in argtys else {('arg',) + k}, k)
      body(n, r)
    # two clauses cannot stand in one quotation where a variable of
    # both has no type in common between them; the clauses are
    # grouped into as few quotations as that allows, which is one
    # for most definitions and two for the rest (a clause of
    # bviSem's evaluate has a dest that is a number where the
    # clause for Call has one that is an option)
    def fails(idx):
      """do these clauses force a variable to two types?  A place
         that is an argument of the function and that no clause
         patterns on is a type of its own, and two of those unify:
         the fvs that every member of a family takes is not a
         clash.  What clashes is two places whose types the
         constructors fix and that are not the same"""
      parent = {}
      def find(x):
        while parent.get(x, x) != x: x = parent[x]
        return x
      def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb: parent[ra] = rb
      # the type that the constructors of these clauses give each
      # variable, for the tail of a cons pattern: it is a list of
      # whatever the head is
      cty = {}
      for v2, es in where.items():
        cs = {next(iter(t)) for (n, t) in es
              if n in idx and len(t) == 1 and
              isinstance(next(iter(t)), str)}
        if len(cs) == 1: cty[v2] = next(iter(cs))
      def resolve(t):
        out = set()
        for x in t:
          if isinstance(x, tuple) and x[0] == 'lst':
            y = cty.get(x[1])
            if y: out.add(y + ' list')
          else:
            out.add(x)
        return out
      seen = []
      for v in where.values():
        toks = [x for x in (resolve(t) for (n, t) in v if n in idx)
                if x]
        # a place that could be one of several types says nothing
        # of its own, but two of them with none in common clash
        multi = [t for t in toks if len(t) > 1]
        if len(multi) > 1 and not set.intersection(*multi):
          return True
        ks = [next(iter(t)) for t in toks if len(t) == 1]
        for a in ks[1:]: union(ks[0], a)
        seen.extend(ks)
      byclass = {}
      for x in seen: byclass.setdefault(find(x), set()).add(x)
      for c in byclass.values():
        conc = [x for x in c if isinstance(x, str)]
        for i2 in range(len(conc)):
          for j2 in range(i2 + 1, len(conc)):
            if not hterm.ty_compatible(conc[i2], conc[j2]):
              return True
        # two arguments of one function that a variable makes one
        # type: the source means two types and gets away with it
        # because HOL4 typechecks every clause on its own
        # (balanced_map's trim_help_middle has its comparison and
        # its low bound the other way round in its second clause)
        args = [x[1:] for x in c if not isinstance(x, str)]
        if len(set(args)) > len(set(f for f, _ in args)): return True
      return False
    # the clauses of each member of the family in a quotation of
    # its own, where the override says so: what clashes there is
    # a variable of one member and of another, and the model of
    # the clash does not see it (closSem's evaluate has an args
    # that is the argument list of an App in the clauses of
    # evaluate and the value list that evaluate_app takes)
    if self.defkey in overrides.CLAUSE_BY_FUNCTION:
      byf, groups = {}, []
      for i, (h, _, _) in enumerate(cls):
        f = fname(h)
        if f not in byf:
          byf[f] = len(groups); groups.append([])
        groups[byf[f]].append(i)
      self.clause_split = groups
      return True
    groups = []
    for i in range(len(cls)):
      for g in groups:
        if not fails(g + [i]):
          g.append(i); break
      else:
        groups.append([i])
    self.clause_split = groups
    # why the clauses are in several quotations, as a comment: the
    # variables whose type is not the same in all of them
    why = []
    for k, v in sorted(where.items()):
      tys = []
      for g in groups:
        for (n, t) in v:
          if n in g and len(t) == 1:
            x = next(iter(t))
            if isinstance(x, str) and x not in tys: tys.append(x)
      if len(tys) > 1:
        def ty(t):
          t = ' '.join(t.split())
          return re.sub(r'\(\s+', '(', re.sub(r'\s+\)', ')', t))
        why.append('%s is %s and %s'
                   % (k, ', '.join(map(ty, tys[:-1])), ty(tys[-1])))
    self.clause_why = why if len(groups) > 1 else []
    # with CLASHDBG=4 a definition that did not split says so
    # too, which is what to look at when one should have
    if (len(groups) > 1 or os.environ.get('CLASHDBG') == '4') \
       and os.environ.get('CLASHDBG'):
      print('CLASH %s %s: %s' % (self.thy, self.defkey, groups),
            file=sys.stderr)
      if os.environ.get('CLASHDBG') in ('2', '3', '4'):
        for n, (h, _, _) in enumerate(cls):
          print('   %2d %s' % (n, fname(h)), file=sys.stderr)
        for k, v in where.items():
          if (os.environ.get('CLASHDBG') in ('3', '4') or
              len(set(map(str, [t for _, t in v]))) > 1):
            print('   %s: %s' % (k, v), file=sys.stderr)
    return len(groups) > 1

  def multi_pattern(self, body):
    """does a definition that is not recursive match on more than
       one argument, or with a pattern inside a constructor?  HOL
       Light's machinery for a definition by patterns is very slow
       for those, and a match is not"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      e = hterm.Parser(toks, self.ctx).parse()
      cls = hterm.clauses_of(e)
    except Exception:
      return False
    if len(cls) < 2: return False
    # the names as the port writes them, which is how they are in
    # the right hand sides below
    heads = set(self.ctx.name(h.name) for h, _, _ in cls
                if h.kind == 'id')
    # a match is one clause, so it cannot define a family
    if len(heads) > 1: return False
    # a recursive definition keeps its clauses: the termination
    # machinery does not look inside a match
    for _, _, r in cls:
      if any(nm in heads
             for nm in re.findall(r"[A-Za-z][A-Za-z0-9_']*",
                                  hterm.Printer(self.ctx).pr(r, 0))):
        return False
    global CONS
    CONS = self.ctx.cons
    pats = [args for _, args, _ in cls]
    n = min(len(a) for a in pats)
    posns = 0
    for i in range(n):
      if any(not is_var_pat(a[i]) for a in pats): posns += 1
      if any(nested_pat(a[i]) for a in pats): return True
    return posns >= 2

  def overlapping(self, body):
    """do the clauses of a definition overlap, so that they rely on
       HOL4's first match semantics?"""
    try:
      toks = hterm.tokenize(hol4.strip_comments(body))
      cls = hterm.clauses_of(hterm.Parser(toks, self.ctx).parse())
    except Exception:
      return False
    # a match is one clause, so it cannot define a family
    if len({h.name for h, _, _ in cls if h.kind == 'id'}) > 1:
      return False
    global CONS
    CONS = self.ctx.cons
    if len(cls) < 2: return False
    pats = [args for _, args, _ in cls]
    if any(len(a) != len(pats[0]) for a in pats): return False
    for i in range(len(pats)):
      for j in range(i + 1, len(pats)):
        if all(overlap(p, q) for p, q in zip(pats[i], pats[j])):
          return True
    return False

  def match_form(self, body, only=None):
    if not hasattr(self, 'match_names'): self.match_names = set()
    """the clauses of a definition as one clause with a match, which
       is what HOL4's first match semantics means; with `only' the
       clauses of that constant alone, for a definition of a family
       in which one function has the overlapping clauses
       (overrides.MATCH_CLAUSES)"""
    global CONS
    CONS = self.ctx.cons
    toks = hterm.tokenize(body)
    e = self.arg_cons(self.arm_intvars(
          self.lambda_cons(hterm.Parser(toks, self.ctx).parse())))
    # a bound variable whose name is a constant of the port is
    # renamed here as well (word_copy matches on Shift shift r1 r2
    # n, and shift is the overload of backend_common's word_shift)
    self.ctx.vars = self.shadowing(e)
    cls = hterm.clauses_of(e)
    if only is not None:
      cls = [c for c in cls
             if c[0].kind == 'id' and c[0].name == only]
      if not cls: raise SyntaxError('match_form: no clause of ' + only)
    hop = cls[0][0]
    n = max(len(args) for _, args, _ in cls)
    if any(len(args) != n for _, args, _ in cls):
      raise SyntaxError('match_form: different arities')
    # the names of the arguments, from the clauses that have a
    # variable there
    names = []
    for i in range(n):
      nm = None
      for _, args, _ in cls:
        if args[i].kind == 'id' and not iscon(args[i].name) \
           and args[i].name != '_' and args[i].name not in names:
          nm = args[i].name; break
      if nm is None:
        # a name the port invents for an argument that every
        # clause patterns on.  It has to differ from the ones it
        # invented for another member of the same family: the two
        # stand in one quotation and a name there is one type
        # (bvlSem's do_eq takes a value where its do_eq_list takes
        # a list of them)
        nm = 'x' + str(i + 1)
        while nm in names or nm in self.match_names: nm += "'"
      # a variable whose name is a constant is renamed, and the
      # head of the definition has to use the new name as well
      # (lab_to_target's get_shmem_info takes an ffi_names)
      names.append(self.ctx.vars.get(nm, nm))
      self.match_names.add(names[-1])
    pats = [i for i in range(n)
            if any(args[i].kind != 'id' or iscon(args[i].name)
                   for _, args, _ in cls)
            and not all(args[i].kind == 'id' and
                        not iscon(args[i].name)
                        for _, args, _ in cls)]
    pr = hterm.Printer(self.ctx)
    # the theories that can provide the constructors of every
    # pattern, so that an ambiguous one is resolved as HOL4 does
    # (word_copy's 'copy_prop_inst Skip cs = (Skip,cs)' matches on
    # the Skip of asm and gives back the Skip of wordLang)
    self.clause_clash(body)
    # a type that the source itself puts on a pattern says which
    # theory an ambiguous constructor of another arm is from
    # (word_elimProof's dest_word_loc matches on the Loc of
    # wordLang's word_loc, which only its catchall says)
    atys = {}
    qual = set()
    for _, args, _ in cls:
      for i in pats:
        a = args[i]
        while a.kind == 'paren': a = a.e
        if a.kind != 'typed': continue
        try:
          ty = hterm.parse_type_text(
                 ' '.join(t.text for t in a.ty))
        except Exception:
          continue
        if ty[0] != 'op': continue
        # a type that the source qualifies (bvl$exp) says the
        # theory itself, and that is the whole point of writing it
        # there: without it every theory that has a type of the
        # name is taken, and a constructor that several of them
        # have is resolved by nothing
        if '$' in ty[1]:
          ts = {ty[1].split('$')[0]}
          qual |= ts
        else:
          nm = ty[1]
          ts = {t for (t, ty2) in self.db.datatypes if ty2 == nm}
        if ts: atys[i] = ts | atys.get(i, set())
    # the scrutinee of the match has one type, so a type that one
    # arm says is the type of every arm: the Op of the arm under
    # ((Var n):bvl$exp) is bvl's too.  A constructor that bvl has
    # not got (the IntOp of its argument) falls back on the
    # theories that have it, as it does everywhere
    base = qual or self.contys
    arms = []
    done = False
    for hd_, args, r in cls:
      sub = {args[i].name: names[i] for i in range(n)
             if i not in pats and args[i].kind == 'id'
             and not iscon(args[i].name)}
      # the first pattern that has a constructor in it carries the
      # type, so that an ambiguous constructor is resolved as HOL4
      # does; an arm whose pattern is a variable or an empty list
      # (word_simp's strip_const matches on [] first) says nothing
      if not done and any(has_con(args[i]) for i in pats):
        args = list(args)
        for i in pats:
          # the type that the source puts on a pattern says which
          # theory the constructors of that argument are from,
          # and says nothing about the other arguments
          self.contys = atys.get(i) or base
          args[i] = self.annotate_pat(args[i], True)
        self.contys = base
        done = True
      # the patterns of a clause bind their own variables, and
      # some of them hold an integer where the ones of another
      # clause do not (dataSem's lim_safe has [Number i; v] in
      # one clause and (MemOp (MutCons tag i)) in another)
      iv = self.ctx.intvars
      vs = set()
      for i in pats: vs |= self.int_vars_node(args[i])
      self.ctx.intvars = iv | vs
      wasc = self.contys
      self.contys = base
      try:
        # a comment of the source before the clause goes before
        # the arm that the port makes of it
        cs = hterm.pop_comments(hd_)
        # a pattern is a constructor under its arguments, and HOL
        # Light reads one without parentheses round it; the
        # brackets that the source puts round the pattern of a
        # clause are the ones that its application needs
        # (is_pure (IntOp Add) = F), and the match that the port
        # writes of the clauses needs none.  The patterns of
        # several arguments are a tuple and need theirs
        def bare(a):
          while a.kind == 'paren': a = a.e
          return a
        pat = ','.join(pr.pr(bare(args[i]), 2) for i in pats)
        if len(pats) > 1: pat = '(' + pat + ')'
        # a conditional or a let of an arm needs no parentheses, as
        # HOL Light reads the arm to the end of it; a match does,
        # or the arms after this one would be its
        rr = r
        while rr.kind == 'paren': rr = rr.e
        rp = (0 if rr.kind in ('cond', 'let')
                   and not hterm.open_tail(rr) else 2)
        arms.append((cs, pat,
                     self.pr_body(pr, hterm.rename_ast(r, sub), rp)))
      finally:
        self.ctx.intvars = iv
        self.contys = wasc
    scrut = ','.join(names[i] for i in pats)
    if len(pats) > 1: scrut = '(' + scrut + ')'
    head = pr.pr(hop, 0) + ' ' + ' '.join(names)
    # a comment of the source before a clause stands before the
    # arm that the port makes of it, as it does in the source
    def pre(cs):
      return ''.join('// ' + l + '\n  '
                     for cm in cs for l in cm)
    body = pre(arms[0][0]) + '%s -> %s' % arms[0][1:]
    for cs, p, b in arms[1:]:
      body += '\n  ' + pre(cs) + '| %s -> %s' % (p, b)
    self.ctx.vars = {}
    text = '%s =\n  match %s with\n    %s' % (head, scrut, body)
    # a comment that no clause of this definition has taken goes at
    # the end of the match -- but with `only' the other clauses of
    # the definition are still to come, and the caller puts the
    # comments of those where they belong
    if only is None:
      for l in self.left_comments(toks, text):
        text += '\n  // ' + l
    self.ctx.vars = {}
    return text

  # -- type abbreviations, overloads, inductive relations --------

  def typeabbrev(self, b):
    txt = (overrides.TYPE_TEXT.get((self.thy, b.name)) or
           dbmod.strip_quote(b.body))
    # a comment that stands after the type (wordLang's cutsets)
    cs = [' '.join(m.group(0).split())
          for m in re.finditer(r'\(\*.*?\*\)', b.body or '', re.S)]
    ty = hterm.parse_type_text(txt)
    params = hterm.type_vars_of(ty)
    if params:
      self.out.append(self.at(
        b, 'the type abbreviation %s, which the port expands'
           % b.name))
    else:
      # the type may be too long for one line
      body = self.typ(txt, keep=True)
      head = 'new_type_abbrev("%s",`:' % self.tnm(b.name)
      text = ('\n'.join(fill(head, body.split(' '), 76, tight=True))
              + '`);;')
      if max(len(l) for l in text.split('\n')) > 79:
        text = ('new_type_abbrev("%s",\n' % self.tnm(b.name) +
                '\n'.join(fill('  `:', body.split(' '), 76,
                                tight=True)) + '`);;')
      # the comment stands after the phrase, on its line where the
      # source has it there and the line is not too long
      for c in cs:
        ls = text.split('\n')
        text = (text + ' ' + c if len(ls[-1]) + len(c) + 1 <= 79
                else text + '\n' + c)
      self.out.append(text)

  ETA = re.compile(r"^[\\\u03bb]\s*((?:[A-Za-z_][A-Za-z0-9_']*\s*)+)"
                   r"\.\s*([A-Za-z_][A-Za-z0-9_']*)\s+(.*)$")

  def overload(self, b):
    txt = dbmod.strip_quote(b.body)
    # an overload that is a constant with its arguments spelled
    # out is that constant (mlstring overloads < with
    # \x y. mlstring_lt x y)
    m = self.ETA.match(txt.strip())
    if m and m.group(1).split() == m.group(3).split():
      txt = m.group(2)
    # an overload of one constant whose name other theories of the
    # port use for a constant of their own was an overload in HOL
    # Light as well; now the port writes every such name out as
    # the constant it means, so this one is expanded like any
    # other overload of a source
    # an overload of a symbolic infix the source declared itself is
    # written as an application of the constant it stands for
    if (b.name in hterm.OWN_INFIX and
        b.name not in hterm.BASE_INFIX and IDENT.match(txt.strip())):
      c = self.ctx.name(txt.strip())
      hterm.set_infix_name(b.name, c)
      self.out.append(self.at(
        b, 'the overload %s, which the port writes as an '
           'application of %s' % (b.name, c)))
      return
    # an infix that the source overloads with a term of its own
    # is written as an application of that term (the ' of
    # cmlPtreeConversion is the bind of the option monad)
    if (b.name and b.name in hterm.INFIX and
        not IDENT.match(txt.strip()) and
        self.ctx.overloads.get(b.name)):
      hterm.set_infix_lambda(b.name)
      self.out.append(self.at(
        b, 'the overload %s, which the port expands' % b.name))
      return
    # an infix that HOL Light has as well becomes an overload of
    # HOL Light, which resolves it by the type as HOL4 does
    if b.name in hterm.BASE_INFIX and IDENT.match(txt.strip()):
      c = self.const_name(txt.strip())
      # unless it is one HOL Light has not got (++), which the port
      # writes as an application of the constant it stands for:
      # there is no notation left for an overload to resolve
      if b.name in overrides.BASE_INFIX_CONST:
        self.ctx.overloads[b.name] = c
        self.out.append(self.at(
          b, 'the overload %s, which the port writes as an '
             'application of %s' % (b.name, c)))
        return
      self.out.append('hol4_overload "%s" "%s";;' % (b.name, c))
      return
    self.warn.append('Overload %s' % b.name)
    self.out.append(self.at(
      b, 'the overload %s, which the port expands' % b.name))

  def enable_monad(self, text):
    """the do notation of a source is the bind of the monad that it
       enables; without one it is HOL4's overloaded monad_bind"""
    nm = hol4.monad_enabled(text)
    if nm is None: return
    m = self.db.monads.get(nm)
    if m is None:
      self.warn.append('unknown monad ' + nm)
      return
    out = {}
    for f in ('bind', 'ignorebind'):
      c = m.get(f)
      if c and IDENT.match(c): out[f] = self.ctx.name(c)
    hterm.set_monad(out)
    # the ++ of a source that has enabled a monad is the choice of
    # that monad, not the append of two lists (fromSexp's sexpopt
    # tries the second parse where the first gives NONE).  HOL
    # Light has no ++ at all, so the port writes that choice out
    # as the constant it is, and PLAIN_APPEND of tools/overrides.py
    # says which occurrences of such a file are the list append
    # after all
    c = m.get('choice')
    if c and IDENT.match(c) and self.thy in overrides.MONAD_CHOICE:
      self.ctx.overloads['++'] = self.ctx.name(c)
    # HOL4's monadsyntax overloads return with the unit of the
    # monad, which may be a term and not a constant
    u = m.get('unit')
    if u:
      self.ctx.overloads['return'] = (
          self.ctx.name(u) if IDENT.match(u) else self.term(u))

  # the monadic state machinery that HOL4's ml_monadBaseLib makes
  # with ML code: the accessors of a state record, the
  # manipulators of its fixed size arrays, the functions of its
  # exception type and the run function of an initial state
  # (reg_alloc and linear_scan use all four)

  # the patterns are in hol4.py, because the db uses them as well
  # (it has to know the constants that the port makes here, or a
  # definition of another theory with the same name is not seen as
  # a clash: word_elimProof defines a get_stack of its own)

  ACCESS_FUNS = hol4.MONAD_ACCESS_FUNS
  EXN_FUNS = hol4.MONAD_EXN_FUNS
  ARR_FUNS = hol4.MONAD_ARR_FUNS
  RUN_FUN = hol4.MONAD_RUN_FUN
  ARR_NAMES = hol4.MONAD_ARR_NAMES

  def monadic(self, b):
    txt = b.text
    m = self.ARR_NAMES.search(txt)
    if m:
      self.arrflds = re.findall(r'"([^"]*)"', m.group(1))
    m = self.ACCESS_FUNS.search(txt)
    if m:
      self.monad_access(m.group(1)); return True
    m = self.EXN_FUNS.search(txt)
    if m:
      self.monad_exceptions(m.group(1), m.group(2)); return True
    m = self.ARR_FUNS.search(txt)
    if m:
      flds = [x.strip()[:-len('_accessors')]
              for x in m.group(1).split(',')
              if x.strip().endswith('_accessors')]
      self.monad_arrays(flds, 'Subscript'); return True
    m = self.RUN_FUN.search(txt)
    if m:
      self.monad_run(m.group(1), m.group(3)); return True
    return False

  def mdef(self, name, text):
    """one of the definitions of the monadic machinery; the
       constant has the name that the port gives it, which is not
       the name of HOL4 where another theory defines one of its
       own (word_elimProof has a get_stack as well)"""
    nm = self.nm(name)
    if nm != name and text.startswith(name):
      text = nm + text[len(name):]
    bind = self.bindname(name + '_def')
    dbmod.bind_thm(self.db, self.thy, name + '_def', bind)
    self.out.append('let %s = new_definition\n  `%s`;;\n'
                    % (bind, fmt(text)))
    EMITTED_DEFS.append((self.thy, nm, bind))

  def monad_access(self, ty):
    """get_f and set_f for every field of the state record"""
    rty = self.tnm(ty)
    self.out.append(shorten(
      '(* HOL4 makes the monadic accessors of %s with ML code\n'
      '   (define_monad_access_funs of ml_monadBaseLib); these are\n'
      '   the definitions that it makes *)' % rty))
    for f, _ in self.rec_src.get(rty, []):
      self.mdef('get_' + f,
                'get_%s = (\\state. (M_success (%s state),state))'
                % (f, self.ctx.field(f)))
      self.mdef('set_' + f,
                'set_%s x =\n  (\\state. (M_success one,%s (K x) state))'
                % (f, self.ctx.fupd(f)))

  def monad_exceptions(self, exn, ty):
    """raise_C and handle_C for every constructor of the exception
       type of the state monad"""
    cons = None
    owner = None
    for (t, ety), (cs, _) in self.db.datatypes.items():
      if ety == exn and (t in self.db.ancestors(self.thy) or
                         t == self.thy):
        cons = cs
        owner = t
    if cons is None: return
    # where the exception type is another theory's (linear_scan
    # uses reg_alloc's state_exn, as HOL4 does, whose Datatype it
    # has in a comment), HOL4 makes constants of its own with the
    # same names and the same values; the port has one namespace,
    # so the ones of that theory are the ones it uses
    if owner != self.thy:
      self.out.append(shorten(
        '(* HOL4 makes the functions of the exception type %s a\n'
        '   second time here (define_monad_exception_functions of\n'
        '   ml_monadBaseLib); they are the same as the ones that\n'
        '   %s makes, which the port uses *)' % (exn, owner)))
      return
    args = {}
    for c in cons:
      n = len([1 for i in range(9)
               if self.db.con_argty.get((c, i)) is not None])
      args[c] = ' '.join('e%d' % (i + 1) for i in range(n))
    self.out.append(shorten(
      '(* HOL4 makes the functions of the exception type %s with ML\n'
      '   code (define_monad_exception_functions of\n'
      '   ml_monadBaseLib); these are the definitions that it\n'
      '   makes *)' % exn))
    for c in cons:
      a = args[c]
      con = ('(%s %s)' % (self.nm(c), a)) if a else self.nm(c)
      self.mdef('raise_' + c,
                'raise_%s %s=\n  (\\state. (M_failure %s,state))'
                % (c, a + ' ' if a else '', con))
    for c in cons:
      arms = []
      for d in cons:
        a = args[d]
        pat = self.nm(d) + (' ' + a if a else '')
        con = ('(%s %s)' % (self.nm(d), a)) if a else self.nm(d)
        if d == c:
          arms.append('%s -> f%s state' % (pat, ' ' + a if a else ''))
        else:
          arms.append('%s -> (M_failure %s,state)' % (pat, con))
      self.mdef('handle_' + c,
                'handle_%s x f =\n'
                '  (\\state.\n'
                '    match x state with (res,state) ->\n'
                '      match res with M_success y -> (M_success y,state)\n'
                '      | M_failure e ->\n'
                '        (match e with %s))' % (c, ' | '.join(arms)))

  def monad_arrays(self, flds, exn):
    """f_length, f_sub and update_f of a fixed size array field"""
    self.out.append(shorten(
      '(* HOL4 makes the manipulators of the fixed size arrays with\n'
      '   ML code (define_MFarray_manip_funs of ml_monadBaseLib);\n'
      '   these are the definitions that it makes *)'))
    for f in flds:
      get = '(\\state. %s state)' % self.ctx.field(f)
      setf = '(\\x state. %s (K x) state)' % self.ctx.fupd(f)
      self.mdef(f + '_length', '%s_length = Marray_length %s' % (f, get))
      self.mdef(f + '_sub',
                '%s_sub = Marray_sub %s %s' % (f, get, self.nm(exn)))
      self.mdef('update_' + f,
                'update_%s =\n  Marray_update %s\n    %s %s'
                % (f, get, setf, self.nm(exn)))

  def monad_run(self, ty, new):
    """the record of an initial state, in which an array field is a
       length and an initial value, and the run function"""
    rty = self.tnm(ty)
    flds = self.rec_src.get(rty, [])
    self.out.append(shorten(
      '(* HOL4 makes the record of an initial state of %s and the\n'
      '   run function with ML code (define_run of\n'
      '   ml_monadBaseLib); an array field of it is the length and\n'
      '   the initial value of the array *)' % rty))
    lines = []
    for i, (f, ty2) in enumerate(flds):
      if f in self.arrflds and ty2 is not None and ty2[1] == 'list':
        ty2 = ('op', 'prod', [('op', 'num', []), ty2[2][0]])
      s = hterm.print_type(ty2, self.ctx) if ty2 is not None else 'num'
      pre = '  [' if i == 0 else '   '
      lines.append(' \\\n'.join(
        fill(pre + '"%s","' % f, s.split(' '), 77)) + '"')
    head = ('let %s_FIELDS = define_record "%s"' % (ocaml_name(new), new))
    if len(head) > 79:
      head = ('let %s_FIELDS =\n  define_record "%s"'
              % (ocaml_name(new), new))
    self.out.append('%s\n%s];;' % (head, ';\n'.join(lines)))
    # the literal of such a record is the one that RECORD_OF names
    self.ctx.recs[new] = [f for f, _ in flds]
    args = []
    for f, _ in flds:
      acc = '%s_%s state' % (new, f)
      if f in self.arrflds:
        args.append('(REPLICATE (FST (%s)) (SND (%s)))' % (acc, acc))
      else:
        args.append('(%s)' % acc)
    self.mdef('run_' + new,
              'run_%s x state =\n  run x (mk_%s %s)'
              % (new, rty, ' '.join(args)))

  def hol_reln(self, b):
    r = hol4.hol_reln(b.text)
    if not r: return False
    name, body = r
    self.inductive(hol4.Block('Inductive', name + '_rules', [], body))
    return True

  def inductive(self, b):
    # a rule may hold integers or a name of a theory that the
    # overrides give, as the clauses of a definition may
    key = (self.thy, ocaml_name(b.name))
    conof = dict(overrides.CON_OF.get(key, {}))
    if '*' in conof:
      t = conof.pop('*')
      for (t2, ty), (cons, _) in self.db.datatypes.items():
        if t2 != t: continue
        for c in cons:
          if c in self.ctx.overloaded: conof.setdefault(c, t)
    self.conof_said = {k: v for k, v in conof.items()
                       if not isinstance(v, dict)}
    self.ctx.intnums = key in overrides.INT_NUMERALS
    self.ctx.intvars = set(overrides.INT_ARGS.get(key, []))
    self.ctx.reclit = overrides.RECORD_OF.get(key)
    # the record type of a variable of this block, as a definition
    # and a statement take it (overrides.FIELD_VAR_DEF): the s of
    # source_to_flat's s_rel is the state of the source and the s'
    # is the state of flatLang, which the rule does not say
    oldfv = self.ctx.fieldvar
    fv = overrides.FIELD_VAR_DEF.get(key)
    if fv:
      self.ctx.fieldvar = dict(self.fieldvar)
      self.ctx.fieldvar.update(fv)
    was = dict((nm, (self.ctx.names.get((self.thy, nm)),
                     nm in self.ctx.overloaded))
               for nm in conof)
    for nm, t in conof.items():
      self.ctx.overloaded.discard(nm)
      self.ctx.names[(self.thy, nm)] = self.ctx.names.get((t, nm), nm)
    # the relations that the block defines get the name that the
    # port gives them, as the constants of a Definition do: a
    # relation whose name another theory has as well is written
    # with the name of its theory (word_bignumProof's Eval, where
    # ast has an Eval of its own)
    self.ctx.defining = set(dbmod.rule_names(b.body))
    defined = sorted(self.ctx.defining)
    try:
      term = fmt(self.term(b.body))
    finally:
      for nm in conof:
        old, ovl = was.get(nm, (None, True))
        if ovl: self.ctx.overloaded.add(nm)
        if old is None: del self.ctx.names[(self.thy, nm)]
        else: self.ctx.names[(self.thy, nm)] = old
      self.conof_said = {}
      self.ctx.intnums = False
      self.ctx.intvars = set()
      self.ctx.reclit = None
      self.ctx.defining = set()
      self.ctx.fieldvar = oldfv
    # the binding of the relation in the file, as a definition's
    # (word_bignumProof and five other files state a v_rel of
    # their own, and a proof names the one of its file)
    bind = self.bindname(b.name)
    dbmod.bind_thm(self.db, self.thy, b.name, bind)
    # HOL4 gives a relation three theorems of its own; the port
    # keeps the triple that HOL Light's own machinery gives,
    # and these are its parts under the names HOL4 uses
    for p2, k in (('_rules', 'cake_rules'), ('_ind', 'cake_ind'),
                  ('_cases', 'cake_cases')):
      dbmod.bind_thm(self.db, self.thy, b.name + p2,
                     '%s %s' % (k, bind))
    text = 'let %s = cake_inductive\n  `%s`;;' % (bind, term)
    for c in defined:
      EMITTED_DEFS.append((self.thy,
                           self.ctx.names.get((self.thy, c), c),
                           bind))
    # the relations that the block defines are overloads of HOL4
    # as the constants of a Definition are
    overloads = self.overloads_of(defined)
    # a spot of a definition that no rule can resolve: the second
    # component of the result of bvl_handle's compile is a
    # db_var_set and the first a list of bvl expressions, and
    # bvl's Var and db_vars' Var both take one argument, so
    # nothing but the place says which is which.  A patch that
    # does not apply is an error and not a silence
    if os.environ.get('PATCHDBG') and key in overrides.DEF_PATCH:
      print('PATCHDBG', text[:900], file=sys.stderr)
    text = patch_text(text, overrides.DEF_PATCH.get(key, []))
    text = file_patch(self.thy, text, self.filepatched)
    # HOL4's [simp] on a definition says that its equations belong
    # to the set that its simplifier reaches for, which the port
    # says with a call after the definition, as it does for a
    # theorem (tactics/simpset.ml)
    if 'simp' in (b.attrs or []):
      text += '\nadd_simp %s;;' % bind
    self.out.append(text if not overloads else
                    text + '\n' + '\n'.join(overloads))


IDENT = re.compile(r"^(\w+\$)?[A-Za-z_][A-Za-z0-9_']*$")

CONS = set()           # the constructors in scope, set by the porter


def iscon(n):
  """is this the name of a constructor?  A CakeML source may write
     it with the name of its theory (fpSem$FP_Add)"""
  return n.split('$')[-1] in CONS


# an ML block of a source that is a proof: HOL4's Resume and
# Finalise continue the proof of a theorem, and a tactic that the
# source has on its own does not parse as a block either
PROOF_ML = re.compile(
  r'^\s*(Resume|Finalise)\b|^\s*(>>|>-|\\\\|THEN\b)|'
  r'\b(Cases_on|qexists_tac|qabbrev_tac|match_mp_tac|metis_tac|'
  r'rw|fs|gvs|simp|rfs|strip_tac)\s*[\[(`]', re.M)


# a comment of the source whose body is HOL4 code (a definition or
# a theorem that the source has commented out, an SML binding, a
# tactic): the port has no HOL4 code, not even in a comment, so it
# points at those lines instead of keeping them
COMMENTED_CODE = re.compile('|'.join('(?:%s)' % p for p in [
  r"^\s*(Theorem|Triviality|Definition|Inductive|CoInductive)\s+"
  r"[A-Za-z0-9_']+\s*(\[[^\]]*\])?\s*:",
  r'^\s*Datatype\s*:',
  r'^\s*(Proof|QED|End|Termination)\s*$',
  r"^\s*(val|fun)\s+[A-Za-z0-9_'()]+\s*[=(]",
  r'^\s*open\s+[A-Za-z]',
  r'(^|\s)(>>|>-|\\\\)(\s|$)',
  r'\b(store_thm|save_thm|prove|metis_tac|srw_ss|EVAL)\s*[("\[]',
  r'\b(rw|fs|gvs|simp|rfs|asm_simp_tac|rpt)\s*[\[(]',
]), re.M)


# a comment that holds a block of a source is code, whatever else
# is in it
BLOCK_IN_COMMENT = re.compile('|'.join('(?:%s)' % p for p in [
  r"^\s*(Theorem|Triviality|Definition|Inductive|CoInductive)\s+"
  r"[A-Za-z0-9_']+\s*(\[[^\]]*\])?\s*:",
  # a block that the source has commented out can have the name on
  # a line of its own, with the statement in a quotation under it
  # (type_dCanon has two theorems that way, which an older HOL4
  # would have taken: Theorem foo `...` (tactic))
  r"^\s*(Theorem|Triviality|Definition|Inductive|CoInductive)\s+"
  r"[A-Za-z0-9_']+\s*(\[[^\]]*\])?\s*$",
  r'^\s*Datatype\s*:',
  r'^\s*(Proof|QED|End|Termination)\s*$',
]), re.M)


def commented_code(text):
  """is this comment of a source HOL4 code, which the port does not
     have, or prose, which it keeps?  A comment with a block of a
     source in it is code; one that sketches a line or two of it in
     prose is a comment (the head comment of bvi_let sketches a Let
     of BVI and an SML let, and is the documentation of the file)"""
  body = uncomment(text)
  if BLOCK_IN_COMMENT.search(body): return True
  lines = [l for l in body.split('\n') if l.strip()]
  if not lines: return False
  n = sum(1 for l in lines if COMMENTED_CODE.search(l))
  return 2 * n >= len(lines)


def uncomment(text):
  """the text with the brackets of its comments taken out, so that
     a line of HOL4 code in a one line comment starts the line"""
  return re.sub(r'\(\*|\*\)', '  ', text)


def comment_only(text):
  """is everything of this text inside a comment?"""
  i = 0
  depth = 0
  while i < len(text):
    if text.startswith('(*', i): depth += 1; i += 2; continue
    if text.startswith('*)', i):
      depth -= 1
      if depth < 0: return False
      i += 2; continue
    if not depth and not text[i].isspace(): return False
    i += 1
  return depth == 0


def has_con(p):
  """is there a constructor in this pattern?  An arm whose pattern
     is a variable or an empty list says nothing about the type"""
  while p.kind in ('paren', 'typed'): p = p.e
  if p.kind == 'id': return iscon(p.name)
  if p.kind == 'app':
    h, args = hterm.strip_app(p)
    return ((h.kind == 'id' and iscon(h.name)) or
            any(has_con(a) for a in args))
  if p.kind == 'list': return bool(p.items)
  if p.kind == 'infix': return has_con(p.l) or has_con(p.r)
  return False


def is_var_pat(p):
  """is this pattern a variable?"""
  while p.kind in ('paren', 'typed'): p = p.e
  return p.kind == 'id' and not iscon(p.name)


def vars_pat(p):
  """is this pattern a variable or a tuple of variables, which is
     what the argument of a constructor pattern can be without
     making the pattern a nested one?"""
  while p.kind in ('paren', 'typed'): p = p.e
  if p.kind == 'infix' and p.op == ',':
    return vars_pat(p.l) and vars_pat(p.r)
  return is_var_pat(p)


def nested_pat(p):
  """has this pattern a pattern inside a constructor?  HOL Light's
     machinery for a definition by patterns compiles those into a
     decision tree, which takes minutes where a match takes no
     time at all"""
  while p.kind in ('paren', 'typed'): p = p.e
  if p.kind == 'infix' and p.op == ',':
    return nested_pat(p.l) or nested_pat(p.r)
  if p.kind == 'infix' and p.op == '::':
    args = [p.l, p.r]
  elif p.kind == 'list':
    # [x] is CONS x NIL and [x; y] is CONS x (CONS y NIL)
    return len(p.items) > 1 or any(not vars_pat(a) for a in p.items)
  else:
    h, args = hterm.strip_app(p)
    if not (h.kind == 'id' and h.name in CONS): return False
  return any(not vars_pat(a) for a in args)


def overlap(p, q):
  """can two patterns match the same value?"""
  while p.kind == 'paren': p = p.e
  while q.kind == 'paren': q = q.e
  if p.kind == 'typed': return overlap(p.e, q)
  if q.kind == 'typed': return overlap(p, q.e)
  if p.kind == 'id' and p.name not in CONS: return True
  if q.kind == 'id' and q.name not in CONS: return True
  if p.kind == 'id' and q.kind == 'id': return p.name == q.name
  if p.kind == 'id' or q.kind == 'id':
    h = hterm.strip_app(q if p.kind == 'id' else p)[0]
    return h.kind == 'id' and h.name == (p.name if p.kind == 'id'
                                         else q.name)
  if p.kind == 'num' and q.kind == 'num': return p.text == q.text
  if p.kind == 'num' or q.kind == 'num': return False
  if p.kind == 'list' and q.kind == 'list':
    return len(p.items) == len(q.items) and \
           all(overlap(a, b) for a, b in zip(p.items, q.items))
  if p.kind == 'list' or q.kind == 'list':
    o, l = (q, p) if p.kind == 'list' else (p, q)
    # a list pattern against a :: pattern
    if o.kind == 'infix' and o.op == '::':
      if not l.items: return False
      return overlap(o.l, l.items[0]) and \
             overlap(o.r, Node_list(l.items[1:], l))
    return False
  if p.kind == 'infix' and q.kind == 'infix':
    if p.op != q.op: return False
    return overlap(p.l, q.l) and overlap(p.r, q.r)
  if p.kind == 'infix' or q.kind == 'infix': return False
  hp, ap = hterm.strip_app(p)
  hq, aq = hterm.strip_app(q)
  if hp.kind != 'id' or hq.kind != 'id': return True
  if hp.name != hq.name: return False
  return all(overlap(a, b) for a, b in zip(ap, aq))


def Node_list(items, tok):
  return hterm.Node('list', tok=tok.tok, items=items)


def letline(binding, how, rest):
  """the phrase that makes a definition.  A binding of a pair is
     long, and the way has a long name of its own, so the two go on
     a line each where they do not fit on one, and the two names of
     the pair on a line each where even that is too long."""
  head = 'let %s = %s' % (binding, how)
  if len(head) <= 79:
    return '%s\n  %s;;' % (head, rest)
  if len('let %s =' % binding) <= 79:
    return 'let %s =\n  %s\n  %s;;' % (binding, how, rest)
  a, b = binding.split(',')
  return 'let %s,\n    %s =\n  %s\n  %s;;' % (a, b, how, rest)


def file_patch(thy, text, used=None):
  """the patches that a whole file wants (overrides.FILE_PATCH): a
     name that one theory of a pair means where an argument of it
     is of the other\'s, which no rule of the resolution settles.
     The pattern is a regular expression over the text as it is
     laid out, where \\s+ stands for the break of a line as well
     as a space, and every spot of the file that matches is
     patched.  An entry that the whole file never matches is an
     error, which tools/port.py reports when the file is done"""
  for i, (was, now) in enumerate(overrides.FILE_PATCH.get(thy, [])):
    text, k = re.subn(was, now, text)
    if k and used is not None: used.add(i)
  return '\n'.join(wrap(l, 0, 79) if len(l) > 79 else l
                    for l in text.split('\n'))


def near(text, ws):
  """what stands where a patch looked, for a patch that does not
     apply.  The commonest reason is that a name resolves to
     another theory than it did -- a theory that comes earlier in
     the porting order has taken it -- and then the words of the
     patch are there but for one, so the longest prefix of them
     that is still in the text says where to look and what the
     port says there now"""
  best = 0
  for k in range(len(ws), 0, -1):
    pat = re.compile(r'\s+'.join(re.escape(w) for w in ws[:k]))
    m = pat.search(text)
    if m:
      best = k
      got = ' '.join(text[m.start():m.start() + len(' '.join(ws))
                          + 40].split())
      return ('\n   the first %d word(s) of it are there, and what '
              'follows is\n   %s' % (k, got))
  return '\n   not one word of it is in the block'


def patch_text(text, patches, what='DEF_PATCH'):
  """apply the DEF_PATCH (or THM_PATCH) entries of a block to its
     text.  The text is laid out already, so a patch is matched
     with every run of whitespace of it standing for any other (a
     patch is about what the port says and not about where the
     lines of it break), and a line that the patch makes too long
     is broken again.  A patch that does not apply is an error and
     not a silence"""
  for was, now in patches:
    ws = was.split()
    pat = re.compile(r'\s+'.join(re.escape(w) for w in ws))
    m = pat.search(text)
    if m is None:
      raise SyntaxError('%s does not apply: %s%s'
                        % (what, ' '.join(ws)[:40], near(text, ws)))
    text = text[:m.start()] + ' '.join(now.split()) + text[m.end():]
  return '\n'.join(wrap(l, 0, 79) if len(l) > 79 else l
                   for l in text.split('\n'))


def fmt(text, indent=3, width=79, last=3, extra=2):
  """the layout of a translated term in the HOL Light source; the
     last line of the term is followed by a quote and a ;; (last
     characters), so it has to be that much shorter.  A line that
     is too long is broken and the rest of it indented by extra,
     which is what lines the rest up under the start of the term
     where the term stands in a list of quotations"""
  lines = [l.rstrip() for l in text.split('\n') if l.strip()]
  if not lines: return ''
  base = len(lines[0]) - len(lines[0].lstrip())
  out = [lines[0].lstrip()]
  for l in lines[1:]:
    k = len(l) - len(l.lstrip())
    out.append(' ' * min(indent + max(0, k - base), 30) + l.lstrip())
  return '\n'.join(
    wrap(l, indent, width - (last if i == len(out) - 1 else 0), extra)
    for i, l in enumerate(out))


# the characters a term may be broken before: a newline is as good
# as a space between two tokens of HOL Light
SAFE = '([,#+|'


def wrap(line, indent, width, extra=2, hard=False):
  # a comment of a term runs to the end of its line, so breaking
  # it would put the rest of the line in the comment
  if '//' in line: return line

  """break a line that is too long at a space (or, in a term, before
     a character that starts a token); the continuation is indented
     by extra, and with hard a line without any place to break is
     broken anyway (which only comments allow)"""
  k = len(line) - len(line.lstrip())
  ind = ' ' * (k + extra)
  out = []
  cur = line
  first = True
  while len(cur) + (indent if first else 0) > width:
    limit = width - (indent if first else 0)
    cut = -1
    drop = 0
    safe = -1
    quoted = False
    i = 0
    while i < len(cur) and i <= limit:
      c = cur[i]
      if quoted:
        # a backslash in a string escapes the next character
        if c == '\\': i += 2; continue
        if c == '"': quoted = False
        i += 1; continue
      if c == '"':
        quoted = True; i += 1; continue
      # the break has to be beyond the indentation of the
      # continuation, or the line would not get any shorter
      # and not between the backslash of an abstraction and the
      # variable it binds, which reads as if the line ended in one
      if i > len(ind) and cur[i-1] != '\\':
        if c == ' ': cut = i; drop = 1
        elif c in SAFE and cur[i-1] != ' ': safe = i
      i += 1
    if cut < 0 and safe > 0: cut = safe; drop = 0
    if cut < 0:
      # nothing to break at: with a long indentation, try again with
      # a shorter one
      if len(ind) > 6:
        ind = ' ' * 6
        continue
      if not hard or limit <= len(ind) + 1: break
      cut = limit
      drop = 0
    out.append(cur[:cut])
    cur = ind + cur[cut+drop:]
    first = False
  out.append(cur)
  return '\n'.join(out)


def wf_relation(extra):
  """the relation of a WF_REL_TAC in a HOL4 Termination block
     (the sources write it in lower case as well)"""
  m = re.search(r'(?i:WF_REL_TAC)\s*([`‘“])', extra)
  if not m: return None, extra
  q = m.group(1)
  close = {'`': '`', '‘': '’', '“': '”'}[q]
  i = m.end()
  if extra[i-1:i+1] == '``': i += 1
  j = extra.index(close, i)
  rel = extra[i:j]
  rest = extra[:m.start()] + extra[j+1:]
  return rel, rest


def mlpath(rel):
  return re.sub(r'Script\.sml$', '.ml', rel)


def check_no_run():
  """a run loads the files of ml/ one after the other, so writing
     into ml/ while one is going invalidates it (and a file that a
     needs of a later file reloads is an error of its own)"""
  out = subprocess.run(['ps', '-eo', 'args'],
                       capture_output=True, text=True).stdout
  # the shell that runs checkseq, and not a command line that
  # merely has the word in it (the one that starts this is often
  # the one that starts a run after it)
  if re.search(r'^\S*sh\s+\S*[c]heckseq(\s|$)', out, re.M):
    raise SystemExit('a run is going: ml/ must not change under it')


# a theorem that the port writes by hand, as the file writes it
HANDTHM = re.compile(r"^let ([A-Za-z_][A-Za-z_0-9']*) =[ ]*"
                     r"(?:\n[ ]*)?(?:try[ ]+)?"
                     r"(?:prove|new_axiom|new_definition"
                     r"|define_cases|CONJ|GEN_ALL|SPEC_ALL)\b",
                     re.M)


def port(thy, db=None):
  check_no_run()
  db = db or dbmod.Db()
  p = Porter(db, thy)
  text = p.run()
  text = '\n'.join(l.rstrip() for l in text.split('\n'))
  text = re.sub(r'\n\n\n+', '\n\n\n', text).strip('\n')
  # a line that is still too long after everything that wrapped it
  # (a statement whose closing `), goes on after the wrapping) is
  # broken here; a comment of a source keeps its length
  out, incomment = [], False
  for l in text.split('\n'):
    if not incomment and len(l) > 79 and '(*' not in l \
       and '//' not in l:
      w = wrap(l, 0, 72)
      l = w if max(len(x) for x in w.split('\n')) <= 79 else l
    if '(*' in l and '*)' not in l.split('(*')[-1]: incomment = True
    elif '*)' in l: incomment = False
    out.append(l)
  text = '\n'.join(out)
  for i, l in enumerate(text.split('\n')):
    if len(l) > 79:
      p.warn.append('line %d is %d characters' % (i + 1, len(l)))
  # a theorem or a definition that the port writes by hand
  # (overrides.EXTRA_HEAD and the others) is one a later file can
  # name as it names any other, so the bindings of the file are
  # read off the file.  gram's cmlG_def is one: HOL4 makes it with
  # ML (mk_grammar_def), so nothing of the port's own machinery
  # registered it and gramProps could not name it
  for nm in HANDTHM.findall(text):
    if nm not in db.thmbind: dbmod.bind_thm(db, thy, nm, nm)
  path = ML + db.mlpath_of(thy)
  os.makedirs(os.path.dirname(path), exist_ok=True)
  # the preface is read off the file before it is opened for
  # writing, which truncates it
  out = keep_preface(path, text)
  open(path, 'w').write(out + '\n')
  return path, p.warn, p.amb


BANNER = '(* ======================================================== *)'


def keep_preface(path, text):
  """the preface of a file is derived from the whole port -- which
     files need it, how many blocks its source has -- so
     tools/preface.py owns it and writes it after every file has
     its needs lines.  What this port writes in its place is the
     short one of a fresh file, and porting one theory also ports
     every ancestor of it (the port of a theory depends on what
     the port made of its ancestors), so one
     `python3 -I tools/port.py lab_to_targetProof` would put the
     short preface in the place of the full one in a hundred and
     forty files.  So an existing preface stays, and a full port
     refreshes it through tools/preface.py"""
  try:
    old = open(path).read().split('\n')
  except IOError:
    return text
  new = text.split('\n')
  if not old or not new or old[0] != BANNER or new[0] != BANNER:
    return text
  try:
    oe = old.index(BANNER, 1)
    ne = new.index(BANNER, 1)
  except ValueError:
    return text
  return '\n'.join(old[:oe + 1] + new[ne + 1:])


if __name__ == '__main__':
  db = dbmod.Db()
  # what a theory's port looks like depends on what the port of
  # its ancestors made of them (the type parameters of a datatype,
  # for one), so the ancestors go first, as in a whole run
  want = set(sys.argv[1:])
  anc = set()
  for thy in want: anc |= db.ancestors(thy)
  for thy, _, _ in dbmod.load_order():
    if thy in anc - want: port(thy, db)
  for thy in sys.argv[1:]:
    path, warn, amb = port(thy, db)
    print('wrote', path)
    for w in warn: print('  !', w)
    if amb: print('  ambiguous fields:', amb)
