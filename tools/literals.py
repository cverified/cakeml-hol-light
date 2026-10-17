"""check that the literals of a HOL4 definition survive the port

  python3 -I tools/literals.py [theory...]

For every definition block of a HOL4 source this takes the string
and character literals and the numerals of its term, and the ones
of the phrase of the port that defines the same constant, and
reports where the two differ.  HOL Light takes the characters of a
string literal as they are, where HOL4 reads the escapes of SML,
so a literal that the port copies is a different string: that is
what this finds (and a numeral that the port lost or invented).
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4, hterm, db as dbmod, port as portmod, defsites

KINDS = ('Definition', 'Inductive', 'CoInductive')
C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# a character literal of HOL4 is #"c", a string "..." and an
# mlstring «...»; the character one goes first, or its body would
# count as a string of its own
LIT4 = re.compile(r'#"((?:[^"\\]|\\.)*)"'
                  r'|"((?:[^"\\]|\\.)*)"'
                  r'|«([^»]*)»')
# a numeral of HOL4 or of the port, which is not a part of a name
# a numeral, which a name does not hold (and the name of a
# variable of HOL4 may be a Greek letter with a digit on it)
NUM = re.compile(r"(?<!\w)(?<!')(0x[0-9a-fA-F]+|[0-9]+)[nwci]?")


def hol4_bytes(body):
  """the bytes of all the string and character literals of a HOL4
     term; the bytes and not the literals, because the port may
     split one literal into pieces"""
  out = []
  for m in LIT4.finditer(body):
    t = next(g for g in m.groups() if g is not None)
    out += list(hterm.sml_string_bytes(t))
  return sorted(out)


PIECE = re.compile(r'"([^"]*)"|CHR\s+([0-9]+)')
# only the string literals of the port, for masking: its (CHR n)
# may be a term of the source (lexer_fun's s ++ [CHR 7]) as well
# as the way a literal holds a byte
PORT_STR = re.compile(r'"[^"]*"')


def port_bytes(text):
  """the same of a phrase of the port, where a literal holds its
     characters as they are and a byte that a literal cannot hold
     is a (CHR n); only the quotations of the phrase are read, so
     that a comment of the port counts for nothing"""
  out = []
  quoted = ' '.join(re.findall(r'`([^`]*)`', text, re.S))
  for m in PIECE.finditer(quoted):
    if m.group(1) is not None:
      out += list(m.group(1).encode('utf-8', 'replace'))
    else:
      out.append(int(m.group(2)) % 256)
  return sorted(out)


def nums(text, hol4=False):
  # a digit inside a literal is not a numeral of the term, and the
  # literals of HOL4 have escapes in them where the ones of the
  # port do not
  text = LIT4.sub(' ', text) if hol4 else PORT_STR.sub(' ', text)
  out = []
  for m in NUM.finditer(text):
    t = m.group(1)
    out.append(int(t, 16) if t.startswith('0x') else int(t))
  return sorted(out)


db = dbmod.Db()
sites = defsites.sites()
thys = sys.argv[1:] or [t for t, _, _ in dbmod.load_order()]
tot = sbad = nbad = 0
for thy in thys:
  path = db.thy_of_file.get(thy)
  if not path: continue
  p = portmod.Porter(db, thy)
  for b in hol4.parse(path):
    if b.kind not in KINDS or not p.wanted(b): continue
    body = hol4.strip_comments(b.body)
    names = dbmod.definition_names(body) or dbmod.rule_names(body)
    site = None
    for nm in names:
      for cand in (p.nm_defined(nm), nm, p.const_name(nm)):
        if cand in sites: site = sites[cand]; break
      if site: break
    if not site or not site[1]: continue
    try:
      src = open(C + '/ml/' + site[0]).read()
    except OSError:
      continue
    m = re.search(r"^let %s[ ,].*?;;$" % re.escape(site[1]), src,
                  re.M | re.S)
    if not m: continue
    text = m.group(0)
    tot += 1
    hs, ps = hol4_bytes(body), port_bytes(text)
    if hs != ps:
      miss = [x for x in hs if hs.count(x) > ps.count(x)]
      if miss:
        sbad += 1
        print('%-20s %-26s characters %s' % (thy, b.name or names[:1],
              ''.join(chr(x) for x in sorted(set(miss)))[:20]))
    # the numerals as a set: a port that writes one clause of a
    # pattern where HOL4 has several has the numeral once
    hn, pn = set(nums(body, True)), set(nums(text))
    miss = hn - pn
    if miss:
      nbad += 1
      print('%-20s %-26s numerals %s' % (thy, b.name or names[:1],
            sorted(miss)[:6]))
print('%d definitions, %d with other strings, %d with other numerals'
      % (tot, sbad, nbad))
