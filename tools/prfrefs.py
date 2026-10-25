"""the names that a proof of the store uses and the port has not

  python3 -I tools/prfrefs.py

A proof of the store names a theorem, a definition or a tactic by
its OCaml binding, so a name that no file at or before it binds is
a name that does not resolve -- the file stops at `Unbound value'
when it loads.  This reports those names: the tokens of the proofs
outside the quotations that are neither a binding of the port, nor
one of HOL Light or of the library layer (tools/hl-idents.txt),
nor a local one of the proof itself.

A name it reports is either a reference that a rename left behind
or a lemma that the port has still to prove.
"""
import os, re, sys, glob, collections

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod

KW = set('''let in and fun function with try if then else match when of rec
 begin end do done for to downto while raise assert true false not mod land
 lor lxor lsl lsr asr ref mutable type val module open struct sig as new
 fail failwith fst snd map filter rev hd tl length mem exists forall itlist
 end_itlist List Printf sprintf Failure Not_found Invalid_argument Printexc
 QUOT STR'''.split())


def main():
  db = dbmod.Db()
  order = [t for t, _, _ in dbmod.load_order()]
  pos = {t: i for i, t in enumerate(order)}
  # every binding of every file of the port, with the position of
  # the file that makes it
  made = collections.defaultdict(list)
  for t in order:
    try: p = T + '../ml/' + db.mlpath_of(t)
    except Exception: continue
    if not os.path.exists(p): continue
    text = open(p).read()
    for b in re.findall(r"(?m)^let (?:rec )?\(?([A-Za-z_][A-Za-z_0-9']*)",
                        text):
      made[b].append(pos[t])
    for b in re.findall(r"(?m)^let [A-Za-z_][A-Za-z_0-9']*,"
                        r"([A-Za-z_][A-Za-z_0-9']*)", text):
      made[b].append(pos[t])
  hl = set(l.strip() for l in open(T + 'hl-idents.txt'))
  bad = 0
  for p in sorted(glob.glob(T + '../proofs/**/*.prf', recursive=True)):
    rel = p[p.index('/proofs/') + 8:-4] + '.ml'
    thy = None
    for t in order:
      try:
        if db.mlpath_of(t) == rel: thy = t
      except Exception: pass
    if thy is None: continue
    text = open(p).read()
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    text = re.sub(r'`[^`]*`', ' QUOT ', text, flags=re.S)
    text = re.sub(r'"[^"]*"', ' STR ', text)
    local = set(re.findall(r"\b(?:let|and|fun)\s+(?:rec\s+)?"
                           r"\(?([a-zA-Z_][A-Za-z_0-9']*)", text))
    local |= set(re.findall(r"\bfun\s+(?:\([^)]*\)|[^-]*?)->", text) and
                 re.findall(r"\b([a-z][A-Za-z_0-9']*)\s*(?=[,)]?\s*->)",
                            text))
    for i in sorted(set(re.findall(r"\b([A-Za-z_][A-Za-z_0-9']*)\b",
                                   text))):
      if i in KW or i in local or i in hl: continue
      if i in made and min(made[i]) <= pos[thy]: continue
      print('%s: %s' % (rel, i))
      bad += 1
  print('%d names that do not resolve' % bad)
  return 1 if bad else 0


if __name__ == '__main__':
  sys.exit(main())
