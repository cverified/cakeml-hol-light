"""the phrases of a file of the port, each one on its own

  python3 -I tools/tolerant.py <file of the port> <out> [mark]

A theorem of the port is a plain `let foo = prove (`...`, tac);;`,
so a statement that HOL Light cannot read is an error of the file
and the phrases after it do not load -- which is what the port
wants of a finished file, and not what a harvest wants: the
harvest has to see **every** statement that does not read, not
the first one of each file.

This writes a copy of the file in which every theorem phrase is
wrapped in a `try', so that the one that fails is logged (its name,
the file and the message, to tmp/unstated.txt) and the file loads
on with TRUTH in its place.  With `mark' every phrase also gets a
marker, as tools/locate.py writes them.

The copy is for a harvest only.  Nothing of it goes into ml/.
"""
import sys, re, os

T = os.path.dirname(os.path.abspath(__file__)) + '/'
TMP = T + '../tmp/'

PRELUDE = """let cake_mark s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "%(tmp)smark.txt" in
  output_string ch (s ^ "\\n"); close_out ch;;

let cake_unstated nm e =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "%(tmp)sunstated.txt" in
  output_string ch ("%(file)s\\t" ^ nm ^ "\\t" ^ e ^ "\\n");
  close_out ch;
  print_string ("NOT STATED " ^ nm ^ ": " ^ e ^ "\\n");;
"""

# a theorem of the port, with the `prove' on its line or on the
# next one where the binding is too long for one line
HEAD = re.compile(r"^let ([A-Za-z_][A-Za-z_0-9']*) =\n?\s*prove\n",
                  re.M)


def tolerant(phrase, name):
  """the phrase with its `prove' in a try"""
  body = phrase.rstrip()
  assert body.endswith(';;'), body[-40:]
  body = body[:-2].rstrip()
  body = re.sub(r"^let (%s) =(\n?\s*)prove\n" % re.escape(name),
                r"let \1 =\2try prove\n", body, count=1, flags=re.M)
  return (body + '\n  with e ->\n'
          '    (cake_unstated "%s" (Printexc.to_string e); TRUTH);;'
          % name)


def main():
  src, out = sys.argv[1], sys.argv[2]
  mark = len(sys.argv) > 3 and sys.argv[3] == 'mark'
  text = open(src).read()
  parts = re.split(r'(?<=;;)\n', text)
  res = [PRELUDE % {'tmp': TMP, 'file': src}]
  n = 0
  for p in parts:
    if not p.strip():
      res.append(p); continue
    n += 1
    # the comments of the source stand before the `let', so the
    # head of a theorem is not at the start of the phrase
    m = HEAD.search(p)
    q = tolerant(p, m.group(1)) + '\n' if m else p
    if mark:
      lab = p.strip().split('\n')[0][:60]
      lab = lab.replace('\\', '\\\\').replace('"', "'")
      q = 'cake_mark "%d: %s";;\n%s' % (n, lab, q)
    res.append(q)
  open(out, 'w').write('\n'.join(res))
  print(n)


if __name__ == '__main__':
  main()
