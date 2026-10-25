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

let cake_log_unstated nm e =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "%(tmp)sunstated.txt" in
  output_string ch ("%(file)s\t" ^ nm ^ "\t" ^ e ^ "\n");
  close_out ch;
  print_string ("NOT STATED " ^ nm ^ ": " ^ e ^ "\n");;

(* the statement is read again with the overloads of the record
   fields taken away, here where the file stands: what counts as a
   field overload grows as the port defines its records, so the
   answer of a session that holds the whole port is not the answer
   here *)
let cake_unstated nm mk e =
  (* a statement that reads on its own is one whose proof failed,
     which is not what this harvest is about *)
  (try let _ = mk () in
       cake_log_unstated nm ("PROOF " ^ e)
   with _ ->
     (try let tm = cake_as_vars mk in
          let vs = map (fun v -> fst(dest_var v) ^ " " ^
                                 string_of_type (type_of v))
                       (frees tm) in
          cake_log_unstated nm ("AS_VARS |" ^ String.concat "|" vs)
      with Failure e2 -> cake_log_unstated nm ("NO " ^ e ^ " / " ^ e2)
         | Invalid_argument e2 ->
             cake_log_unstated nm ("NO " ^ e ^ " / " ^ e2)));;

(* the same of a block that reads its statement with the overloads
   taken away already: there the failure is the proof's unless
   even that read does not work, and a statement that reads
   plainly as well does not need the entry at all *)
let cake_unstated_v nm mk e =
  (try let _ = cake_as_vars mk in
       (try let _ = mk () in
            cake_log_unstated nm ("PROOF PLAINOK " ^ e)
        with _ -> cake_log_unstated nm ("PROOF " ^ e))
   with Failure e2 -> cake_log_unstated nm ("NO " ^ e ^ " / " ^ e2)
      | Invalid_argument e2 ->
          cake_log_unstated nm ("NO " ^ e ^ " / " ^ e2));;
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
  # the statement of the block, so that the handler can read it
  # again with the overloads taken away
  m = re.search(r'\(\s*(?:cake_as_vars \(fun \(\) ->\s*)?'
                r'(`.*?`)\s*\)?\s*,', body, re.S)
  stmt = m.group(1) if m else '`T`'
  # the block that reads its statement with the overloads taken
  # away has its own handler
  fn = ('cake_unstated_v' if 'cake_as_vars (fun () ->' in body[:400]
        else 'cake_unstated')
  return (body + '\n  with e ->\n'
          '    (%s "%s" (fun () ->\n%s)\n'
          '       (Printexc.to_string e); TRUTH);;'
          % (fn, name, stmt))


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
