"""a probe of the statements that HOL Light does not read

  python3 -I tools/mkprobe.py <file of the port>... > tmp/probe.ml

For every statement of those files that tmp/unstated.txt says does
not read, this writes the phrases that read it again with the
overloads of the record fields taken away (`cake_as_vars`) and
print its free variables with their types -- which is what
tools/fieldvars.py needs to annotate the statement, and what says
whether the statement can be read at all.

The hiding of the file is applied around its probes, so that a
name the file reads as a variable is one here as well.
"""
import os, re, sys

T = os.path.dirname(os.path.abspath(__file__)) + '/'
ML = T + '../ml/'

PRELUDE = r"""
let cake_probe_log s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
            "/home/freek/claude/hol-light/cakeml/tmp/probeout.txt" in
  output_string ch (s ^ "\n"); close_out ch;;

let cake_probe nm mk =
  try let tm = cake_as_vars mk in
      cake_probe_log
        ("PROBE " ^ nm ^ " |" ^
         String.concat "|"
           (map (fun v -> fst(dest_var v) ^ " " ^
                          string_of_type (type_of v))
                (frees tm)))
  with Failure e -> cake_probe_log ("PROBEFAIL " ^ nm ^ " " ^ e)
     | Invalid_argument e ->
         cake_probe_log ("PROBEFAIL " ^ nm ^ " " ^ e);;
"""


def statements(path, names):
  """the quotation of each named statement of a generated file"""
  text = open(path).read()
  out = []
  for nm in names:
    m = re.search(r"(?m)^let %s =\n?\s*prove\n \(\(?(`.*?`)," % nm,
                  text, re.S)
    if m is None:
      print('no statement of %s in %s' % (nm, path), file=sys.stderr)
      continue
    out.append((nm, m.group(1)))
  return out


def hiding(path):
  """the hide_constant and hide_overloads lines of a file"""
  text = open(path).read()
  hide = re.search(r'let _ = do_list hide_constant \[(.*?)\];;',
                   text, re.S)
  ovl = re.search(r'let _ = hide_overloads\n  \[(.*?)\];;',
                  text, re.S)
  return (hide.group(1) if hide else None,
          ovl.group(1) if ovl else None)


def main():
  bad = {}
  for l in open(T + '../tmp/unstated.txt'):
    p = l.rstrip('\n').split('\t')
    if len(p) < 3 or 'typechecking' not in p[2]: continue
    bad.setdefault(re.sub(r'.*/ml/', '', p[0]), []).append(p[1])
  print(PRELUDE)
  for rel in sys.argv[1:]:
    names = bad.get(rel, [])
    if not names: continue
    hide, ovl = hiding(ML + rel)
    print('(* %s: %d statements *)' % (rel, len(names)))
    if hide: print('let _ = do_list hide_constant [%s];;' % hide)
    if ovl: print('let _ = hide_overloads\n  [%s];;' % ovl)
    for nm, stmt in statements(ML + rel, names):
      print('cake_probe "%s" (fun () ->\n %s);;' % (nm, stmt))
    if ovl: print('let _ = unhide_overloads ();;')
    if hide: print('let _ = do_list unhide_constant [%s];;' % hide)
  print('print_string "PROBEDONE\\n";;')


if __name__ == '__main__':
  main()
