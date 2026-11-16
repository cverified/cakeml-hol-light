"""write the whole port's instrumented copies and one file that
   loads them

  python3 -I tools/mkdriver.py <directory>

tools/bin/abstract loads the port a file at a time, and for every
one of the 492 it spawns a python to write the instrumented copy,
sends a line to tmux and polls for the prompt, captures the pane
and spawns another python to read the error out of it.  Measured:
2.76 seconds of HOL Light's processor time per file against 5.8
seconds of elapsed time, so about half of an abstract is the shell
talking to tmux.

This writes every copy in one python and one file that loads them
in order, so that the shell waits once.
"""
import os, re, sys, io

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
# the tree to read the files from: ml/ itself, or the scratch tree
# of a resolution round (CAKE_ML=tmp/res)
ML = os.environ.get('CAKE_ML') or T + '../ml/'
if not ML.endswith('/'): ML += '/'
REAL = T + '../ml/'

HEAD = '''let cake_t0 = Sys.time();;
let cake_file s =
  print_string ("CAKEFILE " ^ s ^ "\\n"); flush stdout;;
'''

TAIL = '''Printf.printf "DRIVER %.1fs\\n%!" (Sys.time() -. cake_t0);;
'''


def unhidden(path):
  """the constants a file hides from the parser, as a phrase that
     unhides them again: a file that dies leaves them hidden and
     the files after it read the names as variables"""
  try:
    text = open(path, encoding='utf-8').read()
  except OSError:
    return ''
  ns = []
  for m in re.finditer(r'hide_constant\s*\[([^]]*)\]', text):
    ns += re.findall(r'"([^"]+)"', m.group(1))
  if not ns: return ''
  return ('do_list unhide_constant [%s];;'
          % '; '.join('"%s"' % n for n in sorted(set(ns))))


def main():
  if not sys.argv[1:]:
    print(__doc__); return
  out = os.path.abspath(sys.argv[1].rstrip('/')) + '/'
  os.makedirs(out, exist_ok=True)
  import tolerant
  files = [l.strip() for l in open(T + 'load.txt') if l.strip()]
  drv = [HEAD]
  keep = sys.stdout
  for i, f in enumerate(files):
    cp = '%sf%04d.ml' % (out, i)
    sys.argv = ['tolerant', ML + f, cp]
    sys.stdout = io.StringIO()
    try:
      tolerant.main()
    finally:
      sys.stdout = keep
    # the digest that stops a `needs' of a later file from
    # loading the real file over the copy is the real file's
    real = REAL + f
    drv.append('cake_file "%s";;' % f)
    drv.append('loadt "%s";;' % cp)
    # a file that dies never reaches its own unhide_overloads, so
    # the interface stays cut down to the scope of that file and
    # every file after it is read in a scope that no report
    # describes: one failure then looks like fifty.  This is what
    # tools/bin/abstract does between two files, and the driver
    # has to do it too or it is not the same abstract
    drv.append('unhide_overloads ();;')
    u = unhidden(ML + f)
    if u: drv.append(u)
    drv.append('loaded_files := (Filename.basename "%s",'
               ' Digest.file "%s") :: !loaded_files;;' % (real, real))
  drv.append(TAIL)
  open(out + 'driver.ml', 'w').write('\n'.join(drv) + '\n')
  print('%d files, driver in %sdriver.ml' % (len(files), out))


main()
