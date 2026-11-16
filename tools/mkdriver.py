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
import os, sys, io

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
ML = T + '../ml/'

HEAD = '''let cake_t0 = Sys.time();;
let cake_file s =
  print_string ("CAKEFILE " ^ s ^ "\\n"); flush stdout;;
'''

TAIL = '''Printf.printf "DRIVER %.1fs\\n%!" (Sys.time() -. cake_t0);;
'''


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
    real = ML + f
    drv.append('cake_file "%s";;' % f)
    drv.append('loadt "%s";;' % cp)
    drv.append('loaded_files := (Filename.basename "%s",'
               ' Digest.file "%s") :: !loaded_files;;' % (real, real))
  drv.append(TAIL)
  open(out + 'driver.ml', 'w').write('\n'.join(drv) + '\n')
  print('%d files, driver in %sdriver.ml' % (len(files), out))


main()
