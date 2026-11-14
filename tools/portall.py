"""port every theory of the load order (the HOL4 library theories
   of ml/lib as well) into ml/"""
import sys, os, re, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import db as dbmod, port as portmod

portmod.check_no_run()
db = dbmod.Db()


def reserved():
  """the names that the port gives constants of its own and that
     the library must not invent for a size function: the size
     function of a datatype is made where the type is, before the
     theory's own constants are there, and balanced_map's size and
     the size field of panLang's struct_info are names of the
     theory (ml/lib/define.ml, cake_reserved)"""
  out = set()
  for nm, v in db.defs.items():
    for t, _ in v:
      n = db.rename.get((t, nm), nm)
      if re.search(r'_size[0-9]*$', n): out.add(n)
  for (t, ty), (_, flds) in db.datatypes.items():
    for f in flds:
      n = db.rename.get((t, ty), ty) + '_' + f
      if re.search(r'_size[0-9]*$', n): out.add(n)
  bar = '(* ' + '=' * 66 + ' *)'
  lines = [
    'The names that the port gives constants of its own and that',
    'the library must not invent for a size function.  The size',
    'function of a datatype is made where the type is, before the',
    "theory's own constants are there, and balanced_map's size and",
    "the size field of panLang's struct_info are names of the",
    'theory (ml/lib/define.ml, cake_reserved).',
    '',
    'tools/portall.py writes this file.']
  text = [bar] + ['(*  ' + l.ljust(62) + '*)' for l in lines] + \
         [bar, '', 'cake_reserved :=']
  for i, n in enumerate(sorted(out)):
    text.append('  %s"%s"%s' % ('[' if i == 0 else ' ', n,
                                ';' if i < len(out) - 1 else '];;'))
  open('ml/lib/reserved.ml', 'w').write('\n'.join(text) + '\n')
  return len(out)


nres = reserved()
t0 = time.time()
n = bad = 0
T = os.path.dirname(os.path.abspath(__file__))
# every doubt that the translation of a theory has, so that the
# whole port's are in one place (tools/warnings.txt)
out = open(T + '/warnings.txt', 'w')
kinds = {}
for thy, path, kind in dbmod.load_order():
  p, warn, amb = portmod.port(thy, db)
  n += 1
  k = open(p).read().count('PORT FAILED')
  bad += k
  if k: print('%-24s %d PORT FAILED' % (thy, k))
  for w in warn:
    out.write('%s\t%s\n' % (thy, w.replace('\n', ' ')))
    key = re.sub(r'[^a-z ].*', '', w.split(':')[0]).strip() or w[:20]
    kinds[key] = kinds.get(key, 0) + 1
out.close()
# the preface of a file says which files need it, which is only
# known when every file has its needs
import preface
preface.main()
print(n, 'files,', bad, 'PORT FAILED, %.1fs, %d names reserved'
      % (time.time() - t0, nres))
print('warnings in tools/warnings.txt:')
for k, v in sorted(kinds.items(), key=lambda kv: -kv[1])[:12]:
  print('%6d  %s' % (v, k))
