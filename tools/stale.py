"""every entry of an override table still names something of a
   source

  python3 -I tools/stale.py [-v]

`tools/overrides.py` is where the translation says what it cannot
read off a source: a definition that HOL Light cannot make as it
stands, a measure of a termination, a statement that the port
writes out by hand, the record field that a variable of a
statement stands for, and so on.  Every entry is keyed by the
block it is about -- a theory and the name of a block of it -- or
by a theory alone.

An entry whose block is gone from the source is dead: it does
nothing, and the thing the source now says in its place is
ported with no override at all.  That is the one failure a
re-port does not show, because the port is regenerated from the
sources and a dead entry leaves no trace in it.  So when the
sources are a new release of CakeML, this is what says which of
the overrides have to be looked at again.

The test is that the key's name occurs in the text of the
source: a renamed or deleted block takes its name with it.  The
name of a key is the name of the OCaml binding, which lowercases
a capital (`Lnext_def` is keyed `lnext_def`) and which has a
`_def` that the name of a block defined by ML code of the source
has not, so both are allowed for.  A name that the source still
has somewhere else is not caught, so this reports the entries
that are certainly dead, not all of them.  With `-v` every entry
that is checked is listed with the verdict.
"""
import sys, os, re

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import overrides, db as dbmod


def tables():
  """the override tables, by name"""
  out = []
  for n in sorted(dir(overrides)):
    if not n.isupper(): continue
    v = getattr(overrides, n)
    if isinstance(v, (dict, list, set, tuple, frozenset)):
      out.append((n, v))
  return out


def keys_of(table):
  """an entry of a table is a key of a dict or a member of a list"""
  return list(table)


def candidates(name):
  """the names of a source that the porter keys as `name`: it
     lowercases a capital and it adds the `_def` of a block that
     ML code of the source defines"""
  out = [name]
  if name.endswith('_def'): out.append(name[:-4])
  for n in list(out):
    if n[:1].islower(): out.append(n[0].upper() + n[1:])
  return out


def duplicate_keys():
  """a key that a dict literal of tools/overrides.py gives twice:
     Python keeps the last of them and says nothing, so the first
     is dead and the table reads as if it were not.  That is not a
     stale entry but it fails the same way, so it is reported
     here"""
  import ast
  tree = ast.parse(open(T + 'overrides.py').read())
  bad = 0
  for node in ast.walk(tree):
    if not isinstance(node, ast.Dict): continue
    name = '?'
    for a in ast.walk(tree):
      if isinstance(a, ast.Assign) and a.value is node:
        name = getattr(a.targets[0], 'id', '?')
    seen = {}
    for k in node.keys:
      if k is None: continue
      try: v = ast.literal_eval(k)
      except Exception: continue
      if v in seen:
        bad += 1
        print('%s: the key %r is given twice (lines %d and %d);'
              ' the first is dead'
              % (name, v, seen[v], k.lineno))
      seen[v] = k.lineno
  return bad


# what each table's entries look like, so that an entry put in
# the wrong one is caught: CON_OF and its neighbours take a name
# to a theory, DEF_PATCH and THM_PATCH a list of replacements.
# The two take the same key, and a dict in a patch table (or a
# list of pairs in a resolution table) does nothing at all
SHAPES = {
  'CON_OF': dict, 'CON_FILE': dict, 'CON_BODY': dict,
  'CON_CLAUSE': dict, 'DEF_NAMES': dict, 'THM_NAMES': dict,
  'FIELD_OF': dict, 'FIELD_VAR': dict, 'FIELD_VAR_DEF': dict,
  'ARG_TYPES': dict, 'ACCESSORS': dict, 'UPDATERS': dict,
  'DEF_PATCH': list, 'THM_PATCH': list,
}


def wrong_shape():
  """an entry whose value is of the shape another table takes"""
  bad = 0
  for name, want in SHAPES.items():
    t = getattr(overrides, name, None)
    if not isinstance(t, dict): continue
    for k, v in t.items():
      if isinstance(v, want): continue
      bad += 1
      print('%s: the entry %r is a %s where the table takes a %s'
            % (name, k, type(v).__name__, want.__name__))
  return bad


def main():
  verbose = '-v' in sys.argv[1:]
  src = {}
  for thy, path, kind in dbmod.load_order():
    src[thy] = open(path, encoding='utf8', errors='replace').read()
  n = block = thy_only = other = dead = 0
  for name, table in tables():
    for k in keys_of(table):
      n += 1
      if (isinstance(k, tuple) and len(k) == 2 and
          isinstance(k[0], str) and isinstance(k[1], str) and
          k[0] in src):
        block += 1
        ok = any(re.search(r'(?<![A-Za-z0-9_\'])%s'
                           r'(?![A-Za-z0-9_\'])' % re.escape(c),
                           src[k[0]])
                 for c in candidates(k[1]))
        if not ok:
          dead += 1
          print('%s: %s has no %s' % (name, k[0], k[1]))
        elif verbose:
          print('%s: %s %s ok' % (name, k[0], k[1]))
      elif isinstance(k, str) and k in src:
        thy_only += 1
        if verbose: print('%s: %s ok' % (name, k))
      else:
        other += 1
        if verbose: print('%s: %s not placed' % (name, k))
  print('%d entries in %d override tables of tools/overrides.py'
        % (n, len(tables())))
  print('%d of them name a block of a source, %d of which the '
        'source has not' % (block, dead))
  print('%d name a theory of the port, %d name something that the '
        'check cannot place' % (thy_only, other))
  dup = duplicate_keys()
  print('%d keys that a table gives twice' % dup)
  print('%d entries of a shape their table does not take'
        % wrong_shape())


if __name__ == '__main__':
  main()
