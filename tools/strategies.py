"""how each definition of the port was made

A definition of a source goes through cake_define, which tries one
strategy after another, because no single primitive of HOL Light
takes what HOL4 writes.  Searching for the way again on every load
is both slow and silent about what came out, so a run harvests
what worked and the files say it themselves.

WAY holds it, as (theory, constant) -> (strategy, assumed,
relation): the strategy that made the definition, whether its
termination condition was assumed rather than proved, and the
relation it was made with ('' where there was none).

PRIMITIVE is the constants where the strategy is HOL Light's own
new_definition, which is the common case.

tools/bin/strategies harvests both from a run (cake_strategies).
"""

WAY = {
  ('sptree', 'alist_insert'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (\\n. n) x0)'),
  ('sptree', 'difference'):
    ('prim_rec', False, ''),
  ('sptree', 'domain'):
    ('measure', False, 'MEASURE (\\x0. spt_size (\\x. 0) x0)'),
  ('sptree', 'filter_v'):
    ('prim_rec', False, ''),
  ('sptree', 'foldi'):
    ('prim_rec', False, ''),
  ('sptree', 'fromAList'):
    ('prim_rec', False, ''),
  ('sptree', 'inter'):
    ('prim_rec', False, ''),
  ('sptree', 'inter_eq'):
    ('prim_rec', False, ''),
  ('sptree', 'list_insert'):
    ('prim_rec', False, ''),
  ('sptree', 'list_to_num_set'):
    ('prim_rec', False, ''),
  ('sptree', 'lrnext'):
    ('measure', False, 'MEASURE I'),
  ('sptree', 'mapi0'):
    ('prim_rec', False, ''),
  ('sptree', 'mk_BN'):
    ('new_definition', False, ''),
  ('sptree', 'mk_BS'):
    ('new_definition', False, ''),
  ('sptree', 'mk_wf'):
    ('prim_rec', False, ''),
  ('sptree', 'spt_center'):
    ('new_definition', False, ''),
  ('sptree', 'spt_fold'):
    ('prim_rec', False, ''),
  ('sptree', 'spt_left'):
    ('new_recursive_definition', False, ''),
  ('sptree', 'spt_right'):
    ('new_recursive_definition', False, ''),
  ('sptree', 'sptree_delete'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_fromList'):
    ('new_definition', False, ''),
  ('sptree', 'sptree_insert'):
    ('measure', False, 'MEASURE FST'),
  ('sptree', 'sptree_lookup'):
    ('measure', False, 'MEASURE FST'),
  ('sptree', 'sptree_map'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_mapi'):
    ('new_definition', False, ''),
  ('sptree', 'sptree_size'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_toList'):
    ('new_definition', False, ''),
  ('sptree', 'sptree_union'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_wf'):
    ('prim_rec', False, ''),
  ('sptree', 'spts_to_alist'):
    ('guess', False, ''),
  ('sptree', 'spts_to_alist_add_pause'):
    ('new_definition', False, ''),
  ('sptree', 'spts_to_alist_aux'):
    ('match', False, ''),
  ('sptree', 'subspt'):
    ('prim_rec', False, ''),
  ('sptree', 'toAList'):
    ('new_definition', False, ''),
  ('sptree', 'toListA'):
    ('prim_rec', False, ''),
  ('sptree', 'toSortedAList'):
    ('new_definition', False, ''),
}

PRIMITIVE = {k for k, v in WAY.items() if v[0] == 'new_definition'}
