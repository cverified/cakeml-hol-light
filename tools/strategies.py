"""how each definition of the port was made

A definition of a source went through cake_define, which tried one
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
Until a run has, WAY is empty and tools/port.py writes each
definition the way its shape asks for.
"""

WAY = {}

PRIMITIVE = {k for k, v in WAY.items() if v[0] == 'new_definition'}
