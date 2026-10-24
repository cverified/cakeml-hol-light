"""which HOL Light primitive each definition of the port needs

A definition of a source goes through cake_define, which tries one
strategy after another, because no single primitive of HOL Light
takes what HOL4 writes.  Where the first strategy -- HOL Light's
own new_definition -- is the one that works, the file says that
primitive itself.

PRIMITIVE holds the constants where it does, as (theory, constant).
tools/bin/strategies harvests it from a run (cake_strategies).
"""

PRIMITIVE = set()
