"""the statements of the sources that HOL Light does not read

A theorem of the port is a plain `let foo = prove (`...`, tac);;`,
so a statement that HOL Light's parser rejects is an error of the
file and nothing after it loads.  The port cannot know which ones
those are by reading the source -- only HOL Light's parser says --
so the names are harvested from a run:

  tools/bin/harvestall          loads the whole port with every
                                theorem in a try and writes
                                tmp/unstated.txt
  python3 -I tools/mkunstated.py > tools/unstated.py

and where a name is in this table the port writes the comment that
points at the source in the place of the theorem, which is what it
does for a statement its own parser cannot read.

Every entry is a statement to win back: the port then states one
theorem more.  NAMES is keyed by (theory, the name of the source).
"""

NAMES = set([
])
