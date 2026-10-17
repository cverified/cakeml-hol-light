"""compare the axioms that the files of the running checkseq add
   with the ones of the last run (ml/TIMINGS.md)"""
import re
old = {}
for l in open('ml/TIMINGS.md'):
  m = re.match(r'\| `([^`]*)` \| ([0-9.]*) \| ([0-9]*) \|', l)
  if m: old[m.group(1)] = (float(m.group(2)), int(m.group(3) or 0))
prev = 3
tot_new = tot_old = 0.0
ax_new = ax_old = 0
for l in open('tmp/cs.out'):
  m = re.match(r'(\S+)\s+\(([0-9.e-]+), *([0-9]+)\)', l)
  if not m: continue
  f, t, ax = m.group(1), float(m.group(2)), int(m.group(3))
  d = ax - prev; prev = ax
  o = old.get(f)
  tot_new += t; ax_new += d
  if o: tot_old += o[0]; ax_old += o[1]
  if o and (d != o[1] or t > o[0] * 2 + 10):
    print('%-46s %5.1f -> %5.1f  %3d -> %3d' % (f, o[0], t, o[1], d))
print('%-46s %5.0f -> %5.0f  %3d -> %3d (%d files)'
      % ('TOTAL', tot_old, tot_new, ax_old, ax_new, len(open(
         'tmp/cs.out').readlines())))
