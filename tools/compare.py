"""a local page per theory, the three ports side by side

  python3 -I tools/compare.py [directory]

writes an index and one page per theory into <directory> (compare/
by default): HOL4's source, this port, and LightCake's where it has
one.  It is for reading, so it is plain static HTML -- no server, no
fetch, each page carries its own three files.

The three panes scroll together on the names of the blocks: both
ports keep HOL4's name for a theorem, so the page reads the names
off all three files and scrolls the others to the block that the
one being scrolled is showing.  Any column can be hidden.

LightCake is somebody else's private repository: these pages stay on
this machine.
"""
import sys, os, html, re, json

T = os.path.dirname(os.path.abspath(__file__)) + '/'
sys.path.insert(0, T)
import db as dbmod, lightcake as L

# a handful that read differently from one another, for a first look
SHORT = [
  ('data_to_word_memoryProof',
   'a proof theory with its proofs filled in: 611 of them'),
  ('dataSem', 'a semantics: records, a state, a big match'),
  ('bvl_to_bvi', 'a compiler pass: nested matches and app_lists'),
  ('sptree', 'a library theory, its proofs taken from LightCake'),
  ('misc', 'the 380 small lemmas that everything uses'),
  ('cmlPEG', 'a parser written as a PEG'),
  ('flatLang', 'a plain datatype theory, nothing but definitions'),
  ('gen_gc', 'a garbage collector, proofs part filled'),
]

HOL4_AT = re.compile(
  r"^(?:Theorem|Triviality|Definition|Inductive|Type|Overload)\s+"
  r"([A-Za-z0-9_']+)")
TY_AT = re.compile(r"^\s+([A-Za-z0-9_']+)\s*=")
ML_AT = re.compile(r"^let\s+([A-Za-z0-9_']+)")
CMT_AT = re.compile(r"^\(\* ([A-Za-z0-9_']+)(?:\[[^\]]*\])? \*\)\s*$")


def key(n, thy):
  """the name as the other ports write it: both of them keep HOL4's
     name, with the theory in front of it where something else has
     the name, and _def or _ind after it for a definition"""
  n = n.lower()
  t = thy.lower() + '_'
  if n.startswith(t): n = n[len(t):]
  for suf in ('_recursion', '_induct', '_def', '_ind', '_thm', "'"):
    if n.endswith(suf): return n[:-len(suf)]
  return n


def anchors(ls, thy, hol4):
  """where each named block starts, by that name"""
  if ls is None: return []
  out, seen = [], set()
  for i, l in enumerate(ls):
    if hol4:
      m = HOL4_AT.match(l)
      if not m and l.rstrip() == 'Datatype:':
        m = TY_AT.match(ls[i + 1]) if i + 1 < len(ls) else None
    else:
      m = ML_AT.match(l) or CMT_AT.match(l)
    if not m: continue
    k = key(m.group(1), thy)
    if not k or k in seen or k.startswith('_'): continue
    seen.add(k)
    out.append([k, i])
  return out


def lines(path):
  if not path or not os.path.exists(path): return None
  s = open(path, encoding='utf-8', errors='replace').read()
  return s.split('\n')


def pane(title, sub, ls):
  if ls is None:
    return ('<div class=pane><h2><b>%s</b><small>not in this port'
            '</small></h2><pre class=empty>&mdash;</pre></div>'
            % html.escape(title))
  out = ['<div class=pane><h2><b>%s</b><small>%s &middot; %d lines'
         '</small></h2><pre>'
         % (html.escape(title), html.escape(sub), len(ls))]
  for i, l in enumerate(ls):
    out.append('<span class=ln>%4d</span>%s\n'
               % (i + 1, html.escape(l)))
  out.append('</pre></div>')
  return ''.join(out)


CSS = """
:root{--bg:#fbfbfa;--fg:#1a1a18;--dim:#6b6b66;--line:#e2e2dd;
      --head:#fff;--ln:#b9b9b2}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){
  --bg:#17171a;--fg:#e8e8e4;--dim:#9a9a93;--line:#2c2c30;
  --head:#1f1f23;--ln:#55555c}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);
     font:14px/1.5 ui-sans-serif,system-ui,sans-serif}
header{background:var(--head);border-bottom:1px solid var(--line);
       padding:8px 16px;display:flex;gap:14px;align-items:center;
       flex-wrap:wrap}
header h1{font-size:15px;margin:0;font-weight:600}
header a{color:var(--dim);text-decoration:none}
header a:hover{color:var(--fg)}
.tog{margin-left:auto;display:flex;gap:12px;align-items:center;
     font-size:12px;color:var(--dim)}
.tog label{display:flex;gap:4px;align-items:center;cursor:pointer}
.tog input{margin:0;cursor:pointer}
body.cmp{height:100vh;display:flex;flex-direction:column;
         overflow:hidden}
.cols{display:flex;gap:1px;background:var(--line);flex:1;
      min-height:0}
.pane{background:var(--bg);min-width:0;flex:1 1 0;display:flex;
      flex-direction:column}
.pane h2{font-size:12px;font-weight:400;margin:0;padding:7px 12px;
         border-bottom:1px solid var(--line);color:var(--dim);
         background:var(--head);display:flex;
         justify-content:space-between;gap:8px}
.pane h2 b{color:var(--fg);font-weight:600}
pre{margin:0;padding:8px 12px 60vh;overflow:auto;flex:1;
    font:12px/1.45 ui-monospace,SFMono-Regular,Menlo,monospace;
    white-space:pre;tab-size:2}
pre.empty{color:var(--dim);padding:16px}
.ln{display:inline-block;width:3.5em;margin-right:.8em;
    color:var(--ln);text-align:right;user-select:none}
ul{list-style:none;margin:0;padding:0}
li{border-bottom:1px solid var(--line)}
li a{display:flex;gap:12px;padding:9px 16px;text-decoration:none;
     color:var(--fg);align-items:baseline}
li a:hover{background:var(--head)}
li .nm{font:13px ui-monospace,monospace;min-width:20em}
li .why{color:var(--dim);font-size:13px}
li .tag{color:var(--ln);font-size:12px;margin-left:auto}
.wrap{max-width:62em;margin:0 auto;padding:24px 0 80px}
h3{font-size:13px;color:var(--dim);margin:28px 16px 8px;
   font-weight:600;letter-spacing:.04em;text-transform:uppercase}
p.note{color:var(--dim);margin:8px 16px 0;font-size:13px}
"""

JS = r"""
(function(){
var cols = document.querySelector('.cols');
var panes = [].slice.call(cols.children);
var pres = panes.map(function(p){ return p.querySelector('pre') });
var maps = A.map(function(a){
  var m = {};
  for (var i = 0; i < a.length; i++) m[a[i][0]] = i;
  return m;
});
var sync = document.getElementById('sync');
var boxes = [].slice.call(document.querySelectorAll('[data-col]'));

function get(k, d){
  try { var v = localStorage.getItem(k);
        return v === null ? d : v === '1' } catch(e) { return d }
}
function put(k, v){
  try { localStorage.setItem(k, v ? '1' : '0') } catch(e) {}
}
function shown(i){ return panes[i].style.display !== 'none' }
function show(i, on){
  panes[i].style.display = on ? '' : 'none';
  put('col' + i, on);
}
boxes.forEach(function(b){
  var i = +b.getAttribute('data-col');
  b.checked = get('col' + i, true);
  show(i, b.checked);
  b.addEventListener('change', function(){
    show(i, b.checked);
    var j = first();
    if (j >= 0) spread(j);
  });
});
sync.checked = get('sync', true);
sync.addEventListener('change', function(){ put('sync', sync.checked) });
document.addEventListener('keydown', function(e){
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  var i = '123'.indexOf(e.key);
  if (i < 0) return;
  var b = boxes[i];
  if (!b) return;
  b.checked = !b.checked;
  show(i, b.checked);
  var j = first();
  if (j >= 0) spread(j);
});
function first(){
  for (var i = 0; i < panes.length; i++) if (shown(i)) return i;
  return -1;
}
function metric(p){
  var cs = getComputedStyle(p);
  return [parseFloat(cs.lineHeight) || 17,
          parseFloat(cs.paddingTop) || 0];
}
function topline(i){
  var m = metric(pres[i]);
  return (pres[i].scrollTop - m[1]) / m[0];
}
function goto_(i, line){
  var m = metric(pres[i]);
  pres[i].scrollTop = Math.max(0, line * m[0] + m[1]);
}
function prop(s, t){
  var a = pres[s], b = pres[t];
  var m = a.scrollHeight - a.clientHeight;
  b.scrollTop = (m > 0 ? a.scrollTop / m : 0) *
                (b.scrollHeight - b.clientHeight);
}
function map(s, t, line){
  var a = A[s], b = A[t], ms = maps[t];
  if (!a.length || !b.length) return null;
  if (line < a[0][1])
    return line * (b[0][1] + 1) / (a[0][1] + 1);
  var j = -1, jt = -1, k;
  for (k = 0; k < a.length; k++){
    if (a[k][1] > line) break;
    if (ms.hasOwnProperty(a[k][0])) { j = k; jt = ms[a[k][0]] }
  }
  if (j < 0) return null;
  var n = -1, nt = -1;
  for (k = j + 1; k < a.length; k++)
    if (ms.hasOwnProperty(a[k][0]) && ms[a[k][0]] > jt) {
      n = k; nt = ms[a[k][0]]; break;
    }
  var base = b[jt][1];
  if (n < 0) return base + (line - a[j][1]);
  var da = a[n][1] - a[j][1], db = b[nt][1] - base;
  if (da <= 0) return base;
  return base + (line - a[j][1]) * db / da;
}
function spread(s){
  var line = topline(s);
  for (var t = 0; t < pres.length; t++){
    if (t === s || !shown(t)) continue;
    var y = map(s, t, line);
    if (y === null) prop(s, t); else goto_(t, y);
  }
}
var lock = 0;
pres.forEach(function(p, i){
  p.addEventListener('scroll', function(){
    if (lock || !sync.checked || !shown(i)) return;
    lock = 1;
    spread(i);
    requestAnimationFrame(function(){ lock = 0 });
  });
});
})();
"""


def page(thy, hol4, ours, theirs, out):
  ls = [lines(hol4), lines(ours), lines(theirs)]
  a = [anchors(ls[0], thy, True), anchors(ls[1], thy, False),
       anchors(ls[2], thy, False)]
  body = ['<!doctype html><html lang=en><meta charset=utf-8>',
          '<meta name=viewport content="width=device-width,'
          'initial-scale=1">',
          '<title>%s</title><style>%s</style>' % (html.escape(thy), CSS),
          '<body class=cmp>',
          '<header><h1>%s</h1><a href="index.html">&larr; all '
          'theories</a><span class=tog>' % html.escape(thy)]
  for i, nm in enumerate(('HOL4', 'this port', 'LightCake')):
    body.append('<label><input type=checkbox data-col=%d> %s'
                '</label>' % (i, nm))
  body += ['<label><input type=checkbox id=sync> scroll together'
           '</label></span></header>',
           '<div class=cols>',
           pane('HOL4', 'cakeml-src', ls[0]),
           pane('this port', 'ml', ls[1]),
           pane('LightCake', 'lightcake-src', ls[2]),
           '</div>',
           '<script>var A=%s;%s</script></html>'
           % (json.dumps(a, separators=(',', ':')), JS)]
  open(out, 'w', encoding='utf-8').write(''.join(body))


def main():
  d = sys.argv[1] if len(sys.argv) > 1 else T + '../compare'
  d = os.path.abspath(d)
  os.makedirs(d, exist_ok=True)
  rows = []
  for thy, path, kind in dbmod.load_order():
    ours, theirs = L.ours_of(thy), L.theirs_of(thy)
    page(thy, path, ours, theirs, os.path.join(d, thy + '.html'))
    rows.append((thy, kind, ours is not None, theirs is not None))
  byname = dict((r[0], r) for r in rows)

  def item(thy, why=''):
    r = byname.get(thy)
    if not r: return ''
    tag = 'HOL4 + port' + (' + LightCake' if r[3] else '')
    return ('<li><a href="%s.html"><span class=nm>%s</span>'
            '<span class=why>%s</span>'
            '<span class=tag>%s</span></a></li>'
            % (html.escape(thy), html.escape(thy), html.escape(why),
               tag))

  out = ['<!doctype html><html lang=en><meta charset=utf-8>',
         '<meta name=viewport content="width=device-width,'
         'initial-scale=1">',
         '<title>CakeML, three ports</title><style>%s</style>' % CSS,
         '<header><h1>CakeML, three ports side by side</h1></header>',
         '<div class=wrap>',
         '<p class=note>HOL4’s source, this port, and '
         'LightCake’s where it has the theory. %d theories, '
         '%d of them in all three. The panes scroll together on the '
         'names of the blocks; 1, 2 and 3 hide a column.</p>'
         % (len(rows), len([r for r in rows if r[3]])),
         '<h3>A first look</h3><ul>']
  out += [item(t, w) for t, w in SHORT]
  out.append('</ul><h3>Every theory</h3><ul>')
  out += [item(t) for t, _, _, _ in rows]
  out.append('</ul></div></html>')
  open(os.path.join(d, 'index.html'), 'w',
       encoding='utf-8').write(''.join(out))
  print('%d pages in %s' % (len(rows) + 1, d))


if __name__ == '__main__':
  main()
