/-!
# 依存グラフの閲覧用 HTML の固定テンプレート(IDEAL.md C65 / C67)

`naru deps` が `deps.json` の本文を `{{DATA}}`(`<script type="application/json">` の中)に、先頭のコメント(C64 のヘッダ)を `{{HEADER}}` に
入れて `index.html` にする。単一ファイルで自己完結: 外部への読み込み(CDN・Web フォント・`fetch`)を持たず `file://` で開いても動く。
乱数・時刻は使わない(描画は埋め込んだデータだけから決定的に行う)。ライトとダークの両テーマ(`prefers-color-scheme`)。

表示するもの(C67):
- ファイル単位タブ: 縦向きの層状グラフ(層 0 が最上段。層の中はモジュールの並び順)。既定は推移簡約した辺だけを描き、切替で全辺。ファイルを選ぶと
  使う側(出る辺)と使われる側(入る辺)を色分けで強調し(選んだファイルの直接の辺は簡約で省かれていても描く)、横のパネルに宣言数(種類別)・使うファイルと
  使われるファイル(辺の本数と「宣言 → 宣言」の内訳、import 行に無い参照の印)・参照の無い import を出す。色はグループ別、各ファイルに宣言数。
- 宣言単位タブ: 宣言名と種類で絞り込める一覧(ファイルごと)、選んだ宣言の種類・モジュール・`ファイル:行`・要旨、「この宣言が使う」「この宣言を使う」の
  ファイルごとのまとめ(直接 / 推移的の切替。推移的なときは距離 2 以上を区別)。宣言をクリックするとその宣言に移り、ファイル単位タブから移れる。
- 統計: ファイル数・宣言数・宣言間の辺・うちファイルを跨ぐもの・ファイル間の辺・推移簡約後の辺・層の数(生成側の `stats`)。

データ(宣言・辺・層・推移簡約・import との差)はすべて Lean の生成側(`Deps.lean`)が作り、ここではレイアウト(層の中の並び・座標)だけを決める。
-/

namespace Naru.Deps

def template : String := r##"{{HEADER}}<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>naru 依存グラフ</title>
<style>
:root { --bg: #ffffff; --fg: #1b1b1b; --muted: #666666; --panel: #f5f6f8; --border: #d8dbe0; --edge: #a0a4ab; --out: #1f6fd0; --in: #d9731a; --sel: #111111; --node-text: #111111; --accent: #2a62b8; }
@media (prefers-color-scheme: dark) {
  :root { --bg: #141518; --fg: #e6e6e6; --muted: #a3a7ad; --panel: #1d1f24; --border: #3a3d45; --edge: #6d717a; --out: #6fb0f5; --in: #f2a35e; --sel: #ffffff; --node-text: #101010; --accent: #8ab8ff; }
}
* { box-sizing: border-box; }
html, body { margin: 0; padding: 0; background: var(--bg); color: var(--fg); font: 14px/1.45 -apple-system, "Helvetica Neue", "Hiragino Sans", "Noto Sans JP", sans-serif; }
header { padding: 10px 16px; border-bottom: 1px solid var(--border); display: flex; flex-wrap: wrap; align-items: baseline; gap: 8px 20px; }
header h1 { font-size: 18px; margin: 0; }
#stats { color: var(--muted); font-size: 13px; }
#stats b { color: var(--fg); font-weight: 600; }
nav button { font: inherit; padding: 4px 12px; border: 1px solid var(--border); background: var(--panel); color: var(--fg); cursor: pointer; }
nav button.active { background: var(--accent); color: #fff; border-color: var(--accent); }
main { padding: 10px 16px; }
.controls { display: flex; flex-wrap: wrap; gap: 8px 18px; align-items: center; margin-bottom: 8px; color: var(--muted); }
.controls input[type=text], .controls select { font: inherit; padding: 3px 6px; background: var(--bg); color: var(--fg); border: 1px solid var(--border); }
.legend span { display: inline-block; width: 12px; height: 12px; vertical-align: -1px; margin-right: 4px; border-radius: 2px; }
.split { display: grid; grid-template-columns: minmax(0, 1fr) 380px; gap: 12px; }
#graph-wrap { overflow: auto; border: 1px solid var(--border); background: var(--bg); max-height: calc(100vh - 150px); }
#decl-list { overflow: auto; border: 1px solid var(--border); max-height: calc(100vh - 150px); padding: 6px 10px; }
aside { border: 1px solid var(--border); background: var(--panel); padding: 10px 12px; overflow: auto; max-height: calc(100vh - 150px); font-size: 13px; }
aside h2 { font-size: 15px; margin: 0 0 6px 0; word-break: break-all; }
aside h3 { font-size: 13px; margin: 12px 0 4px 0; color: var(--muted); font-weight: 600; }
aside ul { margin: 0; padding-left: 18px; }
aside li { margin: 2px 0; }
.muted { color: var(--muted); }
.flag { color: var(--in); font-weight: 600; }
.link { color: var(--accent); cursor: pointer; text-decoration: underline dotted; }
.dist { color: var(--muted); font-size: 12px; }
.kind { color: var(--muted); font-size: 12px; margin-right: 4px; }
.mod-head { font-weight: 600; margin: 8px 0 2px 0; word-break: break-all; }
.decl-item { padding: 1px 4px; cursor: pointer; word-break: break-all; }
.decl-item:hover { background: var(--panel); }
.decl-item.selected { background: var(--accent); color: #fff; }
.decl-item.selected .kind { color: #e8e8e8; }
svg text { font: 12px ui-monospace, "SF Mono", Menlo, Consolas, monospace; fill: var(--node-text); pointer-events: none; }
svg text.count { font-size: 11px; }
svg .node rect { stroke: rgba(0,0,0,0.35); stroke-width: 1; cursor: pointer; }
svg .node.selected rect { stroke: var(--sel); stroke-width: 3; }
svg .node.related rect { stroke: var(--sel); stroke-width: 2; }
svg .edge { fill: none; stroke: var(--edge); stroke-width: 1.2; opacity: 0.85; }
svg .edge.out { stroke: var(--out); stroke-width: 2.4; opacity: 1; }
svg .edge.in { stroke: var(--in); stroke-width: 2.4; opacity: 1; }
svg .edge.dim { opacity: 0.18; }
svg .edge.extra { stroke-dasharray: 5 4; }
svg .layer-label { fill: var(--muted); font-size: 11px; }
#arrow-edge path { fill: var(--edge); }
#arrow-out path { fill: var(--out); }
#arrow-in path { fill: var(--in); }
svg .layer-line { stroke: var(--border); stroke-width: 1; stroke-dasharray: 3 5; }
button.small { font: inherit; font-size: 12px; padding: 2px 8px; border: 1px solid var(--border); background: var(--bg); color: var(--fg); cursor: pointer; }
</style>
</head>
<body>
<header>
  <h1>naru 依存グラフ</h1>
  <nav><button data-tab="files" class="active">ファイル単位</button><button data-tab="decls">宣言単位</button></nav>
  <div id="stats"></div>
</header>
<main>
<section id="tab-files">
  <div class="controls">
    <label><input type="checkbox" id="all-edges"> 全辺を描く(既定は推移簡約した辺だけ。選んだファイルの直接の辺は点線で描く)</label>
    <span class="legend"><span style="background: var(--out)"></span>選んだファイルが使う <span style="background: var(--in)"></span>選んだファイルを使う</span>
    <span id="group-legend" class="legend"></span>
  </div>
  <div class="split">
    <div id="graph-wrap"><svg id="graph" xmlns="http://www.w3.org/2000/svg"></svg></div>
    <aside id="file-panel"><span class="muted">ファイル(節点)をクリックすると、宣言数・使うファイル・使われるファイル・import との差をここに出す。上ほど層の番号が小さく、層 0(他のファイルに依存しない)が最上段。矢印は使う側から使われる側へ。</span></aside>
  </div>
</section>
<section id="tab-decls" hidden>
  <div class="controls">
    <input type="text" id="decl-filter" placeholder="宣言名で絞り込む" size="32">
    <select id="kind-filter"><option value="">すべての種類</option></select>
    <label><input type="checkbox" id="transitive"> 推移的(距離 2 以上を区別して表示)</label>
    <span id="decl-count" class="muted"></span>
  </div>
  <div class="split">
    <div id="decl-list"></div>
    <aside id="decl-panel"><span class="muted">宣言をクリックすると、種類・モジュール・ファイル:行・要旨と、この宣言が使う / この宣言を使う宣言(ファイルごと)をここに出す。</span></aside>
  </div>
</section>
</main>
<script id="deps-data" type="application/json">{{DATA}}</script>
<script>
'use strict';
(function () {
  var DATA = JSON.parse(document.getElementById('deps-data').textContent);
  var modules = DATA.modules, decls = DATA.decls, declEdges = DATA.declEdges, fileEdges = DATA.fileEdges;
  var modIndex = new Map(), declIndex = new Map();
  modules.forEach(function (m, i) { modIndex.set(m.name, i); });
  decls.forEach(function (d, i) { declIndex.set(d.name, i); });
  var declsByModule = modules.map(function () { return []; });
  decls.forEach(function (d, i) { declsByModule[modIndex.get(d.module)].push(i); });
  var declOut = decls.map(function () { return []; }), declIn = decls.map(function () { return []; });
  declEdges.forEach(function (e, k) { declOut[declIndex.get(e.from)].push(k); declIn[declIndex.get(e.to)].push(k); });
  var fileOut = modules.map(function () { return []; }), fileIn = modules.map(function () { return []; });
  fileEdges.forEach(function (e, k) { fileOut[modIndex.get(e.from)].push(k); fileIn[modIndex.get(e.to)].push(k); });
  var reducedSet = new Set(DATA.reducedEdges.map(function (e) { return e.from + ' -> ' + e.to; }));
  var groups = Array.from(new Set(modules.map(function (m) { return m.group; }))).sort();
  var palette = ['#8ecae6', '#ffd166', '#b5e48c', '#f4a5ae', '#cdb4f8', '#ffb86b', '#9ad0c2', '#f5c6e0', '#c7d2fe', '#d9c7a8', '#a8dadc', '#e9e2a6'];
  function groupColor(g) { return palette[groups.indexOf(g) % palette.length]; }
  var kinds = Array.from(new Set(decls.map(function (d) { return d.kind; })));
  var kindOrder = ['type', 'record', 'state', 'enum', 'input', 'fn', 'protocol', 'observer', 'scenario', 'predicate', 'condition', 'regime', 'property', 'claim', 'claim bundle'];
  kinds.sort(function (a, b) { return kindOrder.indexOf(a) - kindOrder.indexOf(b); });
  function shortName(q) { var i = q.lastIndexOf('.'); return i < 0 ? q : q.slice(i + 1); }
  function declLabel(d) { var m = d.module; return d.name.indexOf(m + '.') === 0 ? d.name.slice(m.length + 1) : d.name; }

  function el(tag, attrs, children) {
    var e = document.createElement(tag);
    if (attrs) Object.keys(attrs).forEach(function (k) {
      if (k === 'class') e.className = attrs[k];
      else if (k === 'onclick') e.addEventListener('click', attrs[k]);
      else e.setAttribute(k, attrs[k]);
    });
    (children || []).forEach(function (c) { e.appendChild(typeof c === 'string' ? document.createTextNode(c) : c); });
    return e;
  }
  function svgEl(tag, attrs) {
    var e = document.createElementNS('http://www.w3.org/2000/svg', tag);
    Object.keys(attrs || {}).forEach(function (k) { e.setAttribute(k, attrs[k]); });
    return e;
  }
  function clear(node) { while (node.firstChild) node.removeChild(node.firstChild); }

  // 統計
  var s = DATA.stats;
  var stats = document.getElementById('stats');
  [['ファイル', s.files], ['宣言', s.decls], ['宣言間の辺', s.declEdges], ['うちファイルを跨ぐもの', s.declEdgesAcrossFiles], ['ファイル間の辺', s.fileEdges], ['推移簡約後の辺', s.reducedEdges], ['層', s.layers]].forEach(function (p, i) {
    if (i > 0) stats.appendChild(document.createTextNode(' · '));
    stats.appendChild(document.createTextNode(p[0] + ' '));
    stats.appendChild(el('b', null, [String(p[1])]));
  });

  // タブ
  var tabs = document.querySelectorAll('nav button');
  function showTab(name) {
    tabs.forEach(function (b) { b.classList.toggle('active', b.getAttribute('data-tab') === name); });
    document.getElementById('tab-files').hidden = name !== 'files';
    document.getElementById('tab-decls').hidden = name !== 'decls';
  }
  tabs.forEach(function (b) { b.addEventListener('click', function () { showTab(b.getAttribute('data-tab')); }); });

  // ファイル単位: 層状のレイアウト(層 0 が最上段。層の中はモジュールの並び順)
  var selectedFile = null;
  var maxLayer = modules.reduce(function (a, m) { return Math.max(a, m.layer); }, 0);
  var rows = [];
  for (var L = 0; L <= maxLayer; L++) rows.push([]);
  modules.forEach(function (m, i) { rows[m.layer].push(i); });
  var charW = 7.3, padX = 14, nodeH = 40, gapX = 26, rowH = 120, marginX = 70, marginY = 30;
  var pos = modules.map(function () { return null; });
  var svgW = 0;
  rows.forEach(function (row, L) {
    var x = marginX;
    row.forEach(function (i) {
      var w = Math.max(110, Math.round(modules[i].name.length * charW) + 2 * padX);
      pos[i] = { x: x, y: marginY + L * rowH, w: w, h: nodeH };
      x += w + gapX;
    });
    svgW = Math.max(svgW, x - gapX + marginX);
  });
  var svgH = marginY + (maxLayer + 1) * rowH;
  var svg = document.getElementById('graph');
  svg.setAttribute('width', svgW);
  svg.setAttribute('height', svgH);
  svg.setAttribute('viewBox', '0 0 ' + svgW + ' ' + svgH);
  var defs = svgEl('defs');
  ['edge', 'out', 'in'].forEach(function (name) {
    var marker = svgEl('marker', { id: 'arrow-' + name, viewBox: '0 0 10 10', refX: '9', refY: '5', markerWidth: '7', markerHeight: '7', orient: 'auto-start-reverse' });
    var path = svgEl('path', { d: 'M 0 0 L 10 5 L 0 10 z' });
    marker.appendChild(path);
    defs.appendChild(marker);
  });
  svg.appendChild(defs);
  var layerGroup = svgEl('g'), edgeGroup = svgEl('g'), nodeGroup = svgEl('g');
  svg.appendChild(layerGroup); svg.appendChild(edgeGroup); svg.appendChild(nodeGroup);
  rows.forEach(function (row, L) {
    var y = marginY + L * rowH + nodeH / 2;
    layerGroup.appendChild(svgEl('line', { 'class': 'layer-line', x1: 8, y1: y, x2: svgW - 8, y2: y }));
    var t = svgEl('text', { 'class': 'layer-label', x: 8, y: y - 6 });
    t.textContent = '層 ' + L;
    layerGroup.appendChild(t);
  });
  var cycleMembers = modules.map(function (m) { return DATA.components[m.component]; });
  modules.forEach(function (m, i) {
    var p = pos[i];
    var g = svgEl('g', { 'class': 'node' });
    g.setAttribute('data-module', String(i));
    var rect = svgEl('rect', { x: p.x, y: p.y, width: p.w, height: p.h, rx: 6, ry: 6 });
    rect.setAttribute('fill', groupColor(m.group));
    g.appendChild(rect);
    var t1 = svgEl('text', { x: p.x + p.w / 2, y: p.y + 17, 'text-anchor': 'middle' });
    t1.textContent = m.name;
    g.appendChild(t1);
    var t2 = svgEl('text', { 'class': 'count', x: p.x + p.w / 2, y: p.y + 32, 'text-anchor': 'middle' });
    t2.textContent = declsByModule[i].length + ' 宣言' + (cycleMembers[i].length > 1 ? ' · 循環' : '');
    g.appendChild(t2);
    g.addEventListener('click', function () { selectFile(i); });
    nodeGroup.appendChild(g);
  });
  function edgePath(a, b) {
    var pa = pos[a], pb = pos[b];
    var x1 = pa.x + pa.w / 2, y1 = pa.y, x2 = pb.x + pb.w / 2, y2 = pb.y + pb.h;
    if (pa.y === pb.y) {
      // 同じ層(循環する成分の中): 上に膨らむ弧
      var bulge = 34;
      return 'M ' + x1 + ' ' + y1 + ' C ' + x1 + ' ' + (y1 - bulge) + ', ' + x2 + ' ' + (y2 - pb.h - bulge) + ', ' + x2 + ' ' + (y2 - pb.h);
    }
    var dy = Math.max(40, (y1 - y2) / 2);
    return 'M ' + x1 + ' ' + y1 + ' C ' + x1 + ' ' + (y1 - dy) + ', ' + x2 + ' ' + (y2 + dy) + ', ' + x2 + ' ' + y2;
  }
  function drawEdges() {
    clear(edgeGroup);
    var all = document.getElementById('all-edges').checked;
    fileEdges.forEach(function (e) {
      var a = modIndex.get(e.from), b = modIndex.get(e.to);
      var reduced = reducedSet.has(e.from + ' -> ' + e.to);
      var incident = selectedFile !== null && (a === selectedFile || b === selectedFile);
      if (!all && !reduced && !incident) return;
      var cls = 'edge';
      var marker = 'edge';
      if (selectedFile !== null) {
        if (a === selectedFile) { cls += ' out'; marker = 'out'; }
        else if (b === selectedFile) { cls += ' in'; marker = 'in'; }
        else cls += ' dim';
      }
      if (!all && !reduced) cls += ' extra';
      var path = svgEl('path', { 'class': cls, d: edgePath(a, b), 'marker-end': 'url(#arrow-' + marker + ')' });
      var title = svgEl('title');
      title.textContent = e.from + ' → ' + e.to + '(' + e.count + ' 本' + (e.imported ? '' : '、import 行に無い') + ')';
      path.appendChild(title);
      edgeGroup.appendChild(path);
    });
    var related = new Set();
    if (selectedFile !== null) {
      fileOut[selectedFile].forEach(function (k) { related.add(modIndex.get(fileEdges[k].to)); });
      fileIn[selectedFile].forEach(function (k) { related.add(modIndex.get(fileEdges[k].from)); });
    }
    nodeGroup.childNodes.forEach(function (g) {
      var i = Number(g.getAttribute('data-module'));
      g.classList.toggle('selected', i === selectedFile);
      g.classList.toggle('related', related.has(i));
    });
  }
  document.getElementById('all-edges').addEventListener('change', drawEdges);
  var legend = document.getElementById('group-legend');
  groups.forEach(function (g) {
    var sw = el('span'); sw.style.background = groupColor(g);
    legend.appendChild(sw);
    legend.appendChild(document.createTextNode((g === '' ? '(グループなし)' : g) + ' '));
  });

  function declLink(i, withModule) {
    var d = decls[i];
    return el('span', { 'class': 'link', onclick: function () { showTab('decls'); selectDecl(i); } }, [withModule ? d.name : declLabel(d)]);
  }
  function fileEdgeDetail(k, dir) {
    var e = fileEdges[k];
    var other = dir === 'out' ? e.to : e.from;
    var li = el('li', null, [el('span', { 'class': 'link', onclick: function () { selectFile(modIndex.get(other)); } }, [other]), ' (' + e.count + ' 本)']);
    if (!e.imported) { li.appendChild(document.createTextNode(' ')); li.appendChild(el('span', { 'class': 'flag' }, ['import 行に無い参照'])); }
    var ul = el('ul');
    declEdges.forEach(function (de, j) {
      var da = decls[declIndex.get(de.from)], db = decls[declIndex.get(de.to)];
      if (da.module === e.from && db.module === e.to) {
        ul.appendChild(el('li', null, [declLink(declIndex.get(de.from), false), ' → ', declLink(declIndex.get(de.to), false), el('span', { 'class': 'dist' }, [' (' + de.sites.length + ' 箇所)'])]));
      }
    });
    li.appendChild(ul);
    return li;
  }
  function selectFile(i) {
    selectedFile = i;
    drawEdges();
    var m = modules[i];
    var panel = document.getElementById('file-panel');
    clear(panel);
    panel.appendChild(el('h2', null, [m.name]));
    panel.appendChild(el('div', { 'class': 'muted' }, [m.path + ' · グループ ' + (m.group === '' ? '(なし)' : m.group) + ' · 層 ' + m.layer]));
    if (cycleMembers[i].length > 1) panel.appendChild(el('div', { 'class': 'flag' }, ['循環する成分: ' + cycleMembers[i].join(', ')]));
    var counts = {};
    declsByModule[i].forEach(function (di) { counts[decls[di].kind] = (counts[decls[di].kind] || 0) + 1; });
    panel.appendChild(el('h3', null, ['宣言数(種類別): ' + declsByModule[i].length]));
    var ulc = el('ul');
    kinds.forEach(function (k) { if (counts[k]) ulc.appendChild(el('li', null, [k + ' ' + counts[k]])); });
    panel.appendChild(ulc);
    panel.appendChild(el('h3', null, ['使うファイル: ' + fileOut[i].length]));
    var ulo = el('ul');
    fileOut[i].forEach(function (k) { ulo.appendChild(fileEdgeDetail(k, 'out')); });
    panel.appendChild(ulo);
    panel.appendChild(el('h3', null, ['使われるファイル: ' + fileIn[i].length]));
    var uli = el('ul');
    fileIn[i].forEach(function (k) { uli.appendChild(fileEdgeDetail(k, 'in')); });
    panel.appendChild(uli);
    var unused = DATA.unusedImports.filter(function (u) { return u.module === m.name; });
    panel.appendChild(el('h3', null, ['参照の無い import: ' + unused.length]));
    var ulu = el('ul');
    unused.forEach(function (u) { ulu.appendChild(el('li', null, [u['import']])); });
    panel.appendChild(ulu);
    panel.appendChild(el('h3', null, ['宣言']));
    var uld = el('ul');
    declsByModule[i].forEach(function (di) { uld.appendChild(el('li', null, [el('span', { 'class': 'kind' }, [decls[di].kind]), declLink(di, false)])); });
    panel.appendChild(uld);
    panel.appendChild(el('p', null, [el('button', { 'class': 'small', onclick: function () { moduleFilter = m.name; document.getElementById('decl-filter').value = ''; renderDeclList(); showTab('decls'); } }, ['宣言単位タブでこのファイルの宣言を見る'])]));
  }

  // 宣言単位
  var selectedDecl = null;
  var moduleFilter = null;
  var kindSelect = document.getElementById('kind-filter');
  kinds.forEach(function (k) { kindSelect.appendChild(el('option', { value: k }, [k])); });
  function renderDeclList() {
    var list = document.getElementById('decl-list');
    clear(list);
    var q = document.getElementById('decl-filter').value.trim().toLowerCase();
    var kind = kindSelect.value;
    var shown = 0;
    modules.forEach(function (m, mi) {
      if (moduleFilter !== null && m.name !== moduleFilter) return;
      var items = declsByModule[mi].filter(function (di) {
        var d = decls[di];
        return (kind === '' || d.kind === kind) && (q === '' || d.name.toLowerCase().indexOf(q) >= 0);
      });
      if (items.length === 0) return;
      list.appendChild(el('div', { 'class': 'mod-head' }, [m.name, el('span', { 'class': 'dist' }, [' ' + m.path])]));
      items.forEach(function (di) {
        var d = decls[di];
        var item = el('div', { 'class': 'decl-item' + (di === selectedDecl ? ' selected' : ''), onclick: function () { selectDecl(di); } },
          [el('span', { 'class': 'kind' }, [d.kind]), declLabel(d) + (d.owner ? ' (protocol ' + d.owner + ')' : '')]);
        item.setAttribute('data-decl', String(di));
        list.appendChild(item);
        shown++;
      });
    });
    document.getElementById('decl-count').textContent = shown + ' / ' + decls.length + ' 宣言' + (moduleFilter !== null ? ' · モジュール ' + moduleFilter + ' だけ(名前を入力すると解除)' : '');
  }
  document.getElementById('decl-filter').addEventListener('input', function () { moduleFilter = null; renderDeclList(); });
  kindSelect.addEventListener('change', renderDeclList);
  document.getElementById('transitive').addEventListener('change', function () { if (selectedDecl !== null) renderDeclPanel(); });
  function neighbours(start, dir, transitive) {
    // 幅優先: 宣言の添字 → 距離
    var dist = new Map();
    var queue = [start];
    dist.set(start, 0);
    while (queue.length > 0) {
      var v = queue.shift();
      var d = dist.get(v);
      if (d >= 1 && !transitive) continue;
      var edges = dir === 'out' ? declOut[v] : declIn[v];
      edges.forEach(function (k) {
        var e = declEdges[k];
        var w = declIndex.get(dir === 'out' ? e.to : e.from);
        if (!dist.has(w)) { dist.set(w, d + 1); queue.push(w); }
      });
    }
    dist['delete'](start);
    return dist;
  }
  function groupedByFile(dist) {
    var byFile = new Map();
    Array.from(dist.keys()).sort(function (a, b) { return dist.get(a) - dist.get(b) || a - b; }).forEach(function (di) {
      var m = decls[di].module;
      if (!byFile.has(m)) byFile.set(m, []);
      byFile.get(m).push(di);
    });
    var ul = el('ul');
    Array.from(byFile.keys()).sort(function (a, b) { return modIndex.get(a) - modIndex.get(b); }).forEach(function (m) {
      var items = byFile.get(m);
      var inner = el('ul');
      items.forEach(function (di) {
        var d = dist.get(di);
        inner.appendChild(el('li', null, [el('span', { 'class': 'kind' }, [decls[di].kind]), declLink(di, false), d >= 2 ? el('span', { 'class': 'dist' }, [' (距離 ' + d + ')']) : '']));
      });
      ul.appendChild(el('li', null, [el('span', { 'class': 'link', onclick: function () { selectFile(modIndex.get(m)); showTab('files'); } }, [m]), ' (' + items.length + ')', inner]));
    });
    return ul;
  }
  function renderDeclPanel() {
    var d = decls[selectedDecl];
    var m = modules[modIndex.get(d.module)];
    var transitive = document.getElementById('transitive').checked;
    var panel = document.getElementById('decl-panel');
    clear(panel);
    panel.appendChild(el('h2', null, [d.name]));
    panel.appendChild(el('div', { 'class': 'muted' }, [d.kind + ' · ' + d.phase + ' · ' + d.module + (d.owner ? ' · protocol ' + d.owner : '') + ' · ' + m.path + ':' + d.line + (d.selfRef ? ' · 自己参照' : '')]));
    panel.appendChild(el('p', null, [d.summary === '' ? el('span', { 'class': 'muted' }, ['(宣言コメントなし)']) : d.summary]));
    var outs = neighbours(selectedDecl, 'out', transitive), ins = neighbours(selectedDecl, 'in', transitive);
    panel.appendChild(el('h3', null, ['この宣言が使う' + (transitive ? '(推移的)' : '(直接)') + ': ' + outs.size]));
    panel.appendChild(groupedByFile(outs));
    panel.appendChild(el('h3', null, ['この宣言を使う' + (transitive ? '(推移的)' : '(直接)') + ': ' + ins.size]));
    panel.appendChild(groupedByFile(ins));
    panel.appendChild(el('p', null, [el('button', { 'class': 'small', onclick: function () { selectFile(modIndex.get(d.module)); showTab('files'); } }, ['ファイル単位タブでこのファイルを見る'])]));
  }
  function selectDecl(i) {
    selectedDecl = i;
    document.querySelectorAll('.decl-item').forEach(function (item) { item.classList.toggle('selected', Number(item.getAttribute('data-decl')) === i); });
    renderDeclPanel();
    var item = document.querySelector('.decl-item[data-decl="' + i + '"]');
    if (item && item.scrollIntoView) item.scrollIntoView({ block: 'nearest' });
  }

  // URL の `#file=<モジュール名>` / `#decl=<修飾名>` / `#tab=decls` / `#all=1` / `#transitive=1`(`&` 区切り)で選択状態を開く(共有と観測のため。乱数・時刻は使わない)
  function applyHash() {
    var params = {};
    location.hash.replace(/^#/, '').split('&').forEach(function (kv) {
      var i = kv.indexOf('=');
      if (i > 0) params[decodeURIComponent(kv.slice(0, i))] = decodeURIComponent(kv.slice(i + 1));
    });
    if (params.all === '1') { document.getElementById('all-edges').checked = true; drawEdges(); }
    if (params.transitive === '1') document.getElementById('transitive').checked = true;
    if (params.file && modIndex.has(params.file)) { showTab('files'); selectFile(modIndex.get(params.file)); }
    if (params.decl && declIndex.has(params.decl)) { showTab('decls'); selectDecl(declIndex.get(params.decl)); }
    else if (params.tab === 'decls') showTab('decls');
  }
  drawEdges();
  renderDeclList();
  applyHash();
  window.addEventListener('hashchange', applyHash);
})();
</script>
</body>
</html>
"##

/-- テンプレートにヘッダと JSON を入れる(`{{HEADER}}` を先に、`{{DATA}}` を後に置き換える: JSON の中身は再走査しない)。 -/
def renderHtml (header json : String) : String :=
  (template.replace "{{HEADER}}" header).replace "{{DATA}}" json

end Naru.Deps
