import Std.Data.HashMap
import Naru.Driver
import Naru.Describe

/-!
# 依存グラフ(IDEAL.md C63〜C66、用語「依存グラフ」「宣言の依存」「ファイルの依存」)

`naru deps` がコンパイル単位から作る、宣言単位とファイル単位の参照のグラフ。閲覧と理解のための派生物で、検証の根拠にはしない
(不変条件: 生成 Model / Statements の import の正しさや意味保存の証拠に流用しない)。

- 宣言の依存 = 名前解決の参照の索引 `Resolve.Ref`(値の位置の名前・修飾名・record literal の型名・パターンの構築子・UFCS のメソッド名・型の位置の名前・
  scenario の `input … = …;` の束縛。定義ジャンプ C30 と同じ索引)に記録された、宣言の本体・署名・欄・variant の引数・claim bundle の項目から他の宣言への
  構文上の参照。欄アクセスの record や呼出し結果の型などの推論された依存は含めない。自己参照は辺にせず宣言の属性(`selfRef`)にする。
- ファイルの依存 = ファイルを跨ぐ宣言の依存の集約(辺ごとに宣言の辺の本数と、参照元の `import` 行に参照先があるか)。import 行とは別物で、
  import 行に無い参照(`imported = false`)と参照の無い import(`unusedImports`)は差として報告する。
- 層と強連結成分: 他のファイルに依存しないファイルが層 0、各ファイルは依存先の最大の層 + 1。循環するファイルは 1 つの強連結成分として同じ層にまとめる
  (循環があっても生成は失敗しない: 参照の循環は生成 Model / Statements の import の循環(E017)とは別物で、spec → runtime と spec → spec の参照が
  2 つのファイルの間で逆向きに走ると起きる)。
- 推移簡約: 成分を縮約した DAG で到達関係を変えない最小の辺集合(成分の間の辺 `A → B` は、`A` の他の依存先から `B` へ到達できなければ残す。
  残す成分の辺はそれを作るファイルの辺のうち並びで最初のもの 1 つで代表する)。成分の中(循環)の辺はすべて残す。
- 並び順はすべてソースから決まる: モジュールはソースルートからの相対パス順、宣言はソース中の出現順、辺は(参照元, 参照先)の宣言 / モジュールの順、
  出現位置は(ファイル, 行, 列)の順。ハッシュ表の走査順・時刻・絶対パス・環境変数・乱数には依存しない(C64)。
- JSON は独自の印字(`J.render`)で正規形にする: キーは書いた順で固定、2 空白の字下げ、UTF-8、LF、末尾改行あり、浮動小数なし。`<` `>` `&` は
  `<` 等(バックスラッシュ + `u003c`)に逃がすので、同じバイト列を HTML の `<script type="application/json">` にそのまま埋め込める(C65)。
- 索引に無い文脈・参照先に当たった参照は捨てずに数える(`Graph.dropped`)。名前解決を通った単位では 0 のはずで、`naru deps` は 0 でなければ内部エラーにする。
-/

namespace Naru.Deps
open Std

/-! ## 最小の JSON の木と正規形の印字 -/

inductive J where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | arr (xs : List J)
  | obj (kvs : List (String × J))

def J.isScalar : J → Bool
  | .arr _ | .obj _ => false
  | _ => true

/-- JSON 文字列のエスケープ。`"` `\` と制御文字に加えて `<` `>` `&` も `\u00XX` にする(HTML への埋め込みのため。JSON としては同じ値)。 -/
def escapeJson (s : String) : String := Id.run do
  let hex (n : Nat) : String :=
    let digits := "0123456789abcdef".toList.toArray
    String.ofList [digits[(n / 16) % 16]!, digits[n % 16]!]
  let mut out := ""
  for c in s.toList do
    match c with
    | '"' => out := out ++ "\\\""
    | '\\' => out := out ++ "\\\\"
    | '\n' => out := out ++ "\\n"
    | '\r' => out := out ++ "\\r"
    | '\t' => out := out ++ "\\t"
    | '<' => out := out ++ "\\u003c"
    | '>' => out := out ++ "\\u003e"
    | '&' => out := out ++ "\\u0026"
    | c =>
      if c.toNat < 0x20 then out := out ++ "\\u00" ++ hex c.toNat
      else out := out.push c
  return out

def indentStr (n : Nat) : String := "".pushn ' ' n

/-- 正規形の印字。スカラーだけの配列 / オブジェクトは 1 行、それ以外は 1 要素 1 行(2 空白の字下げ)。 -/
partial def J.render (j : J) (ind : Nat := 0) : String :=
  match j with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .str s => "\"" ++ escapeJson s ++ "\""
  | .arr [] => "[]"
  | .arr xs =>
    if xs.all J.isScalar then "[" ++ ", ".intercalate (xs.map (·.render ind)) ++ "]"
    else "[\n" ++ ",\n".intercalate (xs.map fun x => indentStr (ind + 2) ++ x.render (ind + 2)) ++ "\n" ++ indentStr ind ++ "]"
  | .obj [] => "{}"
  | .obj kvs =>
    if kvs.all (·.2.isScalar) then
      "{ " ++ ", ".intercalate (kvs.map fun (k, v) => "\"" ++ escapeJson k ++ "\": " ++ v.render ind) ++ " }"
    else
      "{\n" ++ ",\n".intercalate (kvs.map fun (k, v) => indentStr (ind + 2) ++ "\"" ++ escapeJson k ++ "\": " ++ v.render (ind + 2)) ++
        "\n" ++ indentStr ind ++ "}"

/-! ## グラフ -/

/-- 1 つのコンパイル単位の入力: ソースルートの接頭辞(`<root>/`)、検査を通ったモジュール、名前解決の参照の索引、各ファイルの本文。 -/
structure UnitInput where
  prefix_ : String
  mods : Array Module
  refs : Array Resolve.Ref
  /-- (ファイルのパス(渡されたまま), 本文)。宣言コメントの要旨を読むのに使う。 -/
  sources : List (String × String)

structure ModuleInfo where
  name : String
  /-- ソースルートからの相対パス。 -/
  path : String
  /-- モジュール名から最後の要素を除いた経路(要素が 1 つなら空)。 -/
  group : String
  imports : List String
  /-- 渡されたパス(参照の索引の `file` と突き合わせる)。 -/
  file : String
deriving Inhabited

structure DeclInfo where
  qualified : String
  name : String
  module : Nat
  kind : DeclKind
  owner : Option String
  line : Nat
  col : Nat
  summary : String
  selfRef : Bool := false
deriving Inhabited

structure Site where
  path : String
  line : Nat
  col : Nat
  written : String
deriving Inhabited

structure DeclEdge where
  src : Nat
  dst : Nat
  sites : List Site
deriving Inhabited

structure FileEdge where
  src : Nat
  dst : Nat
  count : Nat
  imported : Bool
deriving Inhabited

structure Graph where
  modules : Array ModuleInfo
  decls : Array DeclInfo
  declEdges : List DeclEdge
  fileEdges : List FileEdge
  /-- (モジュールの添字, import 行のモジュール名)。参照の無い import。 -/
  unusedImports : List (Nat × String)
  /-- 強連結成分(各成分はモジュールの添字の昇順。成分は最小の添字の順)。 -/
  components : List (List Nat)
  /-- モジュールごとの成分の添字。 -/
  componentOf : Array Nat
  /-- モジュールごとの層。 -/
  layers : Array Nat
  /-- 推移簡約した辺(モジュールの添字の組。並びはファイルの辺と同じ)。 -/
  reduced : List (Nat × Nat)
  /-- 文脈の宣言または参照先が索引に無くて辺にできなかった参照の数(0 のはず)。 -/
  dropped : Nat := 0

def siteLt (a b : Site) : Bool :=
  a.path < b.path || (a.path == b.path && (a.line < b.line || (a.line == b.line && a.col < b.col)))

def pairLt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- ソースルートの接頭辞を落とす。 -/
def stripPrefix (pre : String) (f : String) : String :=
  if !pre.isEmpty && f.startsWith pre then (f.drop pre.length).toString else f

/-! ### 強連結成分(Kosaraju)・層・推移簡約 -/

/-- 深さ優先で訪問し、訪問を終えた順に `v` を前に積む(先頭が最後に終えた節点)。 -/
partial def dfsFinish (adj : Array (List Nat)) (v : Nat) (st : Array Bool × List Nat) : Array Bool × List Nat :=
  if st.1[v]! then st
  else
    let st := (st.1.set! v true, st.2)
    let st := (adj[v]!).foldl (fun s w => dfsFinish adj w s) st
    (st.1, v :: st.2)

/-- 逆向きの辺で到達できる未割当の節点に成分 `c` を割り当てる。 -/
partial def dfsAssign (radj : Array (List Nat)) (c : Nat) (v : Nat) (comp : Array (Option Nat)) : Array (Option Nat) :=
  if (comp[v]!).isSome then comp
  else
    let comp := comp.set! v (some c)
    (radj[v]!).foldl (fun acc w => dfsAssign radj c w acc) comp

/-- 強連結成分: (成分の一覧(各成分は添字の昇順、成分は最小の添字の順), 節点ごとの成分の添字)。 -/
def sccOf (n : Nat) (adj : Array (List Nat)) : List (List Nat) × Array Nat := Id.run do
  let mut radj : Array (List Nat) := Array.replicate n []
  for v in [0:n] do
    for w in adj[v]! do radj := radj.set! w (v :: radj[w]!)
  let mut st : Array Bool × List Nat := (Array.replicate n false, [])
  for v in [0:n] do st := dfsFinish adj v st
  let mut comp : Array (Option Nat) := Array.replicate n none
  let mut next := 0
  for v in st.2 do
    if (comp[v]!).isNone then
      comp := dfsAssign radj next v comp
      next := next + 1
  -- 成分を最小の添字の順に並べ直す
  let mut groups : Array (List Nat) := Array.replicate next []
  for v in [0:n] do
    let c := (comp[v]!).getD 0
    groups := groups.set! c (groups[c]! ++ [v])
  let ordered := (groups.toList.filter (!·.isEmpty)).mergeSort fun a b => a.head! ≤ b.head!
  let mut compOf : Array Nat := Array.replicate n 0
  for (members, i) in ordered.zipIdx do
    for v in members do compOf := compOf.set! v i
  return (ordered, compOf)

/-- 成分の DAG の層: 依存先の無い成分が 0、他は依存先の最大 + 1。 -/
partial def layerOf (cadj : Array (List Nat)) (c : Nat) (memo : Array (Option Nat)) : Nat × Array (Option Nat) :=
  match memo[c]! with
  | some l => (l, memo)
  | none =>
    let (best, memo) := (cadj[c]!).foldl (init := ((none : Option Nat), memo)) fun (acc, memo) d =>
      let (l, memo) := layerOf cadj d memo
      (some (max (acc.getD 0) (l + 1)), memo)
    let l := best.getD 0
    (l, memo.set! c (some l))

/-- `c` から辺 1 つ以上で到達できる成分。 -/
partial def reachFrom (cadj : Array (List Nat)) (c : Nat) : List Nat :=
  let rec go (todo : List Nat) (seen : List Nat) : List Nat :=
    match todo with
    | [] => seen
    | x :: rest =>
      let next := (cadj[x]!).filter fun y => !seen.contains y
      go (next ++ rest) (seen ++ next)
  go (cadj[c]!) (cadj[c]!)

/-! ### 構築 -/

/-- コンパイル単位(1 つ以上)から依存グラフを作る。 -/
def build (units : List UnitInput) : Graph := Id.run do
  -- モジュール: ソースルートからの相対パス順
  let mut unsorted : Array ModuleInfo := #[]
  let mut texts : HashMap String (Array String) := {}
  for u in units do
    for (f, text) in u.sources do texts := texts.insert f ((text.splitOn "\n").toArray)
    for m in u.mods do
      let name := renderPath m.name
      let group := renderPath (m.name.dropLast)
      unsorted := unsorted.push { name, path := stripPrefix u.prefix_ m.file, group, imports := m.imports.toList.map renderPath, file := m.file }
  let mods := unsorted.qsort fun a b => a.path < b.path
  let mut modIdx : HashMap String Nat := {}
  let mut fileMod : HashMap String Nat := {}
  for (m, i) in mods.toList.zipIdx do
    modIdx := modIdx.insert m.name i
    fileMod := fileMod.insert m.file i
  -- 宣言: モジュールの順、ソースの出現順
  let mut decls : Array DeclInfo := #[]
  let mut declIdx : HashMap String Nat := {}
  for (mi, i) in mods.toList.zipIdx do
    let some m := units.findSome? (fun u => u.mods.find? (·.file == mi.file)) | continue
    let lines := (texts.get? mi.file).getD #[]
    for d in m.decls do
      let qualified := renderPath (m.name ++ [d.name])
      let summary := (declComment lines d).head?.getD ""
      declIdx := declIdx.insert qualified decls.size
      decls := decls.push
        { qualified, name := d.name, module := i, kind := d.kind, owner := d.owner, line := d.span.line, col := d.span.col, summary }
  -- 宣言の辺: 参照の索引から(自己参照は属性)
  let mut sitesOf : HashMap (Nat × Nat) (List Site) := {}
  let mut keys : List (Nat × Nat) := []
  let mut dropped := 0
  for u in units do
    for r in u.refs do
      let some mi := fileMod.get? r.file | dropped := dropped + 1; continue
      let ctxQualified := renderPath ((mods[mi]!).name.splitOn "." ++ [r.declName])
      let some src := declIdx.get? ctxQualified | dropped := dropped + 1; continue
      let some dst := declIdx.get? r.target.qualified | dropped := dropped + 1; continue
      if src == dst then
        decls := decls.modify src fun d => { d with selfRef := true }
        continue
      let site : Site := { path := stripPrefix u.prefix_ r.file, line := r.span.line, col := r.span.col, written := renderPath r.path }
      match sitesOf.get? (src, dst) with
      | some ss => sitesOf := sitesOf.insert (src, dst) (site :: ss)
      | none =>
        sitesOf := sitesOf.insert (src, dst) [site]
        keys := (src, dst) :: keys
  let sortedKeys := keys.mergeSort fun a b => pairLt a b || a == b
  let declEdges : List DeclEdge := sortedKeys.map fun k =>
    let ss := ((sitesOf.get? k).getD []).mergeSort fun a b => siteLt a b || (a.path == b.path && a.line == b.line && a.col == b.col)
    -- 同じ位置の重複(同じ参照が 2 回記録されることは無いが、安全網)
    let ss := ss.foldl (init := ([] : List Site)) fun acc s =>
      match acc.getLast? with
      | some t => if t.path == s.path && t.line == s.line && t.col == s.col then acc else acc ++ [s]
      | none => [s]
    { src := k.1, dst := k.2, sites := ss }
  -- ファイルの辺: 宣言の辺の集約
  let mut fileCount : HashMap (Nat × Nat) Nat := {}
  let mut fileKeys : List (Nat × Nat) := []
  for e in declEdges do
    let a := (decls[e.src]!).module
    let b := (decls[e.dst]!).module
    if a == b then continue
    match fileCount.get? (a, b) with
    | some n => fileCount := fileCount.insert (a, b) (n + 1)
    | none =>
      fileCount := fileCount.insert (a, b) 1
      fileKeys := (a, b) :: fileKeys
  let sortedFileKeys := fileKeys.mergeSort fun a b => pairLt a b || a == b
  let fileEdges : List FileEdge := sortedFileKeys.map fun (a, b) =>
    { src := a, dst := b, count := (fileCount.get? (a, b)).getD 0, imported := (mods[a]!).imports.contains (mods[b]!).name }
  -- 参照の無い import(書かれた順)
  let mut unused : List (Nat × String) := []
  for (m, i) in mods.toList.zipIdx do
    for imp in m.imports do
      let used := fileEdges.any fun e => e.src == i && (mods[e.dst]!).name == imp
      if !used then unused := unused ++ [(i, imp)]
  -- 成分・層・推移簡約
  let n := mods.size
  let mut adj : Array (List Nat) := Array.replicate n []
  for e in fileEdges do adj := adj.set! e.src (adj[e.src]! ++ [e.dst])
  let (components, compOf) := sccOf n adj
  let nc := components.length
  let mut cadj : Array (List Nat) := Array.replicate nc []
  for e in fileEdges do
    let a := compOf[e.src]!
    let b := compOf[e.dst]!
    if a != b && !(cadj[a]!).contains b then cadj := cadj.set! a (cadj[a]! ++ [b])
  let mut memo : Array (Option Nat) := Array.replicate nc none
  let mut clayer : Array Nat := Array.replicate nc 0
  for c in [0:nc] do
    let (l, memo') := layerOf cadj c memo
    memo := memo'
    clayer := clayer.set! c l
  let mut layers : Array Nat := Array.replicate n 0
  for v in [0:n] do layers := layers.set! v (clayer[compOf[v]!]!)
  -- 成分の辺 (a, b) を残すのは、a の他の依存先 e から b へ到達できないとき
  let mut keep : List (Nat × Nat) := []
  for c in [0:nc] do
    let succ := cadj[c]!
    for d in succ do
      let redundant := succ.any fun e => e != d && (reachFrom cadj e).contains d
      if !redundant then keep := keep ++ [(c, d)]
  let mut reduced : List (Nat × Nat) := []
  let mut represented : List (Nat × Nat) := []
  for e in fileEdges do
    let a := compOf[e.src]!
    let b := compOf[e.dst]!
    if a == b then reduced := reduced ++ [(e.src, e.dst)]
    else if keep.contains (a, b) && !represented.contains (a, b) then
      reduced := reduced ++ [(e.src, e.dst)]
      represented := represented ++ [(a, b)]
  return { modules := mods, decls, declEdges, fileEdges, unusedImports := unused, components, componentOf := compOf, layers, reduced, dropped }

/-! ### JSON -/

/-- 出力の先頭に入れる版と hash。 -/
structure Meta where
  compilerVersion : String
  compilerHash : String
  /-- (ソースルートからの相対パス, sha256)。パス順。 -/
  sources : List (String × String)

def kindName (k : DeclKind) : String := k.describe

def Graph.stats (g : Graph) : List (String × Nat) :=
  let across := g.declEdges.filter fun e => (g.decls[e.src]!).module != (g.decls[e.dst]!).module
  let maxLayer := g.layers.foldl max 0
  [ ("files", g.modules.size), ("decls", g.decls.size), ("declEdges", g.declEdges.length), ("declEdgesAcrossFiles", across.length),
    ("fileEdges", g.fileEdges.length), ("reducedEdges", g.reduced.length), ("layers", if g.modules.isEmpty then 0 else maxLayer + 1) ]

def toJson (info : Meta) (g : Graph) : J :=
  let modules := g.modules.toList.zipIdx.map fun (m, i) =>
    J.obj [ ("name", .str m.name), ("path", .str m.path), ("group", .str m.group), ("imports", .arr (m.imports.map J.str)),
            ("layer", .nat g.layers[i]!), ("component", .nat g.componentOf[i]!) ]
  let decls := g.decls.toList.map fun d =>
    J.obj [ ("name", .str d.qualified), ("module", .str (g.modules[d.module]!).name), ("kind", .str (kindName d.kind)),
            ("phase", .str d.kind.phase.describe), ("owner", match d.owner with | some o => .str o | none => .null),
            ("line", .nat d.line), ("col", .nat d.col), ("summary", .str d.summary), ("selfRef", .bool d.selfRef) ]
  let declEdges := g.declEdges.map fun e =>
    J.obj [ ("from", .str (g.decls[e.src]!).qualified), ("to", .str (g.decls[e.dst]!).qualified),
            ("sites", .arr (e.sites.map fun s => .obj [ ("path", .str s.path), ("line", .nat s.line), ("col", .nat s.col), ("written", .str s.written) ])) ]
  let fileEdges := g.fileEdges.map fun e =>
    J.obj [ ("from", .str (g.modules[e.src]!).name), ("to", .str (g.modules[e.dst]!).name), ("count", .nat e.count), ("imported", .bool e.imported) ]
  let unused := g.unusedImports.map fun (i, imp) => J.obj [ ("module", .str (g.modules[i]!).name), ("import", .str imp) ]
  let components := g.components.map fun c => J.arr (c.map fun v => .str (g.modules[v]!).name)
  let reduced := g.reduced.map fun (a, b) => J.obj [ ("from", .str (g.modules[a]!).name), ("to", .str (g.modules[b]!).name)]
  J.obj
    [ ("naru-compiler", .str info.compilerVersion), ("naru-compiler-sha256", .str info.compilerHash),
      ("sources", .arr (info.sources.map fun (p, h) => .obj [ ("path", .str p), ("sha256", .str h) ])),
      ("modules", .arr modules), ("decls", .arr decls), ("declEdges", .arr declEdges), ("fileEdges", .arr fileEdges),
      ("unusedImports", .arr unused), ("components", .arr components), ("reducedEdges", .arr reduced),
      ("stats", .obj (g.stats.map fun (k, n) => (k, .nat n))) ]

/-- `deps.json` の本文(末尾に改行 1 つ)。 -/
def renderJson (info : Meta) (g : Graph) : String := (toJson info g).render ++ "\n"

/-- HTML の先頭のコメント(コンパイラ版・ソースの相対パスと sha256 の一覧)。 -/
def htmlHeader (info : Meta) : String :=
  "<!-- naru deps: generated by naru from the source roots of naru.toml. Do not edit by hand: this file is machine-generated (IDEAL.md).\n" ++
  s!"naru-compiler: {info.compilerVersion} sha256:{info.compilerHash}\n" ++
  "".intercalate (info.sources.map fun (p, h) => s!"naru-source: {p} sha256:{h}\n") ++
  "-->\n"

end Naru.Deps
