import Lean.Data.Json
import Std.Data.HashMap
import Naru
import NaruTest.Common
import NaruTest.Repo

/-!
# `naru_test deps` — 依存グラフの検査(IDEAL.md C63〜C66)

リポジトリのルートで `lake exe naru_test deps` と実行する。`lake build naru` の後、`.lake/build/bin/naru deps` を走らせて次を確かめる。

- C63(生成の入口): 現在のソース(`naru.toml` のソースルート)で `naru deps --out <一時ディレクトリ>` が exit 0 で `deps.json` と `index.html` を書く。
  `deps` キーの無い `naru.toml` の検体(`tests/deps/nokey/`)は `--out` 無しで exit 非 0(`--out` があれば書ける)。診断の出る検体(`tests/deps/broken/`)は
  複製の出力先に古いファイルを置いても exit 非 0 で出力先のファイルが増減・変更しない。実行の前後で有効な生成先の全ファイルの sha256 が同じ。
  `grep -rn '"docs' compiler/` が 0 件(出力先のディレクトリ名の直書きが無い)。
- C64(決定性と内容): 別々の一時ディレクトリへ 2 回生成して全ファイルの sha256 が一致。JSON の先頭にコンパイラ版・ソースの相対パスと sha256 の一覧が入り、
  パスがソースルートのディレクトリ名で始まらず、各 sha256 が実際のファイルの hash。手で書いた期待 JSON の検体プロジェクト `tests/deps/sample/`(`expected/deps.json`。
  `naru-compiler-sha256` の値だけ実際の値に置き換える)に対する出力が byte 単位で一致。移植ソースに対する独立な検査: 宣言の総数と種類別件数が `naru_test repo` の
  C60 の宣言列挙(`NaruTest.Repo.scanDeclComments`)と一致、宣言間の辺の各出現位置についてソースをその場で字句解析した字句列が書かれた経路と一致、ファイル間の辺が
  宣言間の辺の集約(本数と import 行の有無)と一致、推移簡約が到達関係を保ちかつ最小、強連結成分が実際の相互到達と一致し層が「他に依存しなければ 0、
  さもなくば依存先の最大 + 1」の再計算と一致して辺の向きと矛盾しない、import との差(`imported` / `unusedImports`)が `module` / `import` 行の再構文解析と
  ファイル間の辺から再計算したものと一致、統計が再計算と一致。
- C65(自己完結の HTML): 追跡中の `index.html` と検体の HTML に、埋め込んだデータの外で外部 URL を読む `<script src>` / `<link>` / `fetch` / URL が無く
  (SVG の名前空間 `http://www.w3.org/2000/svg` は除く)、埋め込みの JSON が同じ回の `deps.json` と byte 単位で同一、テンプレート(`compiler/Naru/DepsTemplate.lean`)と
  HTML(データの外)に `Math.random` / 語 `Date` が無く、`prefers-color-scheme` の分岐がある。
- C66(鮮度と文書): 一時ディレクトリへ再生成した出力と追跡中の `naru.toml` の `deps`(`docs/deps/`)の各ファイルの sha256 が一致(不一致ならどのファイルが
  古いかを出す)、`git check-attr linguist-generated` が両ファイルで `set`、`git grep -l 'naru deps'` が README と docs の 4 文書に当たる。
-/

namespace NaruTest.Deps
open Lean (Json)

def workDir : System.FilePath := ".lake" / "naru" / "test" / "deps"
def fixturesDir : System.FilePath := "tests" / "deps"
def templateSource : System.FilePath := "compiler" / "Naru" / "DepsTemplate.lean"
def compilerDir : System.FilePath := "compiler"
def docsWithDeps : List String := ["README.md", "docs/cli.md", "docs/architecture.md", "docs/testing.md"]
def dataMarker : String := "<script id=\"deps-data\" type=\"application/json\">"

structure Env where
  root : System.FilePath
  bin : System.FilePath

def runDeps (env : Env) (cwd : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  runProc env.bin.toString args (cwd := some cwd)

def freshDir (p : System.FilePath) : IO System.FilePath := do
  if ← p.isDir then IO.FS.removeDirAll p
  IO.FS.createDirAll p
  IO.FS.realPath p

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

def isSha (s : String) : Bool := s.length == 64 && s.toList.all isHex

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- 語としての出現(前後が識別子の文字でない)。 -/
def hasWord (s w : String) : Bool := Id.run do
  let cs := s.toList.toArray
  let ws := w.toList.toArray
  let isIdent (c : Char) : Bool := c.isAlphanum || c == '_'
  for i in [0:cs.size] do
    if i + ws.size ≤ cs.size && cs.extract i (i + ws.size) == ws then
      let before := i == 0 || !(isIdent cs[i - 1]!)
      let after := i + ws.size ≥ cs.size || !(isIdent cs[i + ws.size]!)
      if before && after then return true
  return false

/-- ソースルートのどれかの配下にある相対パスのファイル。 -/
def findInRoots (roots : List System.FilePath) (rel : String) : IO (Option System.FilePath) := do
  for r in roots do
    let f := r / System.FilePath.mk rel
    if ← f.pathExists then return some f
  return none

/-! ## JSON の読み -/

structure JModule where
  name : String
  path : String
  group : String
  imports : List String
  layer : Nat
  component : Nat
deriving Inhabited

structure JDecl where
  name : String
  module : String
  kind : String
  phase : String
  owner : Option String
  line : Nat
  col : Nat
  summary : String
  selfRef : Bool
deriving Inhabited

structure JSite where
  path : String
  line : Nat
  col : Nat
  written : String
deriving Inhabited

structure JDeclEdge where
  src : String
  dst : String
  sites : List JSite
deriving Inhabited

structure JFileEdge where
  src : String
  dst : String
  count : Nat
  imported : Bool
deriving Inhabited

structure Parsed where
  compilerVersion : String
  compilerHash : String
  sources : List (String × String)
  modules : List JModule
  decls : List JDecl
  declEdges : List JDeclEdge
  fileEdges : List JFileEdge
  unusedImports : List (String × String)
  components : List (List String)
  reduced : List (String × String)
  stats : List (String × Nat)
deriving Inhabited

def getStr (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def getNat (j : Json) (k : String) : Except String Nat := do (← j.getObjVal? k).getNat?
def getBool (j : Json) (k : String) : Except String Bool := do (← j.getObjVal? k).getBool?
def getArr (j : Json) (k : String) : Except String (List Json) := do return (← (← j.getObjVal? k).getArr?).toList

def parseGraph (text : String) : Except String Parsed := do
  let j ← Json.parse text
  let compilerVersion ← getStr j "naru-compiler"
  let compilerHash ← getStr j "naru-compiler-sha256"
  let sources ← (← getArr j "sources").mapM fun s => do return (← getStr s "path", ← getStr s "sha256")
  let modules ← (← getArr j "modules").mapM fun m => do
    let imports ← (← getArr m "imports").mapM (·.getStr?)
    let r : JModule := { name := ← getStr m "name", path := ← getStr m "path", group := ← getStr m "group", imports,
                         layer := ← getNat m "layer", component := ← getNat m "component" }
    return r
  let decls ← (← getArr j "decls").mapM fun d => do
    let owner ← match ← d.getObjVal? "owner" with
      | .null => pure none
      | o => pure (some (← o.getStr?))
    let r : JDecl := { name := ← getStr d "name", module := ← getStr d "module", kind := ← getStr d "kind", phase := ← getStr d "phase", owner,
                       line := ← getNat d "line", col := ← getNat d "col", summary := ← getStr d "summary", selfRef := ← getBool d "selfRef" }
    return r
  let declEdges ← (← getArr j "declEdges").mapM fun e => do
    let sites ← (← getArr e "sites").mapM fun s => do
      let r : JSite := { path := ← getStr s "path", line := ← getNat s "line", col := ← getNat s "col", written := ← getStr s "written" }
      return r
    let r : JDeclEdge := { src := ← getStr e "from", dst := ← getStr e "to", sites }
    return r
  let fileEdges ← (← getArr j "fileEdges").mapM fun e => do
    let r : JFileEdge := { src := ← getStr e "from", dst := ← getStr e "to", count := ← getNat e "count", imported := ← getBool e "imported" }
    return r
  let unusedImports ← (← getArr j "unusedImports").mapM fun u => do return (← getStr u "module", ← getStr u "import")
  let components ← (← getArr j "components").mapM fun c => do (← c.getArr?).toList.mapM (·.getStr?)
  let reduced ← (← getArr j "reducedEdges").mapM fun e => do return (← getStr e "from", ← getStr e "to")
  let statsObj ← (← j.getObjVal? "stats").getObj?
  let stats ← statsObj.toList.mapM fun (k, v) => do return (k, ← v.getNat?)
  return { compilerVersion, compilerHash, sources, modules, decls, declEdges, fileEdges, unusedImports, components, reduced, stats }

/-! ## 補助 -/

/-- `start` から辺 1 つ以上で到達できる節点(名前)。 -/
partial def reachable (adj : List (String × List String)) (start : String) : List String :=
  let rec go (todo : List String) (seen : List String) : List String :=
    match todo with
    | [] => seen
    | x :: rest =>
      let next := ((adj.lookup x).getD []).filter fun y => !seen.contains y
      go (next ++ rest) (seen ++ next)
  let init := (adj.lookup start).getD []
  go init init

def adjacencyOf (nodes : List String) (edges : List (String × String)) : List (String × List String) :=
  nodes.map fun n => (n, edges.filterMap fun (a, b) => if a == n then some b else none)

/-- 字句列の添字 `i` から始まる経路(識別子 (`.` 識別子)*)が `segments` と一致するか(先頭一致: 後に何が続いてもよい)。 -/
def pathAt (toks : Array Naru.Token) (i : Nat) (segments : List String) : Bool := Id.run do
  let mut k := i
  let mut first := true
  for seg in segments do
    if !first then
      match toks[k]? with
      | some t =>
        match t.kind with
        | .sym "." => k := k + 1
        | _ => return false
      | none => return false
    first := false
    match toks[k]? with
    | some t =>
      match t.kind with
      | .ident s => if s != seg then return false
      | _ => return false
    | none => return false
    k := k + 1
  return true

/-- HTML の埋め込みデータの外(テンプレート由来の部分)と中(JSON)。 -/
def splitHtml (html : String) : Option (String × String) :=
  match html.splitOn dataMarker with
  | [before, rest] =>
    match rest.splitOn "</script>" with
    | data :: after => some (before ++ "</script>".intercalate after, data)
    | [] => none
  | _ => none

/-! ## 検査 -/

/-- C64: 2 回の生成の一致と、JSON / HTML の先頭。返り値は 1 回目の出力先と JSON の本文と読んだグラフ。 -/
def checkDeterminism (env : Env) (roots : List System.FilePath) : M (Option (System.FilePath × String × Parsed)) := do
  let out1 ← freshDir (workDir / "run1")
  let out2 ← freshDir (workDir / "run2")
  let r1 ← runDeps env env.root #["deps", "--out", out1.toString]
  let r2 ← runDeps env env.root #["deps", "--out", out2.toString]
  if r1.exitCode != 0 || r2.exitCode != 0 then
    fail s!"C63: naru deps --out exit {r1.exitCode} / {r2.exitCode}\n{tail (r1.stdout ++ r1.stderr)}"
    return none
  ok s!"C63: naru deps --out <tmp> exit 0 twice ({r1.stdout.trimAscii.toString})"
  let s1 ← snapshotTree [out1]
  let s2 ← snapshotTree [out2]
  let names (s : List (String × String)) (base : System.FilePath) : List String :=
    s.map fun (p, _) => (p.drop (base.toString.length + 1)).toString
  if names s1 out1 != ["deps.json", "index.html"] then
    fail s!"C63: naru deps wrote {names s1 out1} (expected deps.json and index.html)"
    return none
  ok "C63: the output directory holds exactly deps.json and index.html"
  if (s1.map (·.2)) == (s2.map (·.2)) then ok s!"C64: two generations into different directories have the same sha256 for {s1.length} files"
  else fail s!"C64: the two generations differ: {(s1.zip s2).filter (fun (a, b) => a.2 != b.2) |>.map (·.1.1)}"
  let json ← IO.FS.readFile (out1 / "deps.json")
  let html ← IO.FS.readFile (out1 / "index.html")
  match parseGraph json with
  | .error e =>
    fail s!"C64: deps.json does not parse: {e}"
    return none
  | .ok g =>
    -- 先頭の 3 値
    if g.compilerVersion.isEmpty || !(isSha g.compilerHash) then fail s!"C64: deps.json header: naru-compiler `{g.compilerVersion}` / sha256 `{g.compilerHash}`"
    else ok s!"C64: deps.json starts with naru-compiler {g.compilerVersion} sha256:{g.compilerHash}"
    let mut files : List String := []
    for r in roots do files := files ++ (← Naru.listFiles r "naru")
    let rootNames := roots.map fun r => (r.toString.splitOn "/").head!
    let badPrefix := g.sources.filter fun (p, _) => rootNames.any fun n => p.startsWith (n ++ "/")
    let mut badHash : List String := []
    for (p, h) in g.sources do
      let actual ← match ← findInRoots roots p with
        | some f => pure (some (Naru.sha256Hex (← IO.FS.readBinFile f)))
        | none => pure none
      if actual != some h then badHash := badHash ++ [p]
    if g.sources.length == files.length && badPrefix.isEmpty && badHash.isEmpty then
      ok s!"C64: deps.json lists {g.sources.length} sources with root-relative paths (none starts with {rootNames}) and their actual sha256"
    else fail s!"C64: sources: {g.sources.length} listed vs {files.length} files, bad prefix {badPrefix.map (·.1)}, bad hash {badHash}"
    -- HTML の先頭のコメント
    let headerLines := ((html.splitOn "-->").head!).splitOn "\n"
    let want := [s!"naru-compiler: {g.compilerVersion} sha256:{g.compilerHash}"] ++ g.sources.map fun (p, h) => s!"naru-source: {p} sha256:{h}"
    let missing := want.filter fun w => !headerLines.contains w
    if html.startsWith "<!-- naru deps" && missing.isEmpty then
      ok s!"C64: index.html starts with a comment holding the compiler version / hash and the {g.sources.length} sources"
    else fail s!"C64: index.html header lacks {missing.take 3} (starts with `{(html.take 40).toString}`)"
    return some (out1, json, g)

/-- C65: HTML の自己完結。 -/
def checkHtml (label : String) (html json : String) : M Unit := do
  match splitHtml html with
  | none => fail s!"C65 {label}: no single `{dataMarker}` … `</script>` in the HTML"
  | some (outside, embedded) =>
    if embedded == json then ok s!"C65 {label}: the embedded JSON is byte-identical to deps.json ({json.length} characters)"
    else fail s!"C65 {label}: the embedded JSON differs from deps.json ({embedded.length} vs {json.length} characters)"
    let external := (outside.splitOn "\n").filter fun l =>
      (contains l "<script" && contains l " src=") || contains l "<link" || contains l "fetch(" ||
      ((contains l "https://" || contains l "http://") && !(contains l "www.w3.org/2000/svg"))
    if external.isEmpty then ok s!"C65 {label}: no external <script src> / <link> / fetch / URL outside the embedded data"
    else fail s!"C65 {label}: external references: {external.take 3}"
    -- 先頭のコメント(ソースのパスの一覧)はテンプレートではないので語の検査から除く
    let body := match outside.splitOn "-->" with
      | _ :: rest => "-->".intercalate rest
      | [] => outside
    if contains body "Math.random" || hasWord body "Date" then fail s!"C65 {label}: the HTML uses Math.random or Date"
    else ok s!"C65 {label}: no Math.random / Date"
    if contains outside "prefers-color-scheme" then ok s!"C65 {label}: has a prefers-color-scheme branch (light / dark)"
    else fail s!"C65 {label}: no prefers-color-scheme"

/-- C64: 手で書いた期待 JSON の検体。 -/
def checkSample (env : Env) : M Unit := do
  let dir := fixturesDir / "sample"
  let out ← freshDir (workDir / "sample")
  let r ← runDeps env dir #["deps", "--out", out.toString]
  if r.exitCode != 0 then
    fail s!"C64 sample: naru deps exit {r.exitCode}\n{tail (r.stdout ++ r.stderr)}"
    return
  let actual ← IO.FS.readFile (out / "deps.json")
  let expectedRaw ← IO.FS.readFile (dir / "expected" / "deps.json")
  let hash ← match parseGraph actual with
    | .ok g => pure g.compilerHash
    | .error e => fail s!"C64 sample: output does not parse: {e}"; return
  let expected := expectedRaw.replace "{{compiler-sha256}}" hash
  if actual == expected then ok s!"C64 sample: {dir}: deps.json is byte-identical to the hand-written expected/deps.json (with the compiler sha256 substituted): {actual.length} characters"
  else
    let al := actual.splitOn "\n"
    let el := expected.splitOn "\n"
    let firstDiff := (List.range (max al.length el.length)).find? fun i => al[i]? != el[i]?
    fail s!"C64 sample: deps.json differs from expected/deps.json at line {firstDiff.map (· + 1)}: actual `{(firstDiff.bind fun i => al[i]?).getD ""}` expected `{(firstDiff.bind fun i => el[i]?).getD ""}`"
  checkHtml "sample" (← IO.FS.readFile (out / "index.html")) actual

/-- C63: `deps` キーの無い検体と診断の出る検体。 -/
def checkFailures (env : Env) : M Unit := do
  let nokey := fixturesDir / "nokey"
  let r ← runDeps env nokey #["deps"]
  if r.exitCode != 0 then ok s!"C63 nokey: naru deps without --out and without a `deps` key exits {r.exitCode} ({r.stderr.trimAscii.toString})"
  else fail "C63 nokey: naru deps succeeded although naru.toml has no `deps` and no --out was given"
  let out ← freshDir (workDir / "nokey")
  let r2 ← runDeps env nokey #["deps", "--out", out.toString]
  if r2.exitCode == 0 && (← (out / "deps.json").pathExists) then ok "C63 nokey: with --out the graph is written"
  else fail s!"C63 nokey: naru deps --out exit {r2.exitCode}\n{tail (r2.stdout ++ r2.stderr)}"
  -- 診断の出る検体: 複製の出力先に古いファイルを置いて走らせる
  let broken ← freshDir (workDir / "broken")
  let cp ← runProc "cp" #["-R", (fixturesDir / "broken").toString ++ "/.", broken.toString]
  if cp.exitCode != 0 then
    fail s!"C63 broken: cp exit {cp.exitCode}: {tail cp.stderr}"
    return
  let outDir := broken / "out"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "deps.json") "{ \"stale\": true }\n"
  IO.FS.writeFile (outDir / "index.html") "<!-- stale -->\n"
  IO.FS.writeFile (outDir / "extra.txt") "left over\n"
  let before ← snapshotTree [outDir]
  let r3 ← runDeps env broken #["deps"]
  let after ← snapshotTree [outDir]
  if r3.exitCode != 0 && (contains r3.stderr "E011") then ok s!"C63 broken: naru deps exits {r3.exitCode} with the diagnostic ({(r3.stderr.splitOn "\n").head!})"
  else fail s!"C63 broken: expected exit non-zero with E011, got exit {r3.exitCode}\n{tail (r3.stdout ++ r3.stderr)}"
  if before == after && before.length == 3 then ok s!"C63 broken: the output directory `out/` is untouched ({before.length} files, same paths and sha256)"
  else fail s!"C63 broken: the output directory changed: before {before.map (·.1)}, after {after.map (·.1)}"
  let r4 ← runDeps env broken #["deps", "--out", outDir.toString]
  let after2 ← snapshotTree [outDir]
  if r4.exitCode != 0 && before == after2 then ok "C63 broken: with --out the diagnostic still exits non-zero and leaves the directory untouched"
  else fail s!"C63 broken: --out: exit {r4.exitCode}, directory changed {before != after2}"
  -- 有効な生成先(とその配下)は出力先にできない
  let genBefore ← snapshotTree [env.root / "generated"]
  let r5 ← runDeps env env.root #["deps", "--out", "generated"]
  let r6 ← runDeps env env.root #["deps", "--out", "generated/deps"]
  let genAfter ← snapshotTree [env.root / "generated"]
  if r5.exitCode == 2 && r6.exitCode == 2 && genBefore == genAfter then ok "C63: --out generated / --out generated/deps are refused (exit 2) and the generated directory is untouched"
  else fail s!"C63: --out into the generated directory: exit {r5.exitCode} / {r6.exitCode}, changed {genBefore != genAfter}"

/-- C64: 移植ソースに対する独立な検査。 -/
def checkConsensus (roots : List System.FilePath) (g : Parsed) : M Unit := do
  -- 宣言の総数と種類別件数(`naru_test repo` の C60 の列挙)
  let mut files : List String := []
  for r in roots do files := files ++ (← Naru.listFiles r "naru")
  let mut counted : List (Naru.DeclKind × String) := []
  for f in files do
    match ← NaruTest.Repo.scanDeclComments f with
    | .error e => fail s!"C64 decls: {e}"
    | .ok r => counted := counted ++ r.decls.toList.map fun (k, n, _) => (k, n)
  let kindCounts := NaruTest.Repo.declKinds.map fun k => (k.describe, (counted.filter (·.1 == k)).length)
  let jsonCounts := NaruTest.Repo.declKinds.map fun k => (k.describe, (g.decls.filter (·.kind == k.describe)).length)
  if counted.length == g.decls.length && kindCounts == jsonCounts then
    ok s!"C64 decls: {g.decls.length} declarations, per kind {kindCounts.filter (·.2 > 0)} — same as the C60 enumeration of naru_test repo"
  else fail s!"C64 decls: JSON has {g.decls.length} ({jsonCounts.filter (·.2 > 0)}) but the C60 enumeration has {counted.length} ({kindCounts.filter (·.2 > 0)})"
  -- 出現位置の字句
  let mut tokenCache : Std.HashMap String (Array Naru.Token) := {}
  let mut nSites := 0
  let mut badSites : List String := []
  for e in g.declEdges do
    for s in e.sites do
      nSites := nSites + 1
      let toks ← match tokenCache.get? s.path with
        | some t => pure t
        | none =>
          match ← findInRoots roots s.path with
          | none => badSites := badSites ++ [s!"{s.path} not found"]; pure #[]
          | some f =>
            match Naru.lexAll s.path (← IO.FS.readFile f) with
            | .ok t => tokenCache := tokenCache.insert s.path t; pure t
            | .error d => badSites := badSites ++ [s!"{s.path}: {d.render}"]; pure #[]
      match toks.findIdx? (fun t => t.span.line == s.line && t.span.col == s.col) with
      | none => badSites := badSites ++ [s!"{s.path}:{s.line}:{s.col} no token starts there ({e.src} → {e.dst})"]
      | some i =>
        let segments := s.written.splitOn "."
        if !(pathAt toks i segments) then
          badSites := badSites ++ [s!"{s.path}:{s.line}:{s.col} tokens do not spell `{s.written}` ({e.src} → {e.dst})"]
        -- 書かれた経路の区切りのどれかが参照先の名前(経路の最長の接頭辞で解決した宣言の名前)である
        else if !(segments.contains ((e.dst.splitOn ".").getLast!)) then
          badSites := badSites ++ [s!"{s.path}:{s.line}:{s.col} `{s.written}` does not name the target {e.dst}"]
  if badSites.isEmpty then ok s!"C64 sites: all {nSites} reference sites of the {g.declEdges.length} declaration edges start a token whose path spells the written path (lexed from the source) and the written path names the target declaration"
  else fail s!"C64 sites: {badSites.length} of {nSites} sites disagree with the source: {badSites.take 5}"
  -- ファイル間の辺 = 宣言間の辺の集約
  let modOf : Std.HashMap String String := g.decls.foldl (init := {}) fun m d => m.insert d.name d.module
  let modNames := g.modules.map (·.name)
  let modIdx : Std.HashMap String Nat := (modNames.zipIdx).foldl (init := {}) fun m (n, i) => m.insert n i
  let idx (n : String) : Nat := (modIdx.get? n).getD 0
  let mut agg : List ((String × String) × Nat) := []
  for e in g.declEdges do
    let a := (modOf.get? e.src).getD "?"
    let b := (modOf.get? e.dst).getD "?"
    if a == b then continue
    match agg.lookup (a, b) with
    | some n => agg := agg.map fun (k, c) => if k == (a, b) then (k, n + 1) else (k, c)
    | none => agg := agg ++ [((a, b), 1)]
  let aggSorted := agg.mergeSort fun (x, _) (y, _) => idx x.1 < idx y.1 || (idx x.1 == idx y.1 && idx x.2 ≤ idx y.2)
  let importsOf : Std.HashMap String (List String) := g.modules.foldl (init := {}) fun m x => m.insert x.name x.imports
  let expectedFile := aggSorted.map fun ((a, b), n) => ((a, b), n, ((importsOf.get? a).getD []).contains b)
  let actualFile := g.fileEdges.map fun e => ((e.src, e.dst), e.count, e.imported)
  if expectedFile == actualFile then ok s!"C64 fileEdges: the {g.fileEdges.length} file edges are exactly the aggregation of the cross-file declaration edges (count and import flag), in module order"
  else fail s!"C64 fileEdges: differ from the aggregation ({(expectedFile.zip actualFile).filter (fun (x, y) => x != y) |>.take 3})"
  -- 推移簡約: 到達関係が同じで最小(最小性は成分を跨ぐ辺について。成分の中(循環)の辺は生成側がすべて残す定義)
  let compOf : Std.HashMap String Nat := g.modules.foldl (init := {}) fun m x => m.insert x.name x.component
  let full := g.fileEdges.map fun e => (e.src, e.dst)
  let fullAdj := adjacencyOf modNames full
  let redAdj := adjacencyOf modNames g.reduced
  let notSubset := g.reduced.filter fun e => !full.contains e
  let reachDiff := modNames.filter fun n => (reachable fullAdj n).mergeSort (· ≤ ·) != (reachable redAdj n).mergeSort (· ≤ ·)
  let notMinimal := g.reduced.filter fun (a, b) =>
    let without := adjacencyOf modNames (g.reduced.filter (· != (a, b)))
    compOf.get? a != compOf.get? b && (reachable without a).contains b
  let intraMissing := full.filter fun (a, b) => compOf.get? a == compOf.get? b && !(g.reduced.contains (a, b))
  if notSubset.isEmpty && reachDiff.isEmpty && notMinimal.isEmpty && intraMissing.isEmpty then
    ok s!"C64 reduction: the {g.reduced.length} reduced edges are a subset of the {full.length} file edges, keep the reachability of every module, are minimal across components (removing any one loses a reachable module) and keep every edge inside a component"
  else fail s!"C64 reduction: not a subset {notSubset.take 3}, reachability differs for {reachDiff.take 3}, redundant {notMinimal.take 3}, intra-component edges missing {intraMissing.take 3}"
  -- 強連結成分と層
  let mut badComp : List String := []
  for (c, i) in g.components.zipIdx do
    for a in c do
      if compOf.get? a != some i then badComp := badComp ++ [s!"{a} is listed in component {i} but has component {compOf.get? a}"]
      for b in c do
        if a != b && !((reachable fullAdj a).contains b) then badComp := badComp ++ [s!"{a} and {b} share a component but {b} is not reachable from {a}"]
  for a in modNames do
    for b in modNames do
      if a != b && compOf.get? a != compOf.get? b && (reachable fullAdj a).contains b && (reachable fullAdj b).contains a then
        badComp := badComp ++ [s!"{a} and {b} reach each other but are in different components"]
  if g.components.length != (g.modules.map (·.component)).eraseDups.length then badComp := badComp ++ ["the number of components differs from the components used by the modules"]
  let layerOf : Std.HashMap String Nat := g.modules.foldl (init := {}) fun m x => m.insert x.name x.layer
  let mut badLayer : List String := []
  for m in g.modules do
    let deps := (fullAdj.lookup m.name).getD []
    let outside := deps.filter fun d => compOf.get? d != some m.component
    let want := outside.foldl (init := 0) fun acc d => max acc ((layerOf.get? d).getD 0 + 1)
    if m.layer != want then badLayer := badLayer ++ [s!"{m.name}: layer {m.layer} but its dependencies outside its component give {want}"]
    for d in deps do
      if compOf.get? d == some m.component then
        if layerOf.get? d != some m.layer then badLayer := badLayer ++ [s!"{m.name} and {d} share a component but differ in layer"]
      else if (layerOf.get? d).getD 0 ≥ m.layer then badLayer := badLayer ++ [s!"{m.name} (layer {m.layer}) depends on {d} (layer {layerOf.get? d})"]
  let nLayers := (g.stats.lookup "layers").getD 0
  let maxLayer := g.modules.foldl (init := 0) fun acc m => max acc m.layer
  if nLayers != maxLayer + 1 then badLayer := badLayer ++ [s!"stats.layers = {nLayers} but the highest layer is {maxLayer}"]
  if badComp.isEmpty && badLayer.isEmpty then
    ok s!"C64 layers: {g.components.length} strongly connected components ({(g.components.filter (·.length > 1)).length} cyclic) match mutual reachability, and the {nLayers} layers equal the recomputation (0 without dependencies outside the component, else max + 1; edges across components go to a lower layer)"
  else fail s!"C64 layers: {(badComp ++ badLayer).take 5}"
  -- import との差
  let mut badImports : List String := []
  let mut expectedUnused : List (String × String) := []
  for m in g.modules do
    match ← findInRoots roots m.path with
    | none => badImports := badImports ++ [s!"{m.path} not found"]
    | some f =>
      match ← Naru.parseFile f.toString with
      | .error d => badImports := badImports ++ [d.render]
      | .ok parsed =>
        let imps := parsed.imports.toList.map Naru.renderPath
        if imps != m.imports then badImports := badImports ++ [s!"{m.name}: imports {m.imports} but the source has {imps}"]
        if Naru.renderPath parsed.name != m.name then badImports := badImports ++ [s!"{m.path}: module {Naru.renderPath parsed.name} vs {m.name}"]
        for imp in imps do
          if !(g.fileEdges.any fun e => e.src == m.name && e.dst == imp) then expectedUnused := expectedUnused ++ [(m.name, imp)]
  for e in g.fileEdges do
    let want := ((importsOf.get? e.src).getD []).contains e.dst
    if e.imported != want then badImports := badImports ++ [s!"{e.src} → {e.dst}: imported {e.imported} but the import lines say {want}"]
  if g.unusedImports != expectedUnused then badImports := badImports ++ [s!"unusedImports {g.unusedImports.take 3}… vs recomputed {expectedUnused.take 3}…"]
  if badImports.isEmpty then
    ok s!"C64 imports: import lines re-parsed from the {g.modules.length} sources match, {(g.fileEdges.filter (!·.imported)).length} file edge(s) are not in an import line and {g.unusedImports.length} import(s) have no reference, as recomputed"
  else fail s!"C64 imports: {badImports.take 5}"
  -- 統計
  let across := g.declEdges.filter fun e => modOf.get? e.src != modOf.get? e.dst
  let wantStats := [("files", g.modules.length), ("decls", g.decls.length), ("declEdges", g.declEdges.length), ("declEdgesAcrossFiles", across.length),
                    ("fileEdges", g.fileEdges.length), ("reducedEdges", g.reduced.length), ("layers", maxLayer + 1)]
  let statsOk := wantStats.all fun (k, n) => g.stats.lookup k == some n
  if statsOk then ok s!"C64 stats: {wantStats}" else fail s!"C64 stats: {g.stats} vs recomputed {wantStats}"

/-- C66: 鮮度、`.gitattributes`、文書。 -/
def checkFreshness (fresh : System.FilePath) (tracked : System.FilePath) : M Unit := do
  let a ← snapshotTree [fresh]
  let b ← snapshotTree [tracked]
  let rel (base : System.FilePath) (p : String) : String := (p.drop (base.toString.length + 1)).toString
  let aRel := a.map fun (p, h) => (rel fresh p, h)
  let bRel := b.map fun (p, h) => (rel tracked p, h)
  let stale := aRel.filter fun (p, h) => bRel.lookup p != some h
  let extra := bRel.filter fun (p, _) => (aRel.lookup p).isNone
  if stale.isEmpty && extra.isEmpty && !aRel.isEmpty then ok s!"C66: {tracked}/ is fresh: {aRel.map (·.1)} have the same sha256 as a regeneration"
  else fail s!"C66: {tracked}/ is stale or differs from a regeneration: regenerate with `lake exe naru deps` (stale: {stale.map (·.1)}, extra: {extra.map (·.1)})"
  let attr ← runProc "git" #["check-attr", "linguist-generated", (tracked / "deps.json").toString, (tracked / "index.html").toString]
  let setLines := (attr.stdout.splitOn "\n").filter (·.endsWith "linguist-generated: set")
  if attr.exitCode == 0 && setLines.length == 2 then ok s!"C66: git check-attr linguist-generated: both files are set"
  else fail s!"C66: git check-attr linguist-generated (exit {attr.exitCode}): {attr.stdout.trimAscii.toString}"
  let g ← runProc "git" (#["grep", "-l", "naru deps", "--"] ++ docsWithDeps.toArray)
  let hits := ((g.stdout.splitOn "\n").filter (!·.isEmpty)).mergeSort (· ≤ ·)
  if hits == docsWithDeps.mergeSort (· ≤ ·) then ok s!"C66: git grep -l 'naru deps' hits all of {docsWithDeps}"
  else fail s!"C66: git grep -l 'naru deps' -- {docsWithDeps}: {hits} (exit {g.exitCode})"

def checks : M Unit := do
  let root ← IO.currentDir
  let build ← runProc "lake" #["build", "naru"]
  if build.exitCode != 0 then
    fail s!"lake build naru exit {build.exitCode}: {tail build.stderr}"
    return
  ok "lake build naru exit 0"
  let bin := root / ".lake" / "build" / "bin" / "naru"
  if !(← bin.pathExists) then
    fail s!"{bin} not found"
    return
  let env : Env := { root, bin }
  let cfg ← match ← Naru.readConfig Naru.configFileName with
    | .ok cfg => pure cfg
    | .error e => fail s!"{Naru.configFileName}: {e}"; return
  let roots := cfg.rootPaths
  let some depsDir := cfg.depsPath
    | fail s!"C66: {Naru.configFileName} has no `deps = \"<dir>\"` (the tracked dependency graph needs it)"; return
  ok s!"{Naru.configFileName}: sources {roots}, deps {depsDir}"
  IO.FS.createDirAll workDir
  let generatedBefore ← snapshotTree [cfg.generatedPath]
  let result ← checkDeterminism env roots
  checkSample env
  checkFailures env
  let generatedAfter ← snapshotTree [cfg.generatedPath]
  if generatedBefore == generatedAfter && !generatedBefore.isEmpty then
    ok s!"C63: naru deps wrote nothing under {cfg.generatedPath}/ ({generatedBefore.length} files have the same sha256 before and after)"
  else fail s!"C63: {cfg.generatedPath}/ changed during naru deps"
  let grep ← runProc "grep" #["-rn", "\"docs", compilerDir.toString]
  if grep.exitCode == 1 then ok s!"C63: grep -rn '\"docs' {compilerDir}/ finds nothing (no hard-coded output directory)"
  else fail s!"C63: grep -rn '\"docs' {compilerDir}/ exit {grep.exitCode}:\n{tail grep.stdout 600}"
  match result with
  | none => pure ()
  | some (out1, _, g) =>
    checkConsensus roots g
    -- C65: 追跡中の HTML(同じ回の JSON と同一。鮮度は下で確かめる)
    let trackedHtml := depsDir / "index.html"
    let trackedJson := depsDir / "deps.json"
    if (← trackedHtml.pathExists) && (← trackedJson.pathExists) then
      checkHtml depsDir.toString (← IO.FS.readFile trackedHtml) (← IO.FS.readFile trackedJson)
    else fail s!"C65: {trackedHtml} / {trackedJson} not found"
    let tmpl ← IO.FS.readFile templateSource
    if contains tmpl "Math.random" || hasWord tmpl "Date" then fail s!"C65: {templateSource} uses Math.random or Date"
    else ok s!"C65: {templateSource} has no Math.random / Date"
    checkFreshness out1 depsDir

def run : IO UInt32 := runGroup "naru_test deps" checks

end NaruTest.Deps
