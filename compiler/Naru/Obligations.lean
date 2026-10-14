import Naru.Driver
import Naru.Describe
import Naru.Deps
import Naru.Sha256
import Naru.Backend.Statements

/-!
# 証明義務の一覧 `obligations.json`(IDEAL.md C69、用語「証明義務」「束縛 hash」)

`naru compile` が有効な生成先(`--out` も同じ)に Model / Statements と一緒に書く、プロトコル証明(`proofs/`、Lake ライブラリ `Proofs`)が
証明すべき命題の一覧。義務はコンパイル単位のすべての `claim` と `claim bundle`(入れ子の bundle を含む)で、義務の型は生成側が決め、
証明側は変えない(IDEAL.md「不変条件」)。

- 義務の型: 生成 Statements の宣言(`Statements.A.B.name`)を input の引数と仮引数で全量化した Lean の命題。claim は
  `∀ (input の引数) (仮引数), Statements.A.B.claim input… 仮引数…`(どちらも無ければ `Statements.A.B.claim` そのもの)、claim bundle は
  構造体の命題そのもの `∀ (input の引数), Statements.A.B.Bundle input…`。引数の名前と型の書き方は Statements backend と同じ
  (`inputBinders` / `localName` / `ty`)。証明は `Proofs.A.B.name : <義務の型>` の theorem として書く(`naru proofs`、C70)。
- 束縛 hash: 義務の宣言が属する生成 Statements モジュールの import 閉包(生成ファイルの `import` 行を辿る。`NaruStd` は stdlib の hash で
  代表する)にある生成 Model / Statements ファイルの本文(C1 のヘッダ 5 行を除く)から決定的に計算した sha256:
  `sha256("naru-stdlib\n<stdlib の hash>\n" ++ 閉包の各モジュール(名前順)について "<モジュール名>\n<本文の sha256>\n")`。
  時刻・絶対パス・コンパイラ版・宣言コメントの文言には依存しない(ヘッダ行を除くので、コンパイラ版と単位 hash も入らない)。
  証明ファイルの束縛行 `-- naru-obligation: <修飾名> sha256:<hash>` がこれを宣言し、現在の値と違えば失効(`naru proofs`)。
- 並びはモジュールのソースルートからの相対パス順・ソース中の出現順。JSON は依存グラフと同じ正規形(`Deps.J.render`: キー順固定、2 空白、
  UTF-8、LF、末尾改行あり、浮動小数なし)。先頭にコンパイラ版・stdlib 版・ソースの相対パスと sha256 の一覧(C1 の 3 値)。
- claim の無い単位では義務 0 件の一覧を書く。
-/

namespace Naru.Obligations
open Naru.Deps (J)
open Naru.Backend.Model (Env Meta buildEnv inputBinders inputBinder localName ty app)
open Naru.Backend.Statements (stmtName stmtModule)

/-- 1 つの義務。 -/
structure Obligation where
  /-- naru の修飾名(`Consensus.Spec.Claims.finalizedSafe`)。 -/
  qualified : String
  /-- 種類(claim / claim bundle)。 -/
  kind : DeclKind
  /-- naru のモジュール名。 -/
  module : List String
  /-- ソースルートからの相対パス(並び順)。 -/
  path : String
  /-- 生成 Statements の宣言名(`Statements.Consensus.Spec.Claims.finalizedSafe`)。 -/
  lean : String
  /-- 義務が属する生成 Statements モジュール(`Statements.Consensus.Spec.Claims`)。 -/
  stmtModule : String
  /-- 義務の型(Lean の命題)。 -/
  type : String
  /-- 宣言コメントの 1 行目(`Naru.declComment` と同じ規則)。 -/
  summary : String
  /-- それを項目に持つ claim bundle の修飾名(並び順)。 -/
  bundles : List String
  /-- 束縛 hash(`finish` が埋める)。 -/
  hash : String := ""
deriving Inhabited

/-- 証明の theorem の名前: 生成 Statements の宣言名の先頭 `Statements.` を `Proofs.` に替える(`naru proofs` の対応付け。C70)。 -/
def theoremName (lean : String) : String :=
  if lean.startsWith "Statements." then "Proofs." ++ (lean.drop "Statements.".length).toString else "Proofs." ++ lean

/-- claim の義務の型。 -/
def claimType (env : Env) (k : String) (params : List Core.Param) : String :=
  let binders := inputBinders env k ++ params.map fun (p : Core.Param) => s!"({localName p.name} : {ty p.ty})"
  let call := app (stmtName k) ((env.inputs.getD k []).map inputBinder ++ params.map fun (p : Core.Param) => localName p.name)
  if binders.isEmpty then call else "∀ " ++ " ".intercalate binders ++ ", " ++ call

/-- claim bundle の義務の型(構造体の命題そのもの)。 -/
def bundleType (env : Env) (k : String) : String :=
  let binders := inputBinders env k
  let call := app (stmtName k) ((env.inputs.getD k []).map inputBinder)
  if binders.isEmpty then call else "∀ " ++ " ".intercalate binders ++ ", " ++ call

/-- 1 つのコンパイル単位の義務(束縛 hash は空)。`prefix_` はソースルートの接頭辞(`<root>/`。空なら渡されたパスのまま)、
`texts` は各ファイルの本文(宣言コメントの要旨を読む)。並びはモジュールの相対パス順・ソース中の出現順。 -/
def collect (prefix_ : String) (checked : Checked) (texts : List (String × String)) : List Obligation := Id.run do
  let env := buildEnv checked.core checked.recursions
  -- 項目 → それを持つ bundle(Core のモジュールの順)
  let mut bundlesOf : List (String × List String) := []
  for m in checked.core do
    for d in m.decls do
      if let .claimBundle k _ items := d then
        for (_, target) in items do
          match bundlesOf.lookup target with
          | some _ => bundlesOf := bundlesOf.map fun (t, xs) => if t == target then (t, xs ++ [k]) else (t, xs)
          | none => bundlesOf := bundlesOf ++ [(target, [k])]
  let mut perModule : List (String × List Obligation) := []
  for m in checked.core do
    let path := Deps.stripPrefix prefix_ m.file
    let lines := (((texts.lookup m.file).getD "").splitOn "\n").toArray
    let ast := checked.mods.find? (·.file == m.file)
    let summaryOf (k : String) : String :=
      match ast with
      | none => ""
      | some am =>
        match am.decls.find? (fun (d : Decl) => (d.kind == .claim || d.kind == .claimBundle) && renderPath (am.name ++ [d.name]) == k) with
        | some d => (declComment lines d).head?.getD ""
        | none => ""
    let mut obs : List Obligation := []
    for d in m.decls do
      match d with
      | .fn k _ .claim params _ _ =>
        obs := obs ++ [{ qualified := k, kind := .claim, module := m.name, path, lean := stmtName k, stmtModule := stmtModule m.name,
                         type := claimType env k params, summary := summaryOf k, bundles := (bundlesOf.lookup k).getD [] }]
      | .claimBundle k _ _ =>
        obs := obs ++ [{ qualified := k, kind := .claimBundle, module := m.name, path, lean := stmtName k, stmtModule := stmtModule m.name,
                         type := bundleType env k, summary := summaryOf k, bundles := (bundlesOf.lookup k).getD [] }]
      | _ => pure ()
    if !obs.isEmpty then perModule := perModule ++ [(path, obs)]
  let sorted := perModule.mergeSort fun a b => a.1 ≤ b.1
  return sorted.flatMap (·.2)

/-! ## 束縛 hash -/

/-- 生成ファイルの本文: C1 のヘッダ 5 行(`-- Generated by …` / `naru-compiler` / `naru-stdlib` / `naru-source` / `naru-unit`)を除いたもの。 -/
def bodyOf (content : String) : String := "\n".intercalate ((content.splitOn "\n").drop 5)

/-- 生成先からの相対パス → 生成モジュール名(`Statements/A/B.lean` → `Statements.A.B`)。 -/
def moduleOfPath (rel : String) : String :=
  let base := if rel.endsWith ".lean" then (rel.dropEnd ".lean".length).toString else rel
  base.replace "/" "."

/-- `import` 行のモジュール名(`«»` は外す)。 -/
def importsOf (content : String) : List String :=
  (content.splitOn "\n").filterMap fun l =>
    if l.startsWith "import " then some (((l.drop "import ".length).toString.trimAscii.toString.replace "«" "").replace "»" "") else none

/-- `start` から生成ファイルの `import` 行で到達できる生成モジュール(`start` を含む。名前順、重複なし)。`NaruStd` と生成物に無い
モジュールは辿らない。 -/
partial def closure (files : Array (String × String)) (start : String) : List String :=
  let byName : List (String × String) := files.toList.map fun (rel, content) => (moduleOfPath rel, content)
  let rec go (todo : List String) (seen : List String) : List String :=
    match todo with
    | [] => seen
    | m :: rest =>
      if seen.contains m then go rest seen
      else
        match byName.lookup m with
        | none => go rest seen
        | some content => go (importsOf content ++ rest) (seen ++ [m])
  (go [start] []).mergeSort (· ≤ ·)

/-- 束縛 hash: stdlib の hash と、閉包の各モジュール(名前順)の名前と本文の sha256 を連ねた文字列の sha256。 -/
def bindingHash (stdlibHash : String) (files : Array (String × String)) (stmtModule : String) : String :=
  let byName : List (String × String) := files.toList.map fun (rel, content) => (moduleOfPath rel, content)
  let entries := (closure files stmtModule).map fun m => s!"{m}\n{sha256HexOfString (bodyOf ((byName.lookup m).getD ""))}\n"
  sha256HexOfString (s!"naru-stdlib\n{stdlibHash}\n" ++ "".intercalate entries)

/-- 全単位の義務に束縛 hash を埋め、並び(相対パス順・出現順)を整える。`files` は生成先に書く全ファイル(相対パス, 内容)。 -/
def finish (stdlibHash : String) (files : Array (String × String)) (obs : List Obligation) : List Obligation :=
  let withHash := obs.map fun o => { o with hash := bindingHash stdlibHash files o.stmtModule }
  -- 単位をまたいだ並び: 相対パス順(同じパスの中はもとの順)
  let paths := (withHash.map (·.path)).eraseDups.mergeSort (· ≤ ·)
  paths.flatMap fun p => withHash.filter (·.path == p)

/-! ## JSON -/

def toJson (info : Meta) (sources : List (String × String)) (obs : List Obligation) : J :=
  J.obj
    [ ("naru-compiler", .str info.compilerVersion), ("naru-compiler-sha256", .str info.compilerHash),
      ("naru-stdlib", .str info.stdlibVersion), ("naru-stdlib-sha256", .str info.stdlibHash),
      ("sources", .arr (sources.map fun (p, h) => .obj [ ("path", .str p), ("sha256", .str h) ])),
      ("obligations", .arr (obs.map fun o =>
        .obj [ ("name", .str o.qualified), ("kind", .str o.kind.describe), ("module", .str (renderPath o.module)), ("lean", .str o.lean),
               ("theorem", .str (theoremName o.lean)), ("type", .str o.type), ("sha256", .str o.hash), ("summary", .str o.summary),
               ("bundles", .arr (o.bundles.map J.str)) ])) ]

/-- `obligations.json` の本文(末尾に改行 1 つ)。`sources` はソースルートからの相対パスと sha256(パス順)。 -/
def render (info : Meta) (sources : List (String × String)) (obs : List Obligation) : String :=
  (toJson info (sources.mergeSort fun a b => a.1 ≤ b.1) obs).render ++ "\n"

def fileName : String := "obligations.json"

end Naru.Obligations
