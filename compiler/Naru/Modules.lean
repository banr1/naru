import Naru.Resolve
import Naru.Backend.Statements

/-!
# モジュール構造の共通検査(E017、IDEAL.md C18)

生成前の意味検査として `Driver.compileSources` が走らせる。CLI の `compile`(出力指定あり / なし)と言語サーバー `naru lsp` の
すべてが同じこの検査を通るので、同じ入力・コンパイル単位に対して同じ E017 を同じ行・列に出す(backend の段の検査は安全網)。

- 同名のモジュール(2 つ以上のファイルが同じ `module A.B` を宣言する): それぞれのファイルの `module` 行(名前の位置)に E017。
  生成 Lean は 1 モジュール 1 ファイルなので同名は共存できない。構文解析の直後(名前解決の前)に検査する。
- モジュールの循環: 生成 Model の import グラフ(`Backend.Model.modelGraph`: 出力する runtime 宣言が参照する他のモジュール)と
  生成 Statements の import グラフ(`Backend.Statements.specGraph`: spec 宣言が参照する他のモジュールの spec 宣言)のそれぞれで、
  循環に関与する辺 `A → B`(`A` から `B` へ参照があり、`B` から `A` に戻れる)ごとに、`A` の中でその参照を作る最初の宣言の、
  `B` の宣言への最初の参照(名前解決の索引 `Resolve.Ref`: 値の位置・型の位置の名前)の行・列に E017 を 1 つ出す。参照が
  構文上その宣言に現れない(使う input の署名を通した依存)ときはその宣言の位置に出す。循環のすべての辺に出るので、
  循環を解消する編集でどれか 1 つの辺が消えれば、関係するファイルすべての診断が消える。
  参照が構文上その宣言に現れない依存(推論された型 — 欄の参照 `make().x` の record や呼出しの結果の型 — や、使う input の署名を通した
  依存)は、その宣言の名前の位置に出す(検体 `tests/units/reject/inferred_cycle`)。
  グラフは backend と同じ関数で計算するので、生成の規則(どの宣言を出力し何を import するか)を変えれば検査も揃う。
-/

namespace Naru.Modules
open Backend.Model (Env buildEnv declRefs emitted modelGraph)
open Backend.Statements (specGraph isSpecKey isSpecDecl)

/-- 同名のモジュール: 同じ名前を宣言するすべてのファイルの `module` 行に E017(他の所在を列挙する)。 -/
def duplicates (mods : Array Module) : Array Diagnostic := Id.run do
  let mut out : Array Diagnostic := #[]
  let indexed := mods.toList.zipIdx
  for (m, i) in indexed do
    let others := indexed.filter fun (o, j) => j != i && o.name == m.name
    if others.isEmpty then continue
    let places := ", ".intercalate (others.map fun (o, _) => s!"{o.file}:{o.nameSpan.line}:{o.nameSpan.col}")
    let msg := s!"module `{renderPath m.name}` is also declared at {places}; each module needs its own name (it becomes one generated Lean file)"
    out := out.push { file := m.file, span := m.nameSpan, code := Code.moduleStructure, msg }
  return out

/-- `start` から辺 1 つ以上で到達できるモジュール。 -/
partial def reachable (adj : List (List String × List (List String))) (start : List String) : List (List String) :=
  let rec go (todo : List (List String)) (seen : List (List String)) : List (List String) :=
    match todo with
    | [] => seen
    | x :: rest =>
      let next := ((adj.lookup x).getD []).filter fun y => !seen.contains y
      go (next ++ rest) (seen ++ next)
  let init := (adj.lookup start).getD []
  go init init

/-- `src` から `dst` への経路(辺 1 つ以上。幅優先で最短)。無ければ none。 -/
partial def pathBetween (adj : List (List String × List (List String))) (src dst : List String) :
    Option (List (List String)) :=
  let rec go (queue : List (List String × List (List String))) (seen : List (List String)) : Option (List (List String)) :=
    match queue with
    | [] => none
    | (cur, path) :: rest =>
      let nexts := (adj.lookup cur).getD []
      if nexts.contains dst then some (path ++ [dst])
      else
        let fresh := nexts.filter fun n => !seen.contains n
        go (rest ++ fresh.map fun n => (n, path ++ [n])) (seen ++ fresh)
  go [(src, [src])] [src]

/-- 循環に関与する辺 `a → b` の診断。`pick` はその辺を作りうる宣言(Model なら出力する runtime 宣言、Statements なら spec 宣言)、
`targetOk` は参照先(Statements なら spec 宣言だけ)。`a` の中で `b` を参照する最初の宣言を探し、その宣言の中の `b` への最初の参照
(索引 `refs`。行・列の順)の位置に出す。参照が構文上現れなければ(推論された型や、使う input の署名を通した依存)宣言の名前の位置。 -/
def edgeDiagnostic (env : Env) (mods : Array Module) (refs : Array Resolve.Ref) (a : Core.Module) (b : List String)
    (cycle : List (List String)) (pick : Core.Decl → Bool) (targetOk : String → Bool) (what verb : String) : Option Diagnostic := do
  let (d, viaKey) ← a.decls.toList.findSome? fun d =>
    if pick d then ((declRefs env d).find? fun r => targetOk r && env.moduleOf.get? r == some b).map (d, ·) else none
  let cycleStr := " → ".intercalate (cycle.map fun n => s!"`{renderPath n}`")
  let advice := "generated Lean modules import each other, so move the shared declarations into one module"
  let earlier (x y : Resolve.Ref) : Bool :=
    x.span.line < y.span.line || (x.span.line == y.span.line && x.span.col < y.span.col)
  let candidates := refs.toList.filter fun x =>
    x.file == a.file && x.declName == d.name && x.target.module == b && targetOk x.target.qualified
  let first := candidates.foldl (init := (none : Option Resolve.Ref)) fun acc x =>
    match acc with
    | none => some x
    | some y => if earlier x y then some x else some y
  match first with
  | some x =>
    some { file := a.file, span := x.span, code := Code.moduleStructure,
           msg := s!"{what} `{renderPath a.name}` {verb} to module `{renderPath b}` here ({d.kind.describe} `{d.name}` uses `{x.target.qualified}`), which closes the cycle {cycleStr}; {advice}" }
  | none =>
    let span := ((mods.find? (·.file == a.file)).bind fun m => m.decls.find? (·.name == d.name)).map (·.span) |>.getD {}
    some { file := a.file, span, code := Code.moduleStructure,
           msg := s!"{what} `{renderPath a.name}` {verb} to module `{renderPath b}` ({d.kind.describe} `{d.name}` uses `{viaKey}` without naming it: through an inferred type, such as the record of a field access or the result of a call, or through the signature of an input it uses), which closes the cycle {cycleStr}; {advice}" }

/-- 1 つのグラフの循環に関与するすべての辺の診断(モジュールの順、依存先の名前順)。 -/
def cyclesOf (env : Env) (mods : Array Module) (core : Array Core.Module) (refs : Array Resolve.Ref)
    (graph : List (List String × List (List String))) (pick : Core.Decl → Bool) (targetOk : String → Bool) (what verb : String) :
    Array Diagnostic := Id.run do
  let mut out : Array Diagnostic := #[]
  for (a, deps) in graph do
    for b in deps do
      if !(reachable graph b).contains a then continue
      let some m := core.find? (·.name == a) | continue
      let cycle := a :: (pathBetween graph b a).getD [b, a]
      if let some d := edgeDiagnostic env mods refs m b cycle pick targetOk what verb then out := out.push d
  return out

/-- モジュールの循環(E017): 生成 Model の import グラフと生成 Statements の import グラフのそれぞれで、循環に関与する辺ごとに 1 つ。
名前解決と型検査を通った Core と、名前解決の参照の索引から計算する。 -/
def cycles (mods : Array Module) (core : Array Core.Module) (refs : Array Resolve.Ref) : Array Diagnostic :=
  let env := buildEnv core #[]
  cyclesOf env mods core refs (modelGraph env core) emitted (fun _ => true) "module" "refers" ++
    cyclesOf env mods core refs (specGraph env core) isSpecDecl (isSpecKey env) "the spec declarations of module" "refer"

end Naru.Modules
