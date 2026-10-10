import NaruTest.Common
import NaruSem.Quote
import NaruSem.Denote

/-!
# `naru_test semantics` — コンパイラ意味論保存の検査入口と、実際の Core・実生成宣言の検査(IDEAL.md C39 / C40 / C44 / C45 / C46)

1. C45 の検査入口 `lake build NaruSem`(意味論・一般定理・検体・公理監査を Lean kernel に検査させる)が exit 0。続けて
   `lake env lean semantics/NaruSem.lean` で公理監査の出力(`audit ok: <定数> depends on axioms […]`)を取り直し、必須の定理
   (`requiredTheorems`)がすべて監査されていて、許容しない依存が 0 件であることを確かめる。
2. C39: 検体 `tests/accept/sem_core.naru` を実際の compiler 経路(`Naru.compileFiles`)でコンパイルし、`c39Decls` の各宣言(今回の保存対象の
   構文を 1 つずつ使う)の Core を Lean の項として引用した検査プログラム `.lake/naru/test/semantics/Scope.lean` を書き、モジュール `Scope` として
   `lean` でコンパイルする: 各宣言の適格性(`wtR` / `wtS` = 期待の型。`decide` で kernel が計算する)と、引用した Core が compiler の Core と一致すること
   (`NaruSem.Quote.checkDecls` が同じソースを再びコンパイルして照合する)。
3. C40 / C44 / C46(Model の基礎段階): 同じ検体を実際の CLI(`lake exe naru compile --out`)で `.lake/naru/test/semantics/gen/` に生成し、
   生成 Model `Model/Sem/Core.lean` をそのまま Lean のモジュールにして、検査プログラム `ModelCheck.lean` が各基礎宣言(`c40Decls`: 引用した Core が
   `NaruSem.basic` な runtime 宣言)について、任意の引数で実生成宣言の値が Lean での読み `denoteN` / `denoteB` と等しいこと(`conn_<f>`: kernel の
   定義的等しさ `rfl`)と、そこから独立意味論の結果が実生成宣言の値であること(`pres_<f>`: `check_sound_nat` / `check_sound_bool`)を kernel に
   検査させ、公理監査に載せる。一般定理の量化の形(任意の文脈・式・型・環境)も同じプログラムで照合する。
   負の検体 `ModelWrong.lean`(隔離: 実生成文字列から `&&` / `||` を取り違えた `Wrong.logic` と、束縛を取り違えた `Wrong.letShadow` を作る)は
   Lean の型検査を通るが、同じ正しい入力 Core への接続検査だけが失敗する(正しい出力の対照は同じファイルで成功する)。
4. C45: 監査が禁止依存を失敗にすることを、`sorry` / `native_decide` / 存在しない定数の 3 つの負の検体で確かめる(`lean` が exit 非 0)。
-/

namespace NaruTest.Semantics
open NaruTest

def source : String := "tests/accept/sem_core.naru"
def outDir : System.FilePath := ".lake" / "naru" / "test" / "semantics"
def genDir : System.FilePath := outDir / "gen"
def rootFile : String := "semantics/NaruSem.lean"

/-- 公理監査に現れなければならない定理(C39: 全域性・一意性。C40 / C44: 基礎段階の保存と接続検査の健全性、異なる表現の対応関係)。 -/
def requiredTheorems : List String :=
  [ "NaruSem.eval_total", "NaruSem.Eval_unique", "NaruSem.Sem_exists", "NaruSem.Sem_unique",
    "NaruSem.denote_sound", "NaruSem.preserve_nat", "NaruSem.preserve_bool", "NaruSem.check_sound_nat", "NaruSem.check_sound_bool",
    "NaruSem.CmpOp.leanBool_eq", "NaruSem.EqOp.leanNat_eq", "NaruSem.EqOp.leanBool_eq" ]

/-- 検体の宣言(修飾名, spec か)。今回の保存対象の各構文を 1 つずつ。欠けていれば FAIL。 -/
def c39Decls : List (String × Bool) :=
  [ ("Sem.Core.litNat", false), ("Sem.Core.litBool", false), ("Sem.Core.useVar", false), ("Sem.Core.useLet", false),
    ("Sem.Core.letShadow", false), ("Sem.Core.useIf", false), ("Sem.Core.arith", false), ("Sem.Core.minMax", false),
    ("Sem.Core.cmpNat", false), ("Sem.Core.cmpBool", false), ("Sem.Core.eqNat", false), ("Sem.Core.eqBool", false),
    ("Sem.Core.logic", false), ("Sem.Core.matchNat", false), ("Sem.Core.matchBool", false), ("Sem.Core.matchShadow", false),
    ("Sem.Core.specLit", true), ("Sem.Core.specVar", true), ("Sem.Core.specCmp", true), ("Sem.Core.specCmpBool", true),
    ("Sem.Core.specLogic", true), ("Sem.Core.specEq", true), ("Sem.Core.specArith", true), ("Sem.Core.specLetVal", true),
    ("Sem.Core.specLetProp", true), ("Sem.Core.specLetShadow", true), ("Sem.Core.specIfBool", true), ("Sem.Core.specIfProp", true),
    ("Sem.Core.specForall", true), ("Sem.Core.specExists", true), ("Sem.Core.specMatch", true), ("Sem.Core.specMatchProp", true) ]

/-- C40 の基礎段階の runtime 宣言(リテラル・局所名・let・if・算術・min / max・比較・等値・論理)。`NaruSem.basic` が真でなければならず、
実生成宣言への接続(`conn_<f>`)と保存(`pres_<f>`)を検査する。 -/
def c40Decls : List String :=
  [ "Sem.Core.litNat", "Sem.Core.litBool", "Sem.Core.useVar", "Sem.Core.useLet", "Sem.Core.letShadow", "Sem.Core.useIf",
    "Sem.Core.arith", "Sem.Core.minMax", "Sem.Core.cmpNat", "Sem.Core.cmpBool", "Sem.Core.eqNat", "Sem.Core.eqBool", "Sem.Core.logic" ]

/-- まだ基礎段階に入らない runtime 宣言(`match`: C41)。`NaruSem.basic` が偽であることを明示的に検査する(段階の境界)。 -/
def c41Decls : List String := ["Sem.Core.matchNat", "Sem.Core.matchBool", "Sem.Core.matchShadow"]

def heading (title : String) : M Unit := IO.println s!"== {title}"

def elapsed (start : Nat) : IO String := do
  let ms := (← IO.monoMsNow) - start
  return s!"{ms / 1000}.{(ms % 1000) / 100}s"

/-- 子プロセスを 1 項目として走らせ、exit code を期待と照合する。 -/
def step (label : String) (cmd : String) (args : Array String) (expectExit : UInt32 := 0)
    (cwd : Option System.FilePath := none) (env : Array (String × Option String) := #[]) : M IO.Process.Output := do
  let t ← IO.monoMsNow
  let r ← runProc cmd args cwd env
  let shown := s!"{cmd} {" ".intercalate args.toList}"
  if r.exitCode == expectExit then ok s!"{label}: `{shown}` exit {r.exitCode} ({← elapsed t})"
  else fail s!"{label}: `{shown}` exit {r.exitCode} (expected {expectExit})\n{tail r.stdout 1500}\n{tail r.stderr 1500}"
  return r

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

def countOf (s sub : String) : Nat := (s.splitOn sub).length - 1

def ctxOfParams (ps : List Naru.Core.Param) : NaruSem.Ctx :=
  NaruSem.Ctx.ofList (ps.filterMap fun p => match p.ty with
    | .nat => some (p.name, .nat)
    | .bool => some (p.name, .bool)
    | _ => none)

def sctxOfParams (ps : List Naru.Core.Param) : NaruSem.SCtx :=
  NaruSem.SCtx.ofList (ps.filterMap fun p => match p.ty with
    | .nat => some (p.name, .val .nat)
    | .bool => some (p.name, .val .bool)
    | _ => none)

def tyTerm : NaruSem.Ty → String
  | .nat => "NaruSem.Ty.nat"
  | .bool => "NaruSem.Ty.bool"

def styTerm : NaruSem.STy → String
  | .val t => s!"(NaruSem.STy.val {tyTerm t})"
  | .prop => "NaruSem.STy.prop"

/-- 修飾名 `A.B.f` → 検査プログラムの中の名前 `f`。 -/
def shortName (key : String) : String := (key.splitOn ".").getLast!

/-- 公理監査の出力から監査された定数の名前。 -/
def auditedNames (out : String) : List String :=
  ((out.splitOn "\n").filter fun l => contains l "audit ok:").filterMap fun l =>
    ((l.splitOn "audit ok: ").getD 1 "").splitOn " " |>.head?

/-- 検査プログラム `Scope.lean`(モジュール `Scope`): 引用した Core(`core_<f>`)と文脈(`ctx_<f>`)、適格性の定理(`decide`)、引用の一致の照合(`run_cmd`)。 -/
def scopeProgram (quoted : List (String × String × String × String × Bool)) : String :=
  let defs := quoted.map fun (key, core, ctx, ty, spec) =>
    let n := shortName key
    let wt := if spec then
      s!"theorem wt_{n} : NaruSem.wtS ctx_{n} core_{n} = some {ty} := by decide\n" ++
      s!"theorem form_{n} : (NaruSem.wtS ctx_{n} core_{n}).map NaruSem.STy.isForm = some true := by decide\n"
    else s!"theorem wt_{n} : NaruSem.wtR ctx_{n} core_{n} = some {ty} := by decide\n"
    s!"-- {key}\ndef core_{n} : Naru.Core.Expr :=\n  {core}\ndef ctx_{n} := {ctx}\n{wt}\n"
  let pairs := quoted.map fun (key, _, _, _, _) => s!"({key.quote}, core_{shortName key})"
  s!"-- naru_test semantics (C39): generated from NaruTest/Semantics.lean. The Core of each declaration of {source} as produced by the compiler.\n" ++
  "import NaruSem\n\n" ++
  "".intercalate defs ++
  s!"-- the quoted Core is the Core the compiler produces for the same source (C44)\nrun_cmd NaruSem.Quote.checkDecls {source.quote} [{", ".intercalate pairs}]\n"

/-- 仮引数 → (Lean の束縛, 環境の項目, 実引数)。Nat / Bool 以外は `none`。 -/
def binderOf (p : Naru.Core.Param) : Option (String × String × String) :=
  match p.ty with
  | .nat => some (s!"(«{p.name}» : Nat)", s!"({p.name.quote}, NaruSem.Val.nat «{p.name}»)", s!"«{p.name}»")
  | .bool => some (s!"(«{p.name}» : Bool)", s!"({p.name.quote}, NaruSem.Val.bool «{p.name}»)", s!"«{p.name}»")
  | _ => none

/-- 1 つの基礎宣言の接続と保存: (修飾名, 仮引数, 型) → `conn_<f>`(実生成宣言 = 読み、`rfl`)と `pres_<f>`(独立意味論の結果 = 実生成宣言の値)。 -/
def connOf (key : String) (params : List Naru.Core.Param) (t : NaruSem.Ty) : String :=
  let n := shortName key
  let lean := Naru.Backend.Model.leanName key
  let bs := params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let (den, val, sound) := match t with
    | .nat => ("NaruSem.denoteN", "NaruSem.Val.nat", "NaruSem.check_sound_nat")
    | .bool => ("NaruSem.denoteB", "NaruSem.Val.bool", "NaruSem.check_sound_bool")
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let lam (body : String) : String := if bs.isEmpty then body else s!"fun {args} => {body}"
  let conn := if bs.isEmpty then s!"conn_{n}" else s!"conn_{n} {args}"
  s!"-- {key}: the generated declaration `{lean}` is definitionally the Lean reading of its Core; hence its value is the meaning of the Core\n" ++
  s!"theorem conn_{n} : {quant s!"{call} = {den} (NaruSem.Env.ofList {env}) core_{n}"} := {lam "rfl"}\n" ++
  s!"theorem pres_{n} : {quant s!"NaruSem.eval (NaruSem.Env.ofList {env}) core_{n} = some ({val} ({call}))"} :=\n" ++
  s!"  {lam s!"{sound} {env} wt_{n} (by decide) ({conn})"}\n\n"

/-- 検査プログラム `ModelCheck.lean`: 実生成 Model を import し、一般定理の量化の形と、各基礎宣言の接続・保存を kernel に検査させて監査する。 -/
def modelProgram (decls : List (String × List Naru.Core.Param × NaruSem.Ty)) : String :=
  let names := decls.flatMap fun (key, _, _) => [s!"conn_{shortName key}", s!"pres_{shortName key}"]
  s!"-- naru_test semantics (C40 / C44): generated from NaruTest/Semantics.lean. Connection of the generated Model of {source} to the Core semantics.\n" ++
  "import Scope\nimport Model.Sem.Core\n\n" ++
  "-- the general theorem quantifies over any context, expression, type and matching environment (C40)\n" ++
  "example : ∀ (Γ : NaruSem.Ctx) (e : Naru.Core.Expr) (t : NaruSem.Ty) (ρ : NaruSem.Env),\n" ++
  "    NaruSem.wtR Γ e = some t → NaruSem.basic e = true → Γ = ρ.ty → NaruSem.eval ρ e = some (NaruSem.denoteV ρ t e) :=\n" ++
  "  fun _ _ _ _ h hb hρ => NaruSem.denote_sound h hb _ hρ\n\n" ++
  "".intercalate (decls.map fun (key, params, t) => connOf key params t) ++
  s!"#audit_axioms {" ".intercalate names}\n"

/-- 生成ファイルの中の 1 つの宣言の本文(`def <名前> ` で始まる行から空行まで)。 -/
def declText (content : String) (leanName : String) : Option String := Id.run do
  let lines := content.splitOn "\n"
  let mut acc : List String := []
  let mut inside := false
  for l in lines do
    if !inside then
      if l.startsWith s!"def {leanName} " || l.startsWith s!"def {leanName} :" then
        inside := true
        acc := [l]
    else
      if l.trimAscii.isEmpty then break
      acc := acc ++ [l]
  if acc.isEmpty then none else some ("\n".intercalate acc)

/-- `&&` と `||` を取り違える。 -/
def swapAndOr (s : String) : String :=
  ((s.replace "&&" "\x01").replace "||" "&&").replace "\x01" "||"

/-- 負の検体 `ModelWrong.lean`: 実生成文字列から作った誤出力(型検査は通る)への接続検査は失敗し、正しい出力の対照は成功する。 -/
def wrongProgram (wrongLogic wrongLetShadow : String) : String :=
  "-- naru_test semantics (C46): generated from NaruTest/Semantics.lean. Isolated mistranslations of the generated Model (they type-check) must fail the connection check.\n" ++
  "import Scope\nimport Model.Sem.Core\n\n" ++
  "-- `&&` and `||` swapped in the generated text of `logic`\n" ++ wrongLogic ++ "\n\n" ++
  "-- the second binding renamed in the generated text of `letShadow` (the result refers to the wrong binding)\n" ++ wrongLetShadow ++ "\n\n" ++
  "-- controls: the correct generated declarations connect\n" ++
  "theorem conn_logic_ok : ∀ («a» : Bool) («b» : Bool), Model.Sem.Core.logic «a» «b» = NaruSem.denoteB (NaruSem.Env.ofList [(\"a\", NaruSem.Val.bool «a»), (\"b\", NaruSem.Val.bool «b»)]) core_logic := fun «a» «b» => rfl\n" ++
  "theorem conn_letShadow_ok : ∀ («x» : Nat), Model.Sem.Core.letShadow «x» = NaruSem.denoteN (NaruSem.Env.ofList [(\"x\", NaruSem.Val.nat «x»)]) core_letShadow := fun «x» => rfl\n\n" ++
  "-- the mistranslations must not connect to the same (correct) input Core\n" ++
  "theorem conn_wrong_logic : ∀ («a» : Bool) («b» : Bool), Wrong.logic «a» «b» = NaruSem.denoteB (NaruSem.Env.ofList [(\"a\", NaruSem.Val.bool «a»), (\"b\", NaruSem.Val.bool «b»)]) core_logic := fun «a» «b» => rfl\n" ++
  "theorem conn_wrong_letShadow : ∀ («x» : Nat), Wrong.letShadow «x» = NaruSem.denoteN (NaruSem.Env.ofList [(\"x\", NaruSem.Val.nat «x»)]) core_letShadow := fun «x» => rfl\n"

def checks : M Unit := do
  let t0 ← IO.monoMsNow
  IO.FS.createDirAll outDir
  heading "C45 entry point"
  let _ ← step "C45: build the semantics, the general theorems, the specimens and the axiom audit" "lake" #["build", "NaruSem"]
  let a ← step "C45: re-run the axiom audit of the root file" "lake" #["env", "lean", rootFile]
  let auditLines := (a.stdout.splitOn "\n").filter fun l => contains l "audit ok:"
  let audited := auditedNames a.stdout
  let missing := requiredTheorems.filter fun n => !audited.contains n
  if a.exitCode == 0 && missing.isEmpty && !(contains a.stdout "forbidden") && !(contains a.stderr "forbidden") then
    ok s!"C45: the audit covers {auditLines.length} constant(s) including {requiredTheorems} with 0 forbidden dependencies (allowed: propext / Classical.choice / Quot.sound)"
  else fail s!"C45: audit: exit {a.exitCode}, required theorems not audited: {missing}\n{tail a.stdout 1500}\n{tail a.stderr 1500}"
  let _ ← step "C44: build the Model stdlib the generated Model imports" "lake" #["build", "NaruStd"]
  let e ← runProc "lake" #["env", "printenv", "LEAN_PATH"]
  let leanPath := e.stdout.trimAscii.toString
  if e.exitCode == 0 && !leanPath.isEmpty then ok "lake env printenv LEAN_PATH" else fail s!"lake env printenv LEAN_PATH: exit {e.exitCode}"
  heading "C39 scope of the Core produced by the compiler"
  let (diags, checked) ← Naru.compileFiles [source]
  if diags.isEmpty then ok s!"C39: {source} compiles without diagnostics ({checked.core.size} module(s))"
  else
    fail s!"C39: {source}: {diags.size} diagnostic(s): {diags.toList.map (·.msg)}"
    return
  let mut quoted : List (String × String × String × String × Bool) := []
  let mut basics : List (String × List Naru.Core.Param × NaruSem.Ty) := []
  for (key, spec) in c39Decls do
    match NaruSem.Quote.fnOf? key checked.core with
    | none => fail s!"C39: {source} has no declaration `{key}`"
    | some (_, none) => fail s!"C39: `{key}` has no body"
    | some (params, some body) =>
      match NaruSem.Quote.ctxOf params spec with
      | none => fail s!"C39: `{key}` has a parameter outside Nat / Bool"
      | some ctx =>
        if spec then
          match NaruSem.wtS (sctxOfParams params) body with
          | some τ =>
            if τ.isForm then
              ok s!"C39: `{key}` (spec) is in scope: wtS = {styTerm τ}"
              quoted := quoted ++ [(key, NaruSem.Quote.expr body, ctx, styTerm τ, true)]
            else fail s!"C39: `{key}` (spec) has the value type {styTerm τ}, not a logical type"
          | none => fail s!"C39: `{key}` (spec) is not in scope (wtS = none): {NaruSem.Quote.expr body}"
        else
          match NaruSem.wtR (ctxOfParams params) body with
          | some t =>
            ok s!"C39: `{key}` (runtime) is in scope: wtR = {tyTerm t}"
            quoted := quoted ++ [(key, NaruSem.Quote.expr body, ctx, tyTerm t, false)]
            -- C40: 基礎段階の境界(`basic`)は期待の一覧と一致する
            let isBasic := NaruSem.basic body
            if c40Decls.contains key then
              if isBasic then
                ok s!"C40: `{key}` is a basic expression (NaruSem.basic = true)"
                basics := basics ++ [(key, params, t)]
              else fail s!"C40: `{key}` is expected to be basic but NaruSem.basic = false: {NaruSem.Quote.expr body}"
            else if c41Decls.contains key then
              if !isBasic then ok s!"C40: `{key}` is outside the basic stage (match; NaruSem.basic = false) — C41"
              else fail s!"C40: `{key}` is expected to be outside the basic stage but NaruSem.basic = true"
            else fail s!"C40: `{key}` is a runtime declaration listed in neither c40Decls nor c41Decls"
          | none => fail s!"C39: `{key}` (runtime) is not in scope (wtR = none): {NaruSem.Quote.expr body}"
  for key in c40Decls ++ c41Decls do
    unless c39Decls.contains (key, false) do fail s!"C40: `{key}` is not a runtime declaration of c39Decls"
  let scopeFile := outDir / "Scope.lean"
  IO.FS.writeFile scopeFile (scopeProgram quoted)
  let r ← step s!"C39: lean {scopeFile} as module `Scope` (well-formedness of {quoted.length} quoted Core expressions by `decide`, identity with the compiler's Core)"
    "lean" #[s!"--root={outDir}", "-o", (outDir / "Scope.olean").toString, scopeFile.toString] (env := #[("LEAN_PATH", some leanPath)])
  let agree := s!"checkDecls: {quoted.length} quoted Core expression(s) agree"
  if r.exitCode == 0 && (contains r.stdout agree || contains r.stderr agree) then
    ok s!"C39 / C44: the {quoted.length} quoted Core expressions are the Core the compiler produces for {source}"
  else fail s!"C39 / C44: identity of the quoted Core: expected `{agree}` in the output of lean {scopeFile}\n{tail r.stdout 1500}"
  heading "C40 / C44 connection of the generated Model to the Core semantics"
  -- 実際の CLI で生成し、生成 Model をそのまま Lean のモジュールにする
  if ← genDir.pathExists then IO.FS.removeDirAll genDir
  let _ ← step "C44: generate the Model of the specimen with the real CLI" "lake" #["exe", "naru", "compile", "--out", genDir.toString, source]
  let modelFile := genDir / "Model" / "Sem" / "Core.lean"
  let modelText ← if ← modelFile.pathExists then IO.FS.readFile modelFile else pure ""
  if modelText.isEmpty then
    fail s!"C44: the generated Model {modelFile} is missing or empty"
    return
  ok s!"C44: the generated Model {modelFile} exists ({(modelText.splitOn "\n").length} lines)"
  let lp := s!"{genDir}:{outDir}:{leanPath}"
  let _ ← step "C44: compile the generated Model as the Lean module `Model.Sem.Core`" "lean"
    #[s!"--root={genDir}", "-o", (genDir / "Model" / "Sem" / "Core.olean").toString, modelFile.toString] (env := #[("LEAN_PATH", some lp)])
  let modelCheck := outDir / "ModelCheck.lean"
  IO.FS.writeFile modelCheck (modelProgram basics)
  let m ← step s!"C40 / C44: lean {modelCheck} (shape of the general theorem; connection `rfl` and preservation of {basics.length} generated declarations)"
    "lean" #[modelCheck.toString] (env := #[("LEAN_PATH", some lp)])
  let connAudited := auditedNames m.stdout
  let expectedConn := basics.flatMap fun (key, _, _) => [s!"conn_{shortName key}", s!"pres_{shortName key}"]
  let missingConn := expectedConn.filter fun n => !connAudited.contains n
  if m.exitCode == 0 && missingConn.isEmpty && !(contains m.stdout "forbidden") && !(contains m.stderr "forbidden") then
    ok s!"C44 / C45: the connection and preservation evidence of {basics.length} generated declarations ({expectedConn.length} theorems) is audited with 0 forbidden dependencies"
  else fail s!"C44 / C45: connection evidence: exit {m.exitCode}, not audited: {missingConn}\n{tail m.stdout 1500}\n{tail m.stderr 1500}"
  -- C46: 隔離した誤出力(実生成文字列から作る)は型検査を通るが接続検査に失敗する
  let logicName := Naru.Backend.Model.leanName "Sem.Core.logic"
  let shadowName := Naru.Backend.Model.leanName "Sem.Core.letShadow"
  match declText modelText logicName, declText modelText shadowName with
  | some logicText, some shadowText =>
    let wrongLogic := swapAndOr (logicText.replace logicName "Wrong.logic")
    let shadowBad := "let «y» : Nat := «x» * (2 : Nat)"
    let shadowGood := "let «x» : Nat := «x» * (2 : Nat)"
    let wrongShadow := (shadowText.replace shadowName "Wrong.letShadow").replace shadowGood shadowBad
    if contains logicText "&&" && contains logicText "||" && wrongLogic != logicText.replace logicName "Wrong.logic" then
      ok "C46: `Wrong.logic` is the generated text of `logic` with `&&` and `||` swapped"
    else fail s!"C46: could not derive `Wrong.logic` from the generated text:\n{logicText}"
    if contains shadowText shadowGood && contains wrongShadow shadowBad then
      ok "C46: `Wrong.letShadow` is the generated text of `letShadow` with the second binding renamed"
    else fail s!"C46: could not derive `Wrong.letShadow` from the generated text:\n{shadowText}"
    let wrongFile := outDir / "ModelWrong.lean"
    IO.FS.writeFile wrongFile (wrongProgram wrongLogic wrongShadow)
    let w ← step s!"C46: lean {wrongFile} must fail (the mistranslations type-check but do not connect)" "lean" #[wrongFile.toString]
      (expectExit := 1) (env := #[("LEAN_PATH", some lp)])
    let out := w.stdout ++ "\n" ++ w.stderr
    let errors := countOf out ": error:"
    let semantic := contains out "Wrong.logic" && contains out "Wrong.letShadow"
    let syntactic := contains out "unknown" || contains out "unexpected token" || contains out "import" || contains out "sorry"
    if w.exitCode != 0 && errors == 2 && semantic && !syntactic then
      ok "C46: exactly the 2 connection checks of the mistranslations fail (type mismatch against the Lean reading of the correct Core), the controls succeed, no syntax / import error"
    else fail s!"C46: expected exactly 2 semantic connection failures: exit {w.exitCode}, {errors} error(s)\n{tail out 2000}"
  | _, _ => fail s!"C46: the generated Model does not contain `{logicName}` / `{shadowName}`"
  heading "C45 the audit rejects forbidden dependencies"
  let negatives : List (String × String × String) :=
    [ ("sorry", "theorem bad : (1 : Nat) = 1 := sorry\n#audit_axioms bad\n", "sorryAx"),
      -- `native_decide` は Lean 4.34 では定理ごとの補助公理 `<名前>._native.native_decide.ax_*`(`Lean.ofReduceBool` を内包)に依存する
      ("native_decide", "theorem viaNative : (2 : Nat) + 2 = 4 := by native_decide\n#audit_axioms viaNative\n", "native_decide"),
      ("missing", "#audit_axioms NaruSem.thisTheoremDoesNotExist\n", "unknown") ]
  for (name, body, expectedText) in negatives do
    let f := outDir / s!"Audit_{name}.lean"
    IO.FS.writeFile f ("import NaruSem.Audit\n" ++ body)
    let r ← step s!"C45: {name}: lean {f} must fail" "lean" #[f.toString] (expectExit := 1) (env := #[("LEAN_PATH", some leanPath)])
    if r.exitCode != 0 && (contains r.stdout expectedText || contains r.stderr expectedText) then
      ok s!"C45: the audit rejects `{name}` (mentions `{expectedText}`)"
    else fail s!"C45: the audit did not reject `{name}` with `{expectedText}`: exit {r.exitCode}\n{tail r.stdout 800}\n{tail r.stderr 800}"
  IO.println s!"semantics: total {← elapsed t0}"

def run : IO UInt32 := runGroup "naru_test semantics" checks

end NaruTest.Semantics
