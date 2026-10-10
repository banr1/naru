import NaruTest.Common
import NaruSem.Quote
import NaruSem.Denote

/-!
# `naru_test semantics` — コンパイラ意味論保存の検査入口と、実際の Core・実生成宣言の検査(IDEAL.md C39 / C40 / C41 / C42 / C44 / C45 / C46)

1. C45 の検査入口 `lake build NaruSem`(意味論・一般定理・検体・公理監査を Lean kernel に検査させる)が exit 0。続けて
   `lake env lean semantics/NaruSem.lean` で公理監査の出力(`audit ok: <定数> depends on axioms […]`)を取り直し、必須の定理
   (`requiredTheorems`)がすべて監査されていて、許容しない依存が 0 件であることを確かめる。
2. C39: 検体 `tests/accept/sem_core.naru` を実際の compiler 経路(`Naru.compileFiles`)でコンパイルし、`c39Decls` の各宣言(今回の保存対象の
   構文を 1 つずつ使う)の Core を Lean の項として引用した検査プログラム `.lake/naru/test/semantics/Scope.lean` を書き、モジュール `Scope` として
   `lean` でコンパイルする: 各宣言の適格性(`wtR` / `wtS` = 期待の型。`decide` で kernel が計算する)と、引用した Core が compiler の Core と一致すること
   (`NaruSem.Quote.checkDecls` が同じソースを再びコンパイルして照合する)。
3. C40 / C41 / C44 / C46(Model): 同じ検体を実際の CLI(`lake exe naru compile --out`)で `.lake/naru/test/semantics/gen/` に生成し、
   生成 Model `Model/Sem/Core.lean` をそのまま Lean のモジュールにして、検査プログラム `ModelCheck.lean` が各 runtime 宣言(`c40Decls`: 基礎の
   構文だけの宣言、`c41Decls`: 非再帰の Nat / Bool の `match` を含む宣言)について、任意の引数で実生成宣言の値が Lean での読み `denoteN` / `denoteB`
   と等しいこと(`conn_<f>`: kernel の定義的等しさ。リテラルパターンの `match` は Lean が scrutinee の場合分け `dite (x = k)` / `Bool.casesOn` に
   展開するので、scrutinee の局所名を `cases` で場合分け(Nat はリテラルの最大値 + 1 の深さ、Bool は 1 回)してから `rfl`。`proofOf`)と、そこから
   独立意味論の結果が実生成宣言の値であること(`pres_<f>`: `check_sound_nat` / `check_sound_bool`)を kernel に検査させ、公理監査に載せる。
   一般定理の量化の形(任意の文脈・式・型・環境、腕の列)も同じプログラムで照合する。
   負の検体 `ModelWrong.lean`(隔離: 実生成文字列から `&&` / `||` を取り違えた `Wrong.logic`、束縛を取り違えた `Wrong.letShadow`、Bool の腕を
   入れ替えた `Wrong.matchBool`、ガードを否定した `Wrong.matchNat`、腕の束縛が後続の腕に漏れた形の `Wrong.matchShadow` を作る)は
   Lean の型検査を通るが、同じ正しい入力 Core への接続検査だけが失敗する(正しい出力の対照は同じファイルで成功する。誤りは接続の定理の行にだけ出る)。
4. C42 / C44 / C46(Statements): 同じ生成先の生成 Statements `Statements/Sem/Core.lean` をそのまま Lean のモジュールにして、検査プログラム
   `StatementsCheck.lean` が各基礎段階の spec 宣言(`c42Decls`: 量化・命題の `let`・`match` を含まない宣言。`c43Decls` はその外で、接続は次の段階)について、
   任意の引数で実生成宣言の命題が Lean での読み `denoteP` と等しいこと(`conn_<f>`: `Prop` の等式、kernel の定義的等しさ `rfl`)と、そこから実生成宣言の命題が
   独立意味論の意味そのものであること(`pres_<f>`: `Sem (SEnv.ofList …) core_<f> (Statements.Sem.Core.<f> args)`。`check_sound_prop`)を kernel に検査させ、
   公理監査に載せる。一般定理 `Sem_denote`(両方向の同値)と値 / 命題の境界 `denoteP_iff_denoteB` の量化の形も同じプログラムで照合する。
   負の検体 `StatementsWrong.lean`(`∧` / `∨` の取り違え、含意の向きの反転、Bool の値を `= false` に写した境界の誤り、`if` の分岐の入れ替え)は型検査を通るが
   接続検査だけが失敗する。
5. C45: 監査が禁止依存を失敗にすることを、`sorry` / `native_decide` / 存在しない定数の 3 つの負の検体で確かめる(`lean` が exit 非 0)。
-/

namespace NaruTest.Semantics
open NaruTest

def source : String := "tests/accept/sem_core.naru"
def outDir : System.FilePath := ".lake" / "naru" / "test" / "semantics"
def genDir : System.FilePath := outDir / "gen"
def rootFile : String := "semantics/NaruSem.lean"

/-- 公理監査に現れなければならない定理(C39: 全域性・一意性。C40 / C41 / C44: 保存と接続検査の健全性、腕の列・腕の補題、異なる表現の対応関係。
C42 / C44: Statements の基礎段階の同値定理、値 / 命題の境界、接続検査の健全性、値の等値と命題の同値の区別)。 -/
def requiredTheorems : List String :=
  [ "NaruSem.eval_total", "NaruSem.Eval_unique", "NaruSem.Sem_exists", "NaruSem.Sem_unique",
    "NaruSem.denote_sound", "NaruSem.preserve_nat", "NaruSem.preserve_bool", "NaruSem.check_sound_nat", "NaruSem.check_sound_bool",
    "NaruSem.CmpOp.leanBool_eq", "NaruSem.EqOp.leanNat_eq", "NaruSem.EqOp.leanBool_eq",
    "NaruSem.denoteArms_sound", "NaruSem.denoteArm_sound", "NaruSem.denoteArmsV_hit", "NaruSem.denoteArmsV_miss",
    "NaruSem.denoteArmsV_guard_true", "NaruSem.denoteArmsV_guard_false",
    "NaruSem.Sem_denote", "NaruSem.Sem_denoteP", "NaruSem.check_sound_prop", "NaruSem.denoteP_iff_denoteB", "NaruSem.basic_not_proppy",
    "NaruSem.EqOp.propIff_bool", "NaruSem.CmpOp.leanBoolProp_iff", "NaruSem.LogicOp.prop_iff" ]

/-- 検体の宣言(修飾名, spec か)。今回の保存対象の各構文を 1 つずつ。欠けていれば FAIL。 -/
def c39Decls : List (String × Bool) :=
  [ ("Sem.Core.litNat", false), ("Sem.Core.litBool", false), ("Sem.Core.useVar", false), ("Sem.Core.useLet", false),
    ("Sem.Core.letShadow", false), ("Sem.Core.useIf", false), ("Sem.Core.arith", false), ("Sem.Core.minMax", false),
    ("Sem.Core.cmpNat", false), ("Sem.Core.cmpBool", false), ("Sem.Core.eqNat", false), ("Sem.Core.eqBool", false),
    ("Sem.Core.logic", false), ("Sem.Core.matchNat", false), ("Sem.Core.matchBool", false), ("Sem.Core.matchShadow", false),
    ("Sem.Core.matchLetShadow", false), ("Sem.Core.matchScrut", false), ("Sem.Core.matchLits", false), ("Sem.Core.matchBoolGuard", false),
    ("Sem.Core.specLit", true), ("Sem.Core.specVar", true), ("Sem.Core.specCmp", true), ("Sem.Core.specCmpBool", true),
    ("Sem.Core.specLogic", true), ("Sem.Core.specEq", true), ("Sem.Core.specArith", true), ("Sem.Core.specLetVal", true),
    ("Sem.Core.specLetProp", true), ("Sem.Core.specLetShadow", true), ("Sem.Core.specIfBool", true), ("Sem.Core.specIfProp", true),
    ("Sem.Core.specForall", true), ("Sem.Core.specExists", true), ("Sem.Core.specMatch", true), ("Sem.Core.specMatchProp", true) ]

/-- C40 の基礎段階の runtime 宣言(リテラル・局所名・let・if・算術・min / max・比較・等値・論理)。`NaruSem.basic` が真でなければならない。 -/
def c40Decls : List String :=
  [ "Sem.Core.litNat", "Sem.Core.litBool", "Sem.Core.useVar", "Sem.Core.useLet", "Sem.Core.letShadow", "Sem.Core.useIf",
    "Sem.Core.arith", "Sem.Core.minMax", "Sem.Core.cmpNat", "Sem.Core.cmpBool", "Sem.Core.eqNat", "Sem.Core.eqBool", "Sem.Core.logic" ]

/-- C41 の非再帰の Nat / Bool の `match` の runtime 宣言(同名の仮引数・外側の let・scrutinee の中の名前の束縛、複数のガード不成立からの継続、
Bool のリテラルの腕と Bool の scrutinee のガード、Nat のリテラル 0 / 1 の腕)。`NaruSem.basic` が偽(段階の境界)で、接続と保存を検査する。 -/
def c41Decls : List String :=
  [ "Sem.Core.matchNat", "Sem.Core.matchBool", "Sem.Core.matchShadow", "Sem.Core.matchLetShadow", "Sem.Core.matchScrut",
    "Sem.Core.matchLits", "Sem.Core.matchBoolGuard" ]

/-- C42 の基礎段階の spec 宣言(Bool の値の命題への境界、論理、Nat / Bool の比較・等値、値の `let`、Bool の条件の `if`)。`NaruSem.basic` が真で
なければならず、実生成 Statements への接続と保存を検査する。 -/
def c42Decls : List String :=
  [ "Sem.Core.specLit", "Sem.Core.specVar", "Sem.Core.specCmp", "Sem.Core.specCmpBool", "Sem.Core.specLogic", "Sem.Core.specEq",
    "Sem.Core.specArith", "Sem.Core.specLetVal", "Sem.Core.specIfBool" ]

/-- C43 の spec 宣言(量化・命題の `let` と shadowing・命題の条件の `if`・ガード付き `match`)。`NaruSem.basic` が偽(段階の境界)で、接続は次の段階。 -/
def c43Decls : List String :=
  [ "Sem.Core.specLetProp", "Sem.Core.specLetShadow", "Sem.Core.specIfProp", "Sem.Core.specForall", "Sem.Core.specExists",
    "Sem.Core.specMatch", "Sem.Core.specMatchProp" ]

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

/-- `lean` の出力の `<file>:<line>:<col>: error:` の行の行番号。 -/
def errorLines (out : String) : List Nat :=
  ((out.splitOn "\n").filter fun l => contains l ": error:").filterMap fun l =>
    ((l.splitOn ":").getD 1 "").trimAscii.toString.toNat?

/-- 検査プログラム `Scope.lean`(モジュール `Scope`): 引用した Core(`core_<f>`)と文脈(`ctx_<f>`)、適格性の定理(`decide`)、引用の一致の照合(`run_cmd`)。 -/
def scopeProgram (quoted : List (String × String × String × String × Bool)) : String :=
  let defs := quoted.map fun (key, core, ctx, ty, spec) =>
    let n := shortName key
    let wt := if spec then
      s!"theorem wt_{n} : NaruSem.wtS ctx_{n} core_{n} = some {ty} := by decide\n" ++
      s!"theorem form_{n} : NaruSem.STy.isForm {ty} = true := by decide\n"
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

/-! ### 接続の証明(C41 / C44)

生成形(`Backend.Model.emitMatchGuarded`)の `match` は、リテラルパターンの腕を Lean が scrutinee の場合分け(`dite (x = k)` / `Bool.casesOn`)
に展開するので、自由変数のままでは読み(`matchPat` の `if`)と定義的に等しくない。scrutinee に現れる局所名を、パターンの Nat リテラルの最大値 + 1 の
深さ(Bool は 1 回)だけ `cases` で場合分けすると、両辺が同じ形(ガード付きの腕の `match (if g then some b else none) with …`、残りの腕の読み)に
簡約して `rfl` で閉じる。`match` の無い宣言(と変数・`_` のパターンだけの `match`)は `rfl` の項。 -/

/-- 式の中の局所名(`.var`)。 -/
partial def varsOf : Naru.Core.Expr → List String
  | .var x => [x]
  | .let_ _ _ v b => varsOf v ++ varsOf b
  | .ite c t e => varsOf c ++ varsOf t ++ varsOf e
  | .binop _ l r _ => varsOf l ++ varsOf r
  | .unop _ a => varsOf a
  | .method _ _ r as _ => varsOf r ++ as.flatMap varsOf
  | .match_ s _ arms => varsOf s ++ arms.flatMap fun | .mk _ g b => (g.map varsOf).getD [] ++ varsOf b
  | _ => []

/-- 腕のパターンのリテラルから場合分けの深さ: Nat リテラルの最大値 + 1、Bool のリテラルは 1、リテラルが無ければ 0。 -/
def litDepth (arms : List Naru.Core.Arm) : Nat :=
  arms.foldl (init := 0) fun d arm => match arm with
    | .mk (.lit (.nat n)) _ _ => max d (n + 1)
    | .mk (.lit (.bool _)) _ _ => max d 1
    | _ => d

/-- `match` の scrutinee に現れる局所名と、そのパターンのリテラルから要る場合分けの深さ。 -/
partial def casesOf : Naru.Core.Expr → List (String × Nat)
  | .match_ s _ arms =>
    let d := litDepth arms
    (if d == 0 then [] else (varsOf s).map (·, d)) ++ casesOf s ++
      arms.flatMap fun | .mk _ g b => (g.map casesOf).getD [] ++ casesOf b
  | .let_ _ _ v b => casesOf v ++ casesOf b
  | .ite c t e => casesOf c ++ casesOf t ++ casesOf e
  | .binop _ l r _ => casesOf l ++ casesOf r
  | .unop _ a => casesOf a
  | .method _ _ r as _ => casesOf r ++ as.flatMap casesOf
  | _ => []

def depthOf (cs : List (String × Nat)) (x : String) : Nat :=
  cs.foldl (fun d (y, k) => if y == x then max d k else d) 0

/-- Nat の局所名の `depth` 段の場合分け(`cases x with | zero => tail | succ x => …`)。 -/
def natCases (x : String) (tail : String) : Nat → String
  | 0 => tail
  | d + 1 => s!"(cases «{x}» with | zero => {tail} | succ «{x}» => {natCases x tail d})"

/-- 場合分けの列(局所名, Nat か, 深さ)を tactic の文字列に。 -/
def casesScript : List (String × Bool × Nat) → String → String
  | [], tail => tail
  | (x, true, d) :: rest, tail => natCases x (casesScript rest tail) d
  | (x, false, _) :: rest, tail => s!"(cases «{x}» with | false => {casesScript rest tail} | true => {casesScript rest tail})"

/-- 接続の証明(仮引数と Core の本文から): 場合分けが要れば `by intro …; cases …` の tactic、要らなければ `rfl` の項。 -/
def proofOf (params : List Naru.Core.Param) (body : Naru.Core.Expr) : String :=
  let bs := params.filterMap binderOf
  let args := " ".intercalate (bs.map (·.2.2))
  let cs := casesOf body
  let targets := params.filterMap fun p =>
    let d := depthOf cs p.name
    if d == 0 then none
    else match p.ty with
      | .nat => some (p.name, true, d)
      | .bool => some (p.name, false, 1)
      | _ => none
  if targets.isEmpty then (if bs.isEmpty then "rfl" else s!"fun {args} => rfl")
  else s!"by intro {args}; {casesScript targets "rfl"}"

/-- 接続の定理 1 つ分(1 行): `<thm> : ∀ args, <call> = <読み> (Env.ofList …) <core> := <proof>`。 -/
def connStmt (thm lean : String) (params : List Naru.Core.Param) (t : NaruSem.Ty) (coreName proof : String) : String :=
  let bs := params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let den := match t with | .nat => "NaruSem.denoteN" | .bool => "NaruSem.denoteB"
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  s!"theorem {thm} : {quant s!"{call} = {den} (NaruSem.Env.ofList {env}) {coreName}"} := {proof}"

/-- 1 つの runtime 宣言の接続と保存: `conn_<f>`(実生成宣言 = 読み)と `pres_<f>`(独立意味論の結果 = 実生成宣言の値)。 -/
def connOf (key : String) (params : List Naru.Core.Param) (t : NaruSem.Ty) (body : Naru.Core.Expr) : String :=
  let n := shortName key
  let lean := Naru.Backend.Model.leanName key
  let bs := params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let (val, sound) := match t with
    | .nat => ("NaruSem.Val.nat", "NaruSem.check_sound_nat")
    | .bool => ("NaruSem.Val.bool", "NaruSem.check_sound_bool")
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let lam (body : String) : String := if bs.isEmpty then body else s!"fun {args} => {body}"
  let conn := if bs.isEmpty then s!"conn_{n}" else s!"conn_{n} {args}"
  s!"-- {key}: the generated declaration `{lean}` is definitionally the Lean reading of its Core; hence its value is the meaning of the Core\n" ++
  connStmt s!"conn_{n}" lean params t s!"core_{n}" (proofOf params body) ++ "\n" ++
  s!"theorem pres_{n} : {quant s!"NaruSem.eval (NaruSem.Env.ofList {env}) core_{n} = some ({val} ({call}))"} :=\n" ++
  s!"  {lam s!"{sound} {env} wt_{n} ({conn})"}\n\n"

/-- 検査プログラム `ModelCheck.lean`: 実生成 Model を import し、一般定理の量化の形と、各 runtime 宣言の接続・保存を kernel に検査させて監査する。 -/
def modelProgram (decls : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr)) : String :=
  let names := decls.flatMap fun (key, _, _, _) => [s!"conn_{shortName key}", s!"pres_{shortName key}"]
  s!"-- naru_test semantics (C40 / C41 / C44): generated from NaruTest/Semantics.lean. Connection of the generated Model of {source} to the Core semantics.\n" ++
  "import Scope\nimport Model.Sem.Core\n\n" ++
  "-- the general theorem quantifies over any context, expression, type and matching environment (C40 / C41)\n" ++
  "example : ∀ (Γ : NaruSem.Ctx) (e : Naru.Core.Expr) (t : NaruSem.Ty) (ρ : NaruSem.Env),\n" ++
  "    NaruSem.wtR Γ e = some t → Γ = ρ.ty → NaruSem.eval ρ e = some (NaruSem.denoteV ρ t e) :=\n" ++
  "  fun _ _ _ _ h hρ => NaruSem.denote_sound h _ hρ\n" ++
  "-- the arms theorem quantifies over any well-formed exhaustive arms, environment and scrutinee value (C41)\n" ++
  "example : ∀ (Γ : NaruSem.Ctx) (ts t : NaruSem.Ty) (arms : List Naru.Core.Arm) (ρ : NaruSem.Env) (v : NaruSem.Val),\n" ++
  "    NaruSem.wtArmsR Γ ts arms = some t → NaruSem.exhaustive ts arms = true → Γ = ρ.ty → v.ty = ts →\n" ++
  "    NaruSem.evalArms ρ v arms = some (NaruSem.denoteArmsV ρ t v arms) :=\n" ++
  "  fun _ _ _ _ _ _ h hex hρ hv => NaruSem.denoteArms_sound h hex _ hρ _ hv\n\n" ++
  "".intercalate (decls.map fun (key, params, t, body) => connOf key params t body) ++
  s!"#audit_axioms {" ".intercalate names}\n"

/-! ### Statements の接続(C42 / C44)

生成 Statements の spec 宣言は `Prop` の定数 / 関数なので、接続は `Prop` の等式 `Statements.Sem.Core.f args = denoteP (SEnv.ofList …) core_f`
(kernel の定義的等しさ)。基礎段階の宣言(`c42Decls`)に `match` は無いので証明は `rfl` の項。 -/

/-- 仮引数 → (Lean の束縛, spec の環境の項目(値), 実引数)。 -/
def specBinderOf (p : Naru.Core.Param) : Option (String × String × String) :=
  match p.ty with
  | .nat => some (s!"(«{p.name}» : Nat)", s!"({p.name.quote}, NaruSem.SVal.val (NaruSem.Val.nat «{p.name}»))", s!"«{p.name}»")
  | .bool => some (s!"(«{p.name}» : Bool)", s!"({p.name.quote}, NaruSem.SVal.val (NaruSem.Val.bool «{p.name}»))", s!"«{p.name}»")
  | _ => none

/-- 接続の定理 1 つ分(1 行、Statements): `<thm> : ∀ args, <call> = denoteP (SEnv.ofList …) <core> := rfl`。 -/
def specConnStmt (thm lean : String) (params : List Naru.Core.Param) (coreName : String) : String :=
  let bs := params.filterMap specBinderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let proof := if bs.isEmpty then "rfl" else s!"fun {args} => rfl"
  s!"theorem {thm} : {quant s!"{call} = NaruSem.denoteP (NaruSem.SEnv.ofList {env}) {coreName}"} := {proof}"

/-- 1 つの spec 宣言の接続と保存: `conn_<f>`(実生成宣言の命題 = 読み)、`basic_<f>`(基礎段階の範囲)、`pres_<f>`(実生成宣言の命題は独立意味論の意味)。 -/
def specConnOf (key : String) (params : List Naru.Core.Param) : String :=
  let n := shortName key
  let lean := Naru.Backend.Statements.stmtName key
  let bs := params.filterMap specBinderOf
  let vals := params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let valsEnv := "[" ++ ", ".intercalate (vals.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let lam (body : String) : String := if bs.isEmpty then body else s!"fun {args} => {body}"
  let conn := if bs.isEmpty then s!"conn_{n}" else s!"conn_{n} {args}"
  s!"-- {key}: the generated declaration `{lean}` is definitionally the Lean reading of its Core; hence it is the meaning of the Core\n" ++
  specConnStmt s!"conn_{n}" lean params s!"core_{n}" ++ "\n" ++
  s!"theorem basic_{n} : NaruSem.basic core_{n} = true := by decide\n" ++
  s!"theorem pres_{n} : {quant s!"NaruSem.Sem (NaruSem.SEnv.ofList {env}) core_{n} ({call})"} :=\n" ++
  s!"  {lam s!"NaruSem.check_sound_prop {valsEnv} wt_{n} form_{n} basic_{n} ({conn})"}\n\n"

/-- 検査プログラム `StatementsCheck.lean`: 実生成 Statements を import し、一般定理の量化の形と、各基礎段階の spec 宣言の接続・保存を kernel に検査させて監査する。 -/
def statementsProgram (decls : List (String × List Naru.Core.Param)) : String :=
  let names := decls.flatMap fun (key, _) => [s!"conn_{shortName key}", s!"basic_{shortName key}", s!"pres_{shortName key}"]
  s!"-- naru_test semantics (C42 / C44): generated from NaruTest/Semantics.lean. Connection of the generated Statements of {source} to the Core semantics.\n" ++
  "import Scope\nimport Statements.Sem.Core\n\n" ++
  "-- the general theorem quantifies over any context, basic expression, matching environment and meaning, and is an equivalence (C42)\n" ++
  "example : ∀ (Γ : NaruSem.SCtx) (e : Naru.Core.Expr) (τ : NaruSem.STy) (ρ : NaruSem.SEnv) (P : Prop),\n" ++
  "    NaruSem.wtS Γ e = some τ → NaruSem.basic e = true → Γ.NoProp → Γ = ρ.ctx → NaruSem.Sem ρ e P → (P ↔ NaruSem.denoteP ρ e) :=\n" ++
  "  fun _ _ _ _ _ hw hb hΓ hρ h => NaruSem.Sem_denote hw hb hΓ _ hρ h\n" ++
  "-- the value / proposition boundary quantifies over any basic expression and environment without proposition bindings (C42)\n" ++
  "example : ∀ (e : Naru.Core.Expr) (ρ : NaruSem.SEnv), NaruSem.basic e = true → ρ.ctx.NoProp →\n" ++
  "    (NaruSem.denoteP ρ e ↔ NaruSem.denoteB ρ.vals e = true) :=\n" ++
  "  fun e ρ hb hΓ => NaruSem.denoteP_iff_denoteB e hb ρ hΓ\n\n" ++
  "".intercalate (decls.map fun (key, params) => specConnOf key params) ++
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

/-- 2 つの部分文字列を取り違える。 -/
def swapText (a b : String) (s : String) : String :=
  ((s.replace a "\x01").replace b a).replace "\x01" b

/-- `&&` と `||` を取り違える。 -/
def swapAndOr : String → String := swapText "&&" "||"

/-- 負の検体の作り方: (検体の宣言, `Wrong.<名前>`, 実生成文字列に要る部分 `good`, 誤出力に現れる部分 `bad`, 変換, 説明)。 -/
structure Mistranslation where
  key : String
  wrong : String
  good : String
  bad : String
  transform : String → String
  note : String

def mistranslations : List Mistranslation :=
  [ { key := "Sem.Core.logic", wrong := "Wrong.logic", good := "&&", bad := "||", transform := swapAndOr,
      note := "`&&` and `||` swapped in the generated text of `logic`" },
    { key := "Sem.Core.letShadow", wrong := "Wrong.letShadow", good := "let «x» : Nat := «x» * (2 : Nat)", bad := "let «y» : Nat := «x» * (2 : Nat)",
      transform := fun s => s.replace "let «x» : Nat := «x» * (2 : Nat)" "let «y» : Nat := «x» * (2 : Nat)",
      note := "the second binding renamed in the generated text of `letShadow` (the result refers to the wrong binding)" },
    { key := "Sem.Core.matchBool", wrong := "Wrong.matchBool", good := "| true =>", bad := "| false =>", transform := swapText "| true =>" "| false =>",
      note := "the `true` and `false` arms swapped in the generated text of `matchBool` (arm order / selection)" },
    { key := "Sem.Core.matchNat", wrong := "Wrong.matchNat", good := "if Decidable.decide («n» < (10 : Nat)) then", bad := "if !Decidable.decide («n» < (10 : Nat)) then",
      transform := fun s => s.replace "if Decidable.decide («n» < (10 : Nat)) then" "if !Decidable.decide («n» < (10 : Nat)) then",
      note := "the guard negated in the generated text of `matchNat` (guard success / failure swapped)" },
    { key := "Sem.Core.matchShadow", wrong := "Wrong.matchShadow", good := "«n» == «x»", bad := "«x» == «x»",
      transform := fun s => s.replace "«n» == «x»" "«x» == «x»",
      note := "the arm binding leaked into the following arm in the generated text of `matchShadow` (`n == x` reads the pattern's `n` = `x` instead of the parameter)" } ]

/-- 負の検体(Statements、C46): 実生成文字列から作る誤翻訳。論理の取り違え、含意の向き、Bool の値の命題への境界、`if` の分岐。 -/
def specMistranslations : List Mistranslation :=
  [ { key := "Sem.Core.specLogic", wrong := "Wrong.specLogic", good := "∧", bad := "∨", transform := swapText "∧" "∨",
      note := "`∧` and `∨` swapped in the generated text of `specLogic`" },
    { key := "Sem.Core.specCmp", wrong := "Wrong.specCmp", good := "(«x» < «y») → («x» ≤ «y»)", bad := "(«x» ≤ «y») → («x» < «y»)",
      transform := fun s => s.replace "(«x» < «y») → («x» ≤ «y»)" "(«x» ≤ «y») → («x» < «y»)",
      note := "the implication reversed in the generated text of `specCmp` (a one-directional error the equivalence must reject)" },
    { key := "Sem.Core.specVar", wrong := "Wrong.specVar", good := "«a» = true", bad := "«a» = false",
      transform := fun s => s.replace "«a» = true" "«a» = false",
      note := "the Bool value mapped to the wrong proposition (`= false`) in the generated text of `specVar` (value / proposition boundary)" },
    { key := "Sem.Core.specIfBool", wrong := "Wrong.specIfBool", good := "«x» > (0 : Nat)", bad := "«x» = (0 : Nat)",
      transform := swapText "«x» > (0 : Nat)" "«x» = (0 : Nat)",
      note := "the `then` and `else` branches swapped in the generated text of `specIfBool`" } ]

/-- 負の検体のプログラムと、接続検査が失敗しなければならない行(1 始まり)。誤出力(型検査は通る)の宣言の後に、正しい出力の対照 `conn_<f>_ok` と
誤出力への接続 `conn_wrong_<f>` を置く(`connOf 定理名 Lean 名 検体の宣言名` が接続の定理 1 行を返す。宣言が無ければ `none`)。 -/
def wrongProgramWith (what importMod : String) (wrongs : List (Mistranslation × String))
    (connOf : String → String → String → Option String) : String × List Nat := Id.run do
  let mut lines : List String :=
    [ s!"-- naru_test semantics (C46): generated from NaruTest/Semantics.lean. Isolated mistranslations of the generated {what} (they type-check) must fail the connection check.",
      "import Scope", s!"import {importMod}", "" ]
  for (m, text) in wrongs do
    lines := lines ++ [s!"-- {m.note}"] ++ text.splitOn "\n" ++ [""]
  lines := lines ++ ["-- controls: the correct generated declarations connect"]
  for (m, _) in wrongs do
    if let some stmt := connOf s!"conn_{shortName m.key}_ok" "" m.key then lines := lines ++ [stmt]
  lines := lines ++ ["", "-- the mistranslations must not connect to the same (correct) input Core"]
  let mut failing : List Nat := []
  for (m, _) in wrongs do
    if let some stmt := connOf s!"conn_wrong_{shortName m.key}" m.wrong m.key then
      lines := lines ++ [stmt]
      failing := failing ++ [lines.length]
  return ("\n".intercalate lines ++ "\n", failing)

/-- 負の検体 `ModelWrong.lean`(Model)。Lean 名が空なら正しい実生成宣言(対照)。 -/
def wrongProgram (decls : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr))
    (wrongs : List (Mistranslation × String)) : String × List Nat :=
  wrongProgramWith "Model" "Model.Sem.Core" wrongs fun thm lean key =>
    (decls.find? fun (k, _, _, _) => k == key).map fun (key, params, t, body) =>
      let name := if lean.isEmpty then Naru.Backend.Model.leanName key else lean
      connStmt thm name params t s!"core_{shortName key}" (proofOf params body)

/-- 負の検体 `StatementsWrong.lean`(Statements)。 -/
def specWrongProgram (decls : List (String × List Naru.Core.Param)) (wrongs : List (Mistranslation × String)) : String × List Nat :=
  wrongProgramWith "Statements" "Statements.Sem.Core" wrongs fun thm lean key =>
    (decls.find? fun (k, _) => k == key).map fun (key, params) =>
      let name := if lean.isEmpty then Naru.Backend.Statements.stmtName key else lean
      specConnStmt thm name params s!"core_{shortName key}"

/-- 実生成文字列から負の検体を作る(型検査は通るが接続は失敗する誤出力)。`good` が元の文字列にあり、変換後に `bad` が現れ、変換が実際に変えたことを確かめる。 -/
def deriveWrongs (what : String) (text : String) (leanNameOf : String → String) (mts : List Mistranslation) : M (List (Mistranslation × String)) := do
  let mut wrongs : List (Mistranslation × String) := []
  for mt in mts do
    let leanName := leanNameOf mt.key
    match declText text leanName with
    | some decl =>
      let renamed := decl.replace leanName mt.wrong
      let wrong := mt.transform renamed
      if contains decl mt.good && contains wrong mt.bad && wrong != renamed then
        ok s!"C46: `{mt.wrong}` is the generated text of `{leanName}` with {mt.note}"
        wrongs := wrongs ++ [(mt, wrong)]
      else fail s!"C46: could not derive `{mt.wrong}` from the generated text:\n{decl}"
    | none => fail s!"C46: the generated {what} does not contain `{leanName}`"
  return wrongs

/-- 負の検体のプログラムを `lean` に掛け、ちょうど `conn_wrong_*` の行だけで失敗することを確かめる(構文 / import の誤りではなく、意味の対応の不成立)。 -/
def checkWrong (what : String) (file : System.FilePath) (program : String × List Nat) (wrongs : List (Mistranslation × String)) (lp : String) : M Unit := do
  let (wrongText, failing) := program
  IO.FS.writeFile file wrongText
  let w ← step s!"C46: lean {file} must fail (the {wrongs.length} mistranslations of the generated {what} type-check but do not connect)" "lean" #[file.toString]
    (expectExit := 1) (env := #[("LEAN_PATH", some lp)])
  let out := w.stdout ++ "\n" ++ w.stderr
  let errs := errorLines out
  let onlyWrong := errs.all failing.contains
  let allWrong := failing.all errs.contains
  let named := wrongs.all fun (mt, _) => contains out mt.wrong
  let syntactic := contains out "unknown" || contains out "unexpected token" || contains out "import" || contains out "sorry"
  if w.exitCode != 0 && failing.length == wrongs.length && onlyWrong && allWrong && named && !syntactic then
    ok s!"C46: exactly the {wrongs.length} connection checks of the mistranslations of the {what} fail (lines {failing}: the reading of the correct Core is not reached), the controls succeed, no syntax / import error"
  else fail s!"C46: expected the connection failures exactly on lines {failing}: exit {w.exitCode}, error lines {errs}\n{tail out 2500}"

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
  let mut connected : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr) := []
  let mut specConnected : List (String × List Naru.Core.Param) := []
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
              -- C42 / C43: 段階の境界(`basic`)は期待の一覧と一致し、基礎段階の宣言は接続・保存を検査する
              let isBasic := NaruSem.basic body
              if c42Decls.contains key then
                if isBasic then
                  ok s!"C42: `{key}` is a basic spec expression (NaruSem.basic = true)"
                  specConnected := specConnected ++ [(key, params)]
                else fail s!"C42: `{key}` is expected to be basic but NaruSem.basic = false: {NaruSem.Quote.expr body}"
              else if c43Decls.contains key then
                if !isBasic then
                  ok s!"C43: `{key}` is outside the basic stage (quantifier / Prop let / match; NaruSem.basic = false); its connection is the next stage"
                else fail s!"C43: `{key}` is expected to contain a quantifier / Prop let / match but NaruSem.basic = true"
              else fail s!"C42 / C43: `{key}` is a spec declaration listed in neither c42Decls nor c43Decls"
            else fail s!"C39: `{key}` (spec) has the value type {styTerm τ}, not a logical type"
          | none => fail s!"C39: `{key}` (spec) is not in scope (wtS = none): {NaruSem.Quote.expr body}"
        else
          match NaruSem.wtR (ctxOfParams params) body with
          | some t =>
            ok s!"C39: `{key}` (runtime) is in scope: wtR = {tyTerm t}"
            quoted := quoted ++ [(key, NaruSem.Quote.expr body, ctx, tyTerm t, false)]
            -- C40 / C41: 段階の境界(`basic`)は期待の一覧と一致し、どちらの段階の宣言も接続・保存を検査する
            let isBasic := NaruSem.basic body
            if c40Decls.contains key then
              if isBasic then
                ok s!"C40: `{key}` is a basic expression (NaruSem.basic = true)"
                connected := connected ++ [(key, params, t, body)]
              else fail s!"C40: `{key}` is expected to be basic but NaruSem.basic = false: {NaruSem.Quote.expr body}"
            else if c41Decls.contains key then
              if !isBasic then
                ok s!"C41: `{key}` is outside the basic stage (match; NaruSem.basic = false); connection proof: `{proofOf params body}`"
                connected := connected ++ [(key, params, t, body)]
              else fail s!"C41: `{key}` is expected to contain a match but NaruSem.basic = true"
            else fail s!"C40 / C41: `{key}` is a runtime declaration listed in neither c40Decls nor c41Decls"
          | none => fail s!"C39: `{key}` (runtime) is not in scope (wtR = none): {NaruSem.Quote.expr body}"
  for key in c40Decls ++ c41Decls do
    unless c39Decls.contains (key, false) do fail s!"C40 / C41: `{key}` is not a runtime declaration of c39Decls"
  for key in c42Decls ++ c43Decls do
    unless c39Decls.contains (key, true) do fail s!"C42 / C43: `{key}` is not a spec declaration of c39Decls"
  let scopeFile := outDir / "Scope.lean"
  IO.FS.writeFile scopeFile (scopeProgram quoted)
  let r ← step s!"C39: lean {scopeFile} as module `Scope` (well-formedness of {quoted.length} quoted Core expressions by `decide`, identity with the compiler's Core)"
    "lean" #[s!"--root={outDir}", "-o", (outDir / "Scope.olean").toString, scopeFile.toString] (env := #[("LEAN_PATH", some leanPath)])
  let agree := s!"checkDecls: {quoted.length} quoted Core expression(s) agree"
  if r.exitCode == 0 && (contains r.stdout agree || contains r.stderr agree) then
    ok s!"C39 / C44: the {quoted.length} quoted Core expressions are the Core the compiler produces for {source}"
  else fail s!"C39 / C44: identity of the quoted Core: expected `{agree}` in the output of lean {scopeFile}\n{tail r.stdout 1500}"
  heading "C40 / C41 / C44 connection of the generated Model to the Core semantics"
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
  IO.FS.writeFile modelCheck (modelProgram connected)
  let m ← step s!"C40 / C41 / C44: lean {modelCheck} (shape of the general theorems; connection and preservation of {connected.length} generated declarations)"
    "lean" #[modelCheck.toString] (env := #[("LEAN_PATH", some lp)])
  let connAudited := auditedNames m.stdout
  let expectedConn := connected.flatMap fun (key, _, _, _) => [s!"conn_{shortName key}", s!"pres_{shortName key}"]
  let missingConn := expectedConn.filter fun n => !connAudited.contains n
  if m.exitCode == 0 && missingConn.isEmpty && !(contains m.stdout "forbidden") && !(contains m.stderr "forbidden") then
    ok s!"C44 / C45: the connection and preservation evidence of {connected.length} generated declarations ({expectedConn.length} theorems; {c41Decls.length} with a match) is audited with 0 forbidden dependencies"
  else fail s!"C44 / C45: connection evidence: exit {m.exitCode}, not audited: {missingConn}\n{tail m.stdout 1500}\n{tail m.stderr 1500}"
  -- C46: 隔離した誤出力(実生成文字列から作る)は型検査を通るが接続検査に失敗する
  let wrongs ← deriveWrongs "Model" modelText Naru.Backend.Model.leanName mistranslations
  checkWrong "Model" (outDir / "ModelWrong.lean") (wrongProgram connected wrongs) wrongs lp
  heading "C42 / C44 connection of the generated Statements to the Core semantics"
  let stmtFile := genDir / "Statements" / "Sem" / "Core.lean"
  let stmtText ← if ← stmtFile.pathExists then IO.FS.readFile stmtFile else pure ""
  if stmtText.isEmpty then
    fail s!"C44: the generated Statements {stmtFile} is missing or empty"
    return
  ok s!"C44: the generated Statements {stmtFile} exists ({(stmtText.splitOn "\n").length} lines)"
  let _ ← step "C44: compile the generated Statements as the Lean module `Statements.Sem.Core`" "lean"
    #[s!"--root={genDir}", "-o", (genDir / "Statements" / "Sem" / "Core.olean").toString, stmtFile.toString] (env := #[("LEAN_PATH", some lp)])
  let stmtCheck := outDir / "StatementsCheck.lean"
  IO.FS.writeFile stmtCheck (statementsProgram specConnected)
  let s ← step s!"C42 / C44: lean {stmtCheck} (shape of the general equivalence theorem and the value / proposition boundary; connection and preservation of {specConnected.length} generated spec declarations)"
    "lean" #[stmtCheck.toString] (env := #[("LEAN_PATH", some lp)])
  let specAudited := auditedNames s.stdout
  let expectedSpec := specConnected.flatMap fun (key, _) => [s!"conn_{shortName key}", s!"basic_{shortName key}", s!"pres_{shortName key}"]
  let missingSpec := expectedSpec.filter fun n => !specAudited.contains n
  if s.exitCode == 0 && missingSpec.isEmpty && !(contains s.stdout "forbidden") && !(contains s.stderr "forbidden") then
    ok s!"C44 / C45: the connection and preservation evidence of {specConnected.length} generated spec declarations ({expectedSpec.length} theorems) is audited with 0 forbidden dependencies"
  else fail s!"C44 / C45: connection evidence (Statements): exit {s.exitCode}, not audited: {missingSpec}\n{tail s.stdout 1500}\n{tail s.stderr 1500}"
  if specConnected.length != c42Decls.length then
    fail s!"C42: expected the {c42Decls.length} basic spec declarations to be connected, got {specConnected.length}"
  let specWrongs ← deriveWrongs "Statements" stmtText Naru.Backend.Statements.stmtName specMistranslations
  checkWrong "Statements" (outDir / "StatementsWrong.lean") (specWrongProgram specConnected specWrongs) specWrongs lp
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
