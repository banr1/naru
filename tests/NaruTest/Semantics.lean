import NaruTest.Common
import NaruSem.Quote

/-!
# `naru_test semantics` — コンパイラ意味論保存の検査入口と、実際の Core の適格性(IDEAL.md C39 / C45)

1. C45 の検査入口 `lake build NaruSem`(意味論・一般定理・検体・公理監査を Lean kernel に検査させる)が exit 0。続けて
   `lake env lean semantics/NaruSem.lean` で公理監査の出力(`audit ok: <定数> depends on axioms […]`)を取り直し、必須の定理
   (`c39Theorems`)がすべて監査されていて、許容しない依存が 0 件であることを確かめる。
2. C39: 検体 `tests/accept/sem_core.naru` を実際の compiler 経路(`Naru.compileFiles`)でコンパイルし、`c39Decls` の各宣言(今回の保存対象の
   構文を 1 つずつ使う)の Core を Lean の項として引用した検査プログラム `.lake/naru/test/semantics/Scope.lean` を書き、`lean` で
   検査する: 各宣言の適格性(`wtR` / `wtS` = 期待の型。`decide` で kernel が計算する)と、引用した Core が compiler の Core と一致すること
   (`NaruSem.Quote.checkDecls` が同じソースを再びコンパイルして照合する)。
3. C45: 監査が禁止依存を失敗にすることを、`sorry` / `native_decide` / 存在しない定数の 3 つの負の検体で確かめる(`lean` が exit 非 0)。
-/

namespace NaruTest.Semantics
open NaruTest

def source : String := "tests/accept/sem_core.naru"
def outDir : System.FilePath := ".lake" / "naru" / "test" / "semantics"
def rootFile : String := "semantics/NaruSem.lean"

/-- 公理監査に現れなければならない定理(C39: 全域性・一意性)。 -/
def c39Theorems : List String :=
  ["NaruSem.eval_total", "NaruSem.Eval_unique", "NaruSem.Sem_exists", "NaruSem.Sem_unique"]

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

/-- 検査プログラム: 引用した Core(`core_<f>`)と文脈(`ctx_<f>`)、適格性の定理(`decide`)、引用の一致の照合(`run_cmd`)。 -/
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

def checks : M Unit := do
  let t0 ← IO.monoMsNow
  IO.FS.createDirAll outDir
  heading "C45 entry point"
  let _ ← step "C45: build the semantics, the general theorems, the specimens and the axiom audit" "lake" #["build", "NaruSem"]
  let a ← step "C45: re-run the axiom audit of the root file" "lake" #["env", "lean", rootFile]
  let auditLines := (a.stdout.splitOn "\n").filter fun l => contains l "audit ok:"
  let audited := auditLines.filterMap fun l => ((l.splitOn "audit ok: ").getD 1 "").splitOn " " |>.head?
  let missing := c39Theorems.filter fun n => !audited.contains n
  if a.exitCode == 0 && missing.isEmpty && !(contains a.stdout "forbidden") && !(contains a.stderr "forbidden") then
    ok s!"C45: the audit covers {auditLines.length} constant(s) including {c39Theorems} with 0 forbidden dependencies (allowed: propext / Classical.choice / Quot.sound)"
  else fail s!"C45: audit: exit {a.exitCode}, required theorems not audited: {missing}\n{tail a.stdout 1500}\n{tail a.stderr 1500}"
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
          | none => fail s!"C39: `{key}` (runtime) is not in scope (wtR = none): {NaruSem.Quote.expr body}"
  let scopeFile := outDir / "Scope.lean"
  IO.FS.writeFile scopeFile (scopeProgram quoted)
  let r ← step s!"C39: lean {scopeFile} (well-formedness of {quoted.length} quoted Core expressions by `decide`, identity with the compiler's Core)"
    "lean" #[scopeFile.toString] (env := #[("LEAN_PATH", some leanPath)])
  let agree := s!"checkDecls: {quoted.length} quoted Core expression(s) agree"
  if r.exitCode == 0 && (contains r.stdout agree || contains r.stderr agree) then
    ok s!"C39 / C44: the {quoted.length} quoted Core expressions are the Core the compiler produces for {source}"
  else fail s!"C39 / C44: identity of the quoted Core: expected `{agree}` in the output of lean {scopeFile}\n{tail r.stdout 1500}"
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
