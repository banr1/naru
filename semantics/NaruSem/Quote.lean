import Lean
import Naru.Driver
import NaruSem.Scope

/-!
# Core の引用(IDEAL.md C39 / C44)

検査プログラムは、実際の compiler 経路(`Naru.compileFiles` → `Checked.core`)から得た宣言の Core を Lean の項として引用し
(`def core_f : Naru.Core.Expr := …`)、その上で適格性(`wtR` / `wtS`)や値 / 命題の対応を kernel に検査させる。
引用した Core が実際に入力された Core と一致することは、同じ検査プログラムの中で `run_cmd` が同じソースを再びコンパイルして
`==`(構造の等しさ)で照合する(`checkDecls`)。誤出力に合わせて期待側を変えないための仕組みで、不一致ならその Lean ファイルの
検査が失敗する。

- `expr` / `pat` / `tyV` / `lit`: Core の木を Lean の項の文字列にする(`Naru.Core.Expr.…` の完全修飾)。対象外の構文も写す
  (対象外であることは `wtR` / `wtS` が `none` で判定する)。
- `fnBody? key core`: 修飾名 `key` の fn / spec 宣言の本体。
- `checkDecls path expected`: `path` をコンパイルし、`expected` の各 (修飾名, 引用した Core) が実際の Core と一致することを確かめる。
-/

namespace NaruSem.Quote
open Naru

deriving instance BEq for TyV
deriving instance BEq for Core.Pat
deriving instance BEq for Core.Expr, Core.Arm

/-- Lean の文字列リテラル。 -/
def str (s : String) : String := s.quote

partial def tyV : TyV → String
  | .bool => "Naru.TyV.bool"
  | .nat => "Naru.TyV.nat"
  | .int => "Naru.TyV.int"
  | .string => "Naru.TyV.string"
  | .unit => "Naru.TyV.unit"
  | .option t => s!"(Naru.TyV.option {tyV t})"
  | .result t e => s!"(Naru.TyV.result {tyV t} {tyV e})"
  | .list t => s!"(Naru.TyV.list {tyV t})"
  | .set t => s!"(Naru.TyV.set {tyV t})"
  | .table k v => s!"(Naru.TyV.table {tyV k} {tyV v})"
  | .tuple ts => s!"(Naru.TyV.tuple {list (ts.map tyV)})"
  | .named k d => s!"(Naru.TyV.named {str k} {str d})"
  | .fn ps r => s!"(Naru.TyV.fn {list (ps.map tyV)} {tyV r})"
  | .mvar n => s!"(Naru.TyV.mvar {n})"
  | .unknown => "Naru.TyV.unknown"
where
  list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def lit : Lit → String
  | .nat n => s!"(Naru.Lit.nat {n})"
  | .str s => s!"(Naru.Lit.str {str s})"
  | .bool b => s!"(Naru.Lit.bool {b})"
  | .unit => "Naru.Lit.unit"

def quant : Quant → String
  | .forall_ => "Naru.Quant.forall_"
  | .exists_ => "Naru.Quant.exists_"

partial def pat : Core.Pat → String
  | .wild => "Naru.Core.Pat.wild"
  | .bind x => s!"(Naru.Core.Pat.bind {str x})"
  | .lit l => s!"(Naru.Core.Pat.lit {lit l})"
  | .tuple ps => s!"(Naru.Core.Pat.tuple {list (ps.map pat)})"
  | .builtin n ps => s!"(Naru.Core.Pat.builtin {str n} {list (ps.map pat)})"
  | .variant k v ps => s!"(Naru.Core.Pat.variant {str k} {str v} {list (ps.map pat)})"

def binder (b : String × TyV) : String := s!"({str b.1}, {tyV b.2})"

mutual

partial def expr : Core.Expr → String
  | .lit l t => s!"(Naru.Core.Expr.lit {lit l} {tyV t})"
  | .var x => s!"(Naru.Core.Expr.var {str x})"
  | .global k => s!"(Naru.Core.Expr.global {str k})"
  | .call k args => s!"(Naru.Core.Expr.call {str k} {list (args.map expr)})"
  | .callLocal f args => s!"(Naru.Core.Expr.callLocal {expr f} {list (args.map expr)})"
  | .method tn n r args rt => s!"(Naru.Core.Expr.method {str tn} {str n} {expr r} {list (args.map expr)} {tyV rt})"
  | .builtin n args t => s!"(Naru.Core.Expr.builtin {str n} {list (args.map expr)} {tyV t})"
  | .variant k v args => s!"(Naru.Core.Expr.variant {str k} {str v} {list (args.map expr)})"
  | .field r k n => s!"(Naru.Core.Expr.field {expr r} {str k} {str n})"
  | .binop op l r t => s!"(Naru.Core.Expr.binop {str op} {expr l} {expr r} {tyV t})"
  | .unop op a => s!"(Naru.Core.Expr.unop {str op} {expr a})"
  | .ite c t e => s!"(Naru.Core.Expr.ite {expr c} {expr t} {expr e})"
  | .match_ s st arms => s!"(Naru.Core.Expr.match_ {expr s} {tyV st} {list (arms.map arm)})"
  | .let_ x t v b => s!"(Naru.Core.Expr.let_ {str x} {tyV t} {expr v} {expr b})"
  | .record k fs base =>
    let fields := list (fs.map fun (f, x) => s!"({str f}, {expr x})")
    let b := match base with
      | some e => s!"(some {expr e})"
      | none => "none"
    s!"(Naru.Core.Expr.record {str k} {fields} {b})"
  | .list es t => s!"(Naru.Core.Expr.list {list (es.map expr)} {tyV t})"
  | .tuple es => s!"(Naru.Core.Expr.tuple {list (es.map expr)})"
  | .lambda ps b => s!"(Naru.Core.Expr.lambda {list (ps.map binder)} {expr b})"
  | .quant q bs b => s!"(Naru.Core.Expr.quant {quant q} {list (bs.map binder)} {expr b})"
  | .error => "Naru.Core.Expr.error"

partial def arm : Core.Arm → String
  | .mk p g b =>
    let gs := match g with
      | some g => s!"(some {expr g})"
      | none => "none"
    s!"(Naru.Core.Arm.mk {pat p} {gs} {expr b})"

end

/-- 修飾名の fn / spec 宣言: (仮引数, 本体)。 -/
def fnOf? (key : String) (core : Array Core.Module) : Option (List Core.Param × Option Core.Expr) :=
  core.toList.findSome? fun m => m.decls.toList.findSome? fun d =>
    match d with
    | .fn k _ _ params _ body => if k == key then some (params, body) else none
    | _ => none

/-- 本体の Core。 -/
def fnBody? (key : String) (core : Array Core.Module) : Option Core.Expr :=
  match fnOf? key core with
  | some (_, some b) => some b
  | _ => none

/-- 仮引数から文脈の項: `NaruSem.Ctx.ofList [("x", NaruSem.Ty.nat), …]`(runtime)/ `NaruSem.SCtx.ofList [("x", NaruSem.STy.val NaruSem.Ty.nat), …]`
(spec)。Nat / Bool 以外の仮引数があれば `none`(対象外)。 -/
def ctxOf (params : List Core.Param) (spec : Bool) : Option String := do
  let entries ← params.mapM fun p => do
    let t ← match p.ty with
      | .nat => some "NaruSem.Ty.nat"
      | .bool => some "NaruSem.Ty.bool"
      | _ => none
    let t := if spec then s!"NaruSem.STy.val {t}" else t
    return s!"({str p.name}, {t})"
  return (if spec then "NaruSem.SCtx.ofList " else "NaruSem.Ctx.ofList ") ++ list entries

open Lean Elab Command in
/-- `run_cmd NaruSem.Quote.checkDecls "<path>" [("<修飾名>", core_f), …]`: ソースをコンパイルし、引用した Core が実際の Core と
一致することを確かめる(診断があれば・宣言が無ければ・不一致なら失敗)。 -/
def checkDecls (path : String) (expected : List (String × Core.Expr)) : CommandElabM Unit := do
  let (diags, checked) ← Naru.compileFiles [path]
  unless diags.isEmpty do
    throwError "checkDecls: {path} has {diags.size} diagnostic(s): {diags.toList.map (·.msg)}"
  let mut n : Nat := 0
  for (key, e) in expected do
    match fnBody? key checked.core with
    | none => throwError "checkDecls: {path} has no fn / spec declaration `{key}` with a body"
    | some actual =>
      unless actual == e do
        throwError "checkDecls: the quoted Core of `{key}` differs from the Core produced by the compiler for {path}:\n  quoted: {expr e}\n  actual: {expr actual}"
      n := n + 1
  logInfo m!"checkDecls: {n} quoted Core expression(s) agree with the compiler's Core of {path}"

end NaruSem.Quote
