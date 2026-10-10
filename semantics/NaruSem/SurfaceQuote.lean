import Lean
import Naru.Driver
import NaruSem.Surface

/-!
# Surface AST の引用(IDEAL.md C48 / C51)

検査プログラムは、実際の構文解析の出力(`Naru.compileFiles` → `Checked.mods` の各宣言の `body`)を対象の型 `Surf.Expr` に写し(`ofAst?`。
対象外の構文を含めば `none`)、Lean の項として引用して(`def ast_f : NaruSem.Surf.Expr := …`)、その上で適格性(`Surf.wtR` / `Surf.wtS`)を
kernel に検査させる。引用した AST が実際に構文解析された AST と一致することは、同じ検査プログラムの中で `run_cmd` が同じソースを再び
構文解析し、引用の埋め込み `Expr.toAst`(構築子ごとに同じ構築子へ写す。位置情報も含めて情報を落とさない)と `==`(構造の等しさ。
コンパイラの型 `Naru.Expr` の上)で照合する(`checkDecls`)。誤った変換結果に合わせて期待側を変えないための仕組みで、不一致なら
その Lean ファイルの検査が失敗する。

- `ofAst?` — 構文解析の出力 → 対象の AST。対象外の構築子(呼出し・欄・record / list / tuple のリテラル・lambda・名前付き引数・`e;` 文・
  型の tuple / 関数型)があれば `none`(リテラルは文字列・`()` も写り、`wtR` / `wtS` が対象外にする)。`ofDeclAst?` — 構文解析の宣言 → 最小の fn / spec 宣言の包装
  `Surf.Decl`(fn / spec 宣言が使わない欄が既定値で、本体があり、対象の構文だけから成るとき)。
- `expr` / `arm` / `stmt` / `pat` / `ty` / `binder` / `span` / `param` / `declWith` / `declTy` — 対象の AST を Lean の項の文字列にする(`NaruSem.Surf.Expr.…` の完全修飾)。
- `declOf? key mods` — 修飾名 `key` の fn / spec 宣言(構文解析の出力)と本体。`paramCtx? params` — 仮引数の型注釈から文脈。
- `checkDecls path expected` — `path` を構文解析し、`expected` の各 (修飾名, 引用した宣言) の埋め込み(`Decl.toAst`)が実際に構文解析された宣言(種別・名前・
  位置・仮引数・戻り型・本体)と一致することを確かめる。
-/

namespace NaruSem.Surf.Quote
open Naru

deriving instance BEq for Naru.Ty
deriving instance BEq for Naru.Binder
deriving instance BEq for Naru.Pattern, Naru.Expr, Naru.Arg, Naru.Arm, Naru.Stmt
deriving instance BEq for Naru.Param, Naru.Field, Naru.Variant
deriving instance BEq for Naru.Decl

/-! ## 構文解析の出力 → 対象の AST -/

partial def tyOfAst? : Naru.Ty → Option Ty
  | .named sp n args => do
    let args' ← args.toList.mapM tyOfAst?
    return .named sp n args'
  | _ => none

def patOfAst? : Naru.Pattern → Option Pat
  | .wild sp => some (.wild sp)
  | .bind sp x => some (.bind sp x)
  | .lit sp l => some (.lit sp l)
  | _ => none

def binderOfAst? (b : Naru.Binder) : Option Binder :=
  match b.ty with
  | none => some { name := b.name, ty := none, span := b.span }
  | some t => (tyOfAst? t).map fun t' => { name := b.name, ty := some t', span := b.span }

mutual

/-- 構文解析の出力を対象の AST に写す。対象外の構築子を含めば `none`。 -/
partial def ofAst? : Naru.Expr → Option Expr
  | .lit sp l => some (.lit sp l)
  | .var sp n => some (.var sp n)
  | .method sp r n args => do
    let r' ← ofAst? r
    let args' ← args.toList.mapM argOfAst?
    return .method sp r' n args'
  | .binop sp op l r => do return .binop sp op (← ofAst? l) (← ofAst? r)
  | .unop sp op a => do return .unop sp op (← ofAst? a)
  | .ite sp c t e => do return .ite sp (← ofAst? c) (← ofAst? t) (← ofAst? e)
  | .matchE sp s arms => do return .matchE sp (← ofAst? s) (← arms.toList.mapM armOfAst?)
  | .block sp stmts tail => do
    let stmts' ← stmts.toList.mapM stmtOfAst?
    let tail' ← match tail with
      | some e => some <$> ofAst? e
      | none => pure none
    return .block sp stmts' tail'
  | .quant sp q bs b => do
    let bs' ← bs.toList.mapM binderOfAst?
    return .quant sp q bs' (← ofAst? b)
  | _ => none

partial def argOfAst? : Naru.Arg → Option Expr
  | .pos e => ofAst? e
  | .named .. => none

partial def armOfAst? : Naru.Arm → Option Arm
  | .mk p g b => do
    let p' ← patOfAst? p
    let g' ← match g with
      | some g => some <$> ofAst? g
      | none => pure none
    return .mk p' g' (← ofAst? b)

partial def stmtOfAst? : Naru.Stmt → Option Stmt
  | .letS sp x ty v => do
    let ty' ← match ty with
      | some t => some <$> tyOfAst? t
      | none => pure none
    return .letS sp x ty' (← ofAst? v)
  | _ => none

end

def paramOfAst? (p : Naru.Param) : Option Param :=
  (tyOfAst? p.ty).map fun t => { name := p.name, ty := t, span := p.span }

/-- 構文解析の宣言を最小の fn / spec 宣言の包装に写す。fn / spec 宣言が使わない欄(別名・欄・variant・derive・項目・owner)が既定値でなければ、
本体が無ければ、対象外の構文を含めば `none`。 -/
def ofDeclAst? (d : Naru.Decl) : Option Decl := do
  guard (d.aliasOf.isNone && d.fields.isEmpty && d.variants.isEmpty && d.derives.isEmpty && d.items.isEmpty && d.owner.isNone)
  let body ← d.body
  let body' ← ofAst? body
  let params ← d.params.toList.mapM paramOfAst?
  let ret ← match d.ret with
    | some t => some <$> tyOfAst? t
    | none => pure none
  return { kind := d.kind, name := d.name, span := d.span, params, ret, body := body' }

/-! ## Lean の項への引用 -/

def str (s : String) : String := s.quote

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def span (sp : Span) : String := s!"(Naru.Span.mk {sp.line} {sp.col})"

def lit : Lit → String
  | .nat n => s!"(Naru.Lit.nat {n})"
  | .str s => s!"(Naru.Lit.str {str s})"
  | .bool b => s!"(Naru.Lit.bool {b})"
  | .unit => "Naru.Lit.unit"

def quant : Quant → String
  | .forall_ => "Naru.Quant.forall_"
  | .exists_ => "Naru.Quant.exists_"

partial def ty : Ty → String
  | .named sp n args => s!"(NaruSem.Surf.Ty.named {span sp} {list (n.map str)} {list (args.map ty)})"

def pat : Pat → String
  | .wild sp => s!"(NaruSem.Surf.Pat.wild {span sp})"
  | .bind sp x => s!"(NaruSem.Surf.Pat.bind {span sp} {str x})"
  | .lit sp l => s!"(NaruSem.Surf.Pat.lit {span sp} {lit l})"

def optTy : Option Ty → String
  | some t => s!"(some {ty t})"
  | none => "none"

def binder (b : Binder) : String :=
  s!"(\{ name := {str b.name}, ty := {optTy b.ty}, span := {span b.span} } : NaruSem.Surf.Binder)"

mutual

partial def expr : Expr → String
  | .lit sp l => s!"(NaruSem.Surf.Expr.lit {span sp} {lit l})"
  | .var sp n => s!"(NaruSem.Surf.Expr.var {span sp} {list (n.map str)})"
  | .method sp r n args => s!"(NaruSem.Surf.Expr.method {span sp} {expr r} {str n} {list (args.map expr)})"
  | .binop sp op l r => s!"(NaruSem.Surf.Expr.binop {span sp} {str op} {expr l} {expr r})"
  | .unop sp op a => s!"(NaruSem.Surf.Expr.unop {span sp} {str op} {expr a})"
  | .ite sp c t e => s!"(NaruSem.Surf.Expr.ite {span sp} {expr c} {expr t} {expr e})"
  | .matchE sp s arms => s!"(NaruSem.Surf.Expr.matchE {span sp} {expr s} {list (arms.map arm)})"
  | .block sp stmts tail =>
    let t := match tail with
      | some e => s!"(some {expr e})"
      | none => "none"
    s!"(NaruSem.Surf.Expr.block {span sp} {list (stmts.map stmt)} {t})"
  | .quant sp q bs b => s!"(NaruSem.Surf.Expr.quant {span sp} {quant q} {list (bs.map binder)} {expr b})"

partial def arm : Arm → String
  | .mk p g b =>
    let gs := match g with
      | some g => s!"(some {expr g})"
      | none => "none"
    s!"(NaruSem.Surf.Arm.mk {pat p} {gs} {expr b})"

partial def stmt : Stmt → String
  | .letS sp x t v => s!"(NaruSem.Surf.Stmt.letS {span sp} {str x} {optTy t} {expr v})"

end

def declKind : DeclKind → String
  | .typeAlias => "Naru.DeclKind.typeAlias"
  | .record => "Naru.DeclKind.record"
  | .enum => "Naru.DeclKind.enum"
  | .input => "Naru.DeclKind.input"
  | .fn => "Naru.DeclKind.fn"
  | .state => "Naru.DeclKind.state"
  | .protocol => "Naru.DeclKind.protocol"
  | .predicate => "Naru.DeclKind.predicate"
  | .condition => "Naru.DeclKind.condition"
  | .regime => "Naru.DeclKind.regime"
  | .property => "Naru.DeclKind.property"
  | .claim => "Naru.DeclKind.claim"
  | .claimBundle => "Naru.DeclKind.claimBundle"
  | .scenario => "Naru.DeclKind.scenario"
  | .observer => "Naru.DeclKind.observer"

def param (p : Param) : String :=
  s!"(\{ name := {str p.name}, ty := {ty p.ty}, span := {span p.span} } : NaruSem.Surf.Param)"

/-- 宣言の引用。本体は `bodyTerm`(既に引用した `ast_<f>` の名前など)で与える。 -/
def declWith (d : Decl) (bodyTerm : String) : String :=
  s!"(\{ kind := {declKind d.kind}, name := {str d.name}, span := {span d.span}, params := {list (d.params.map param)}, ret := {optTy d.ret}, body := {bodyTerm} } : NaruSem.Surf.Decl)"

def declTy : DeclTy → String
  | .runtime ctx t =>
    s!"(NaruSem.Surf.DeclTy.runtime {list (ctx.map fun (x, t) => s!"({str x}, {tyTerm t})")} {tyTerm t})"
  | .spec ctx τ =>
    let τs := match τ with
      | .val t => s!"(NaruSem.STy.val {tyTerm t})"
      | .prop => "NaruSem.STy.prop"
    s!"(NaruSem.Surf.DeclTy.spec {list (ctx.map fun (x, t) => s!"({str x}, {tyTerm t})")} {τs})"
where
  tyTerm : NaruSem.Ty → String
    | .nat => "NaruSem.Ty.nat"
    | .bool => "NaruSem.Ty.bool"

/-! ## 宣言の本体と仮引数 -/

/-- 修飾名の fn / spec 宣言(構文解析の出力): (宣言, 本体)。 -/
def declOf? (key : String) (mods : Array Naru.Module) : Option (Naru.Decl × Naru.Expr) :=
  mods.toList.findSome? fun m => m.decls.toList.findSome? fun d =>
    if renderPath (m.name ++ [d.name]) == key && Typecheck.isFnLike d.kind then d.body.map fun b => (d, b) else none

/-- 宣言の本体(構文解析の出力)。 -/
def declBody? (key : String) (mods : Array Naru.Module) : Option Naru.Expr := (declOf? key mods).map (·.2)

/-- 仮引数の型注釈から対象の型。 -/
def paramTy? (p : Naru.Param) : Option NaruSem.Ty := (tyOfAst? p.ty).bind Ty.toTy?

/-- 仮引数の型注釈から文脈の項目(名前, 型)。Nat / Bool 以外の仮引数があれば `none`(対象外)。 -/
def paramCtx? (params : Array Naru.Param) : Option (List (String × NaruSem.Ty)) :=
  params.toList.mapM fun p => (paramTy? p).map fun t => (p.name, t)

def tyTerm : NaruSem.Ty → String
  | .nat => "NaruSem.Ty.nat"
  | .bool => "NaruSem.Ty.bool"

/-- 文脈の項: `NaruSem.Ctx.ofList [("x", NaruSem.Ty.nat), …]`(runtime)/ `NaruSem.SCtx.ofList [("x", NaruSem.STy.val NaruSem.Ty.nat), …]`(spec)。 -/
def ctxTerm (entries : List (String × NaruSem.Ty)) (spec : Bool) : String :=
  let items := entries.map fun (x, t) =>
    if spec then s!"({str x}, NaruSem.STy.val {tyTerm t})" else s!"({str x}, {tyTerm t})"
  (if spec then "NaruSem.SCtx.ofList " else "NaruSem.Ctx.ofList ") ++ list items

open Lean Elab Command in
/-- `run_cmd NaruSem.Surf.Quote.checkDecls "<path>" [("<修飾名>", decl_f), …]`: ソースを構文解析し、引用した宣言(種別・名前・位置・仮引数・戻り型・本体)の
埋め込み(`Decl.toAst`)が実際に構文解析された宣言と `==` で一致することを確かめる(診断があれば・宣言が無ければ・不一致なら失敗)。 -/
def checkDecls (path : String) (expected : List (String × Decl)) : CommandElabM Unit := do
  let (diags, checked) ← Naru.compileFiles [path]
  unless diags.isEmpty do
    throwError "checkDecls: {path} has {diags.size} diagnostic(s): {diags.toList.map (·.msg)}"
  let mut n : Nat := 0
  for (key, d) in expected do
    match declOf? key checked.mods with
    | none => throwError "checkDecls: {path} has no fn / spec declaration `{key}` with a body"
    | some (actual, body) =>
      unless d.toAst == actual do
        throwError "checkDecls: the quoted Surface AST declaration `{key}` differs from the declaration the parser produces for {path}:\n  quoted: {declWith d (expr d.body)}\n  actual: {(ofDeclAst? actual).map (fun a => declWith a (expr a.body)) |>.getD s!"(outside the Surface subset: {(ofAst? body).map expr |>.getD "body outside the subset"})"}"
      n := n + 1
  logInfo m!"checkDecls: {n} quoted Surface AST declaration(s) agree with the parser's AST of {path}"

end NaruSem.Surf.Quote
