import Lean
import Naru.Driver
import NaruSem.Quote
import NaruSem.SurfaceQuote
import NaruSem.Call
import NaruSem.SurfaceCall

/-!
# 宣言群の引用(IDEAL.md C54 / C57)

検査プログラムは、実際の compiler 経路から得た宣言群を Lean の項として引用し(Core: `NaruSem.Call.Prog`、Surface AST: `NaruSem.Surf.Call.Prog`。
どちらも依存順に並べる)、その上で宣言群の適格性(`Call.wtProg` / `Surf.Call.wtProg`)を kernel に検査させる。引用した宣言群が実際の入力・出力と
一致することは、同じ検査プログラムの中で `run_cmd` が同じソースを再びコンパイル / 構文解析して照合する(`checkProg`): 引用した各宣言が
実際の宣言(鍵・種別・仮引数の名前と型・戻り型・本体)と一致し、実際の fn / input / spec 宣言がすべて引用されている(宣言群全体。順序は問わない)。
誤った変換結果に合わせて期待側を変えないための仕組みで、不一致ならその Lean ファイルの検査が失敗する。

- Core: `Call.Quote.declOf? : Core.Decl → Option Call.Decl`(対象の宣言 — fn / input は仮引数と戻り型が Nat / Bool、spec 宣言は仮引数が Nat / Bool —
  を `Call.Decl` に写す。対象外なら `none`)、`Call.Quote.decl`(Lean の項の文字列)、`Call.Quote.checkProg`。
- Surface: `Surf.Call.Quote.ofAst?`(構文解析の出力 → 対象の AST。呼出し・名前付き引数・UFCS を含む)、`ofDeclAst?`(宣言 → `Surf.Call.Decl`。
  モジュール名つき)、`expr` / `decl`(Lean の項の文字列)、`Surf.Call.Quote.checkProg`。
-/

namespace NaruSem.Call.Quote
open Naru

/-- Core の仮引数 → (名前, 対象の型)。Nat / Bool 以外は `none`。 -/
def paramOf? (p : Core.Param) : Option (String × Ty) :=
  match p.ty with
  | .nat => some (p.name, .nat)
  | .bool => some (p.name, .bool)
  | _ => none

/-- 対象の宣言を Core の宣言から写す: fn(本体あり、戻り型 Nat / Bool)、input(本体なし、戻り型 Nat / Bool)、spec 宣言(本体あり)。 -/
def declOf? (d : Core.Decl) : Option Decl :=
  match d with
  | .fn k _ kind params ret body => do
    let ps ← params.mapM paramOf?
    match kind, body with
    | .fn, some b =>
      match ret with
      | .nat => some (.fn k ps .nat b)
      | .bool => some (.fn k ps .bool b)
      | _ => none
    | .input, none =>
      match ret with
      | .nat => some (.input k ps .nat)
      | .bool => some (.input k ps .bool)
      | _ => none
    | kind, some b => if kind.phase == .spec then some (.spec k ps b) else none
    | _, _ => none
  | _ => none

def str (s : String) : String := s.quote

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def tyTerm : Ty → String
  | .nat => "NaruSem.Ty.nat"
  | .bool => "NaruSem.Ty.bool"

def params (ps : List (String × Ty)) : String := list (ps.map fun (x, t) => s!"({str x}, {tyTerm t})")

/-- 宣言の引用。本体は `bodyTerm`(既に引用した `core_<f>` の名前など)で与える。 -/
def declWith (d : Decl) (bodyTerm : String) : String :=
  match d with
  | .fn k ps t _ => s!"(NaruSem.Call.Decl.fn {str k} {params ps} {tyTerm t} {bodyTerm})"
  | .spec k ps _ => s!"(NaruSem.Call.Decl.spec {str k} {params ps} {bodyTerm})"
  | .input k ps t => s!"(NaruSem.Call.Decl.input {str k} {params ps} {tyTerm t})"

def sig : Sig → String
  | .fn ps t => s!"(NaruSem.Call.Sig.fn {list (ps.map tyTerm)} {tyTerm t})"
  | .input ps t => s!"(NaruSem.Call.Sig.input {list (ps.map tyTerm)} {tyTerm t})"
  | .spec ps => s!"(NaruSem.Call.Sig.spec {list (ps.map tyTerm)})"

def declBEq : Decl → Decl → Bool
  | .fn k ps t b, .fn k' ps' t' b' => k == k' && ps == ps' && t == t' && b == b'
  | .spec k ps b, .spec k' ps' b' => k == k' && ps == ps' && b == b'
  | .input k ps t, .input k' ps' t' => k == k' && ps == ps' && t == t'
  | _, _ => false

instance : BEq Decl := ⟨declBEq⟩

/-- 単位の fn / input / spec 宣言のうち対象のもの(修飾名, 宣言)。対象外の宣言(仮引数や戻り型が Nat / Bool でない等)は含めない。 -/
def declsOf (core : Array Core.Module) : List (String × Decl) :=
  core.toList.flatMap fun m => m.decls.toList.filterMap fun d => (declOf? d).map fun c => (d.key, c)

/-- 単位の fn / input / spec 宣言の修飾名(対象外も含む)。 -/
def fnLikeKeys (core : Array Core.Module) : List String :=
  core.toList.flatMap fun m => m.decls.toList.filterMap fun d =>
    match d with
    | .fn k _ kind .. => if kind == .fn || kind == .input || kind.phase == .spec then some k else none
    | _ => none

open Lean Elab Command in
/-- `run_cmd NaruSem.Call.Quote.checkProg "<path>" prog`: ソースをコンパイルし、引用した宣言群の各宣言が実際の Core の宣言(鍵・種別・仮引数・戻り型・本体)と
一致し、実際の fn / input / spec 宣言がすべて引用されていることを確かめる(診断があれば・不一致・欠落・余分があれば失敗)。
`otherPaths` は同じコンパイル単位の他ファイル。空なら従来の単一ファイル検査。 -/
def checkProg (path : String) (prog : Prog) (otherPaths : List String := []) : CommandElabM Unit := do
  let (diags, checked) ← Naru.compileFiles (path :: otherPaths)
  unless diags.isEmpty do
    throwError "checkProg: {path} has {diags.size} diagnostic(s): {diags.toList.map (·.msg)}"
  let actual := declsOf checked.core
  for q in prog do
    match actual.lookup q.key with
    | none => throwError "checkProg: {path} has no fn / input / spec declaration `{q.key}` in the Core (or it is outside the scope)"
    | some a =>
      unless a == q do
        throwError "checkProg: the quoted declaration `{q.key}` differs from the Core the compiler produces for {path}:\n  quoted: {declWith q "…"}\n  actual: {declWith a "…"}"
  let quotedKeys := prog.map Decl.key
  for k in fnLikeKeys checked.core do
    unless quotedKeys.contains k do
      throwError "checkProg: the fn / input / spec declaration `{k}` of {path} is not quoted (the quoted program must cover the whole declaration group)"
  for k in quotedKeys do
    unless (quotedKeys.filter (· == k)).length == 1 do
      throwError "checkProg: the declaration `{k}` is quoted twice"
  logInfo m!"checkProg: {prog.length} quoted Core declaration(s) agree with the compiler's Core of {path} and cover all its fn / input / spec declarations"

end NaruSem.Call.Quote

namespace NaruSem.Surf.Call.Quote
open Naru

/-! ## 構文解析の出力 → 対象の AST -/

mutual

/-- 構文解析の出力を対象の AST に写す。呼出し(実引数は位置・名前付き)と UFCS を含む。対象外の構築子(欄・record / list / tuple のリテラル・lambda)を含めば `none`。 -/
partial def ofAst? : Naru.Expr → Option Expr
  | .lit sp l => some (.lit sp l)
  | .var sp n => some (.var sp n)
  | .call sp f args => do return .call sp (← ofAst? f) (← args.toList.mapM argOfAst?)
  | .method sp r n args => do return .method sp (← ofAst? r) n (← args.toList.mapM argOfAst?)
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
    let bs' ← bs.toList.mapM Surf.Quote.binderOfAst?
    return .quant sp q bs' (← ofAst? b)
  | _ => none

partial def argOfAst? : Naru.Arg → Option Arg
  | .pos e => (ofAst? e).map .pos
  | .named n e => (ofAst? e).map (.named n)

partial def armOfAst? : Naru.Arm → Option Arm
  | .mk p g b => do
    let p' ← Surf.Quote.patOfAst? p
    let g' ← match g with
      | some g => some <$> ofAst? g
      | none => pure none
    return .mk p' g' (← ofAst? b)

partial def stmtOfAst? : Naru.Stmt → Option Stmt
  | .letS sp x ty v => do
    let ty' ← match ty with
      | some t => some <$> Surf.Quote.tyOfAst? t
      | none => pure none
    return .letS sp x ty' (← ofAst? v)
  | _ => none

end

/-- 構文解析の宣言(とそのモジュール名)を対象の宣言に写す。fn / input / spec 宣言で、使わない欄が既定値で、本体(あれば)が対象の構文だけから成るとき。 -/
def ofDeclAst? (module : List String) (d : Naru.Decl) : Option Decl := do
  guard (d.aliasOf.isNone && d.fields.isEmpty && d.variants.isEmpty && d.derives.isEmpty && d.items.isEmpty && d.owner.isNone)
  guard (d.kind == .fn || d.kind == .input || d.kind.phase == .spec)
  let body ← match d.body with
    | some b => some <$> ofAst? b
    | none => pure none
  let params ← d.params.toList.mapM Surf.Quote.paramOfAst?
  let ret ← match d.ret with
    | some t => some <$> Surf.Quote.tyOfAst? t
    | none => pure none
  return { module, kind := d.kind, name := d.name, span := d.span, params, ret, body }

/-! ## Lean の項への引用 -/

open Surf.Quote (str list span lit quant ty pat optTy binder declKind param)

mutual

partial def expr : Expr → String
  | .lit sp l => s!"(NaruSem.Surf.Call.Expr.lit {span sp} {lit l})"
  | .var sp n => s!"(NaruSem.Surf.Call.Expr.var {span sp} {list (n.map str)})"
  | .call sp f args => s!"(NaruSem.Surf.Call.Expr.call {span sp} {expr f} {list (args.map arg)})"
  | .method sp r n args => s!"(NaruSem.Surf.Call.Expr.method {span sp} {expr r} {str n} {list (args.map arg)})"
  | .binop sp op l r => s!"(NaruSem.Surf.Call.Expr.binop {span sp} {str op} {expr l} {expr r})"
  | .unop sp op a => s!"(NaruSem.Surf.Call.Expr.unop {span sp} {str op} {expr a})"
  | .ite sp c t e => s!"(NaruSem.Surf.Call.Expr.ite {span sp} {expr c} {expr t} {expr e})"
  | .matchE sp s arms => s!"(NaruSem.Surf.Call.Expr.matchE {span sp} {expr s} {list (arms.map arm)})"
  | .block sp stmts tail =>
    let t := match tail with
      | some e => s!"(some {expr e})"
      | none => "none"
    s!"(NaruSem.Surf.Call.Expr.block {span sp} {list (stmts.map stmt)} {t})"
  | .quant sp q bs b => s!"(NaruSem.Surf.Call.Expr.quant {span sp} {quant q} {list (bs.map binder)} {expr b})"

partial def arg : Arg → String
  | .pos e => s!"(NaruSem.Surf.Call.Arg.pos {expr e})"
  | .named n e => s!"(NaruSem.Surf.Call.Arg.named {str n} {expr e})"

partial def arm : Arm → String
  | .mk p g b =>
    let gs := match g with
      | some g => s!"(some {expr g})"
      | none => "none"
    s!"(NaruSem.Surf.Call.Arm.mk {pat p} {gs} {expr b})"

partial def stmt : Stmt → String
  | .letS sp x t v => s!"(NaruSem.Surf.Call.Stmt.letS {span sp} {str x} {optTy t} {expr v})"

end

/-- 宣言の引用。本体は `bodyTerm`(`some ast_<f>` / `none`)で与える。 -/
def declWith (d : Decl) (bodyTerm : String) : String :=
  s!"(\{ module := {list (d.module.map str)}, kind := {declKind d.kind}, name := {str d.name}, span := {span d.span}, params := {list (d.params.map param)}, ret := {optTy d.ret}, body := {bodyTerm} } : NaruSem.Surf.Call.Decl)"

/-- 単位の fn / input / spec 宣言(構文解析の出力)のうち対象のもの: (修飾名, モジュール名, 宣言, 対象の宣言)。 -/
def declsOf (mods : Array Naru.Module) : List (String × Decl) :=
  mods.toList.flatMap fun m => m.decls.toList.filterMap fun d =>
    (ofDeclAst? m.name d).map fun sd => (sd.key, sd)

/-- 単位の fn / input / spec 宣言の修飾名(対象外も含む)。 -/
def fnLikeKeys (mods : Array Naru.Module) : List String :=
  mods.toList.flatMap fun m => m.decls.toList.filterMap fun d =>
    if d.kind == .fn || d.kind == .input || d.kind.phase == .spec then some (renderPath (m.name ++ [d.name])) else none

open Lean Elab Command in
/-- `run_cmd NaruSem.Surf.Call.Quote.checkProg "<path>" prog`: ソースを構文解析し、引用した宣言群の各宣言の埋め込み(`Decl.toAst`、モジュール名)が実際に構文解析された
宣言(種別・名前・位置・仮引数・戻り型・本体)と `==` で一致し、実際の fn / input / spec 宣言がすべて引用されていることを確かめる。
`otherPaths` も同じ単位として再構文解析する。 -/
def checkProg (path : String) (prog : Prog) (otherPaths : List String := []) : CommandElabM Unit := do
  let (diags, checked) ← Naru.compileFiles (path :: otherPaths)
  unless diags.isEmpty do
    throwError "checkProg: {path} has {diags.size} diagnostic(s): {diags.toList.map (·.msg)}"
  for q in prog do
    match checked.mods.toList.find? (fun m => m.name == q.module) with
    | none => throwError "checkProg: {path} has no module `{renderPath q.module}` (quoted declaration `{q.key}`)"
    | some m =>
      match m.decls.toList.find? (fun d => d.name == q.name) with
      | none => throwError "checkProg: module `{renderPath q.module}` of {path} has no declaration `{q.name}`"
      | some actual =>
        unless q.toAst == actual do
          throwError "checkProg: the quoted Surface AST declaration `{q.key}` differs from the declaration the parser produces for {path}:\n  quoted: {declWith q (q.body.map (fun b => s!"(some {expr b})") |>.getD "none")}\n  actual: {(ofDeclAst? m.name actual).map (fun a => declWith a (a.body.map (fun b => s!"(some {expr b})") |>.getD "none")) |>.getD "(outside the Surface subset)"}"
  let quotedKeys := prog.map Decl.key
  for k in fnLikeKeys checked.mods do
    unless quotedKeys.contains k do
      throwError "checkProg: the fn / input / spec declaration `{k}` of {path} is not quoted (the quoted program must cover the whole declaration group)"
  for k in quotedKeys do
    unless (quotedKeys.filter (· == k)).length == 1 do
      throwError "checkProg: the declaration `{k}` is quoted twice"
  logInfo m!"checkProg: {prog.length} quoted Surface AST declaration(s) agree with the parser's AST of {path} and cover all its fn / input / spec declarations"

end NaruSem.Surf.Call.Quote
