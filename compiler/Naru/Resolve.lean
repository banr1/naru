import Std.Data.HashMap
import Naru.Ast

/-!
# 名前解決と phase 検査

コンパイル単位(渡されたすべての `.naru`)のトップレベル宣言を 1 つの表に集め、
各宣言の本体・型・引数に現れる名前を解決する。

- 解決できない名前 → E011
- 同名の宣言 → E012
- 型の位置に型でない宣言 → E013
- runtime 宣言から spec 宣言への参照 → **E001(phase leak)**

解決した参照(値の位置・型の位置の名前 → 宣言)は `Ref` として集め、`resolveAll` が診断と一緒に返す。モジュール構造の共通検査
(`Modules.lean`、E017)が、モジュール同士の参照の実在する行・列を引くのに使う(C18)。

型検査・capability 検査はこの後の段(別モジュール)で行う。
-/

namespace Naru.Resolve
open Std

structure Sym where
  name : String
  qualified : String
  kind : DeclKind
  file : String
  span : Span
  /-- 宣言のあるモジュールの名前。 -/
  module : List String := []
deriving Inhabited

/-- 解決した参照 1 つ: どのファイルのどの位置で、どの宣言の中から、どの宣言を参照したか。 -/
structure Ref where
  file : String
  span : Span
  /-- 参照が現れた宣言(文脈)の名前と種類。 -/
  declName : String
  declKind : DeclKind
  target : Sym
deriving Inhabited

/-- いま検査している宣言の文脈。 -/
structure Ctx where
  file : String
  declKind : DeclKind
  declName : String
  locals : List String

structure St where
  globals : HashMap String Sym := {}
  diags : Array Diagnostic := #[]
  /-- 解決した参照(出現順)。 -/
  refs : Array Ref := #[]

abbrev R := StateM St

instance : Inhabited (R Unit) := ⟨pure ()⟩
instance : Inhabited (R (List String)) := ⟨pure []⟩

def report (file : String) (span : Span) (code msg : String) : R Unit :=
  modify fun s => { s with diags := s.diags.push { file, span, code, msg } }

/-- 解決した参照を索引に足す。 -/
def record (ctx : Ctx) (span : Span) (sym : Sym) : R Unit :=
  modify fun s => { s with refs := s.refs.push { file := ctx.file, span, declName := ctx.declName, declKind := ctx.declKind, target := sym } }

/-- primitive 型(IDEAL.md「言語の意味論」)。 -/
def builtinTypes : List String :=
  ["Bool", "Nat", "Int", "String", "Unit", "Option", "Result", "List", "Set", "Table"]

/-- 組み込みの値・構築子・自由関数。stdlib が naru で書かれるまでの暫定。
`sort` は `sort(xs, by = …)`、`choose` / `pick` は常に E003(型検査の段で報告)。 -/
def builtinValues : List String := ["Some", "None", "Ok", "Err", "sort", "choose", "pick"]

def isBuiltinHead (head : String) : Bool :=
  builtinTypes.contains head || builtinValues.contains head

/-- 宣言を表に集める。同名・組み込み名の再宣言は E012。 -/
def collect (m : Module) : R Unit := do
  for d in m.decls do
    let s ← get
    if isBuiltinHead d.name then
      report m.file d.span Code.duplicate
        s!"`{d.name}` is a built-in name and cannot be redeclared"
      continue
    match s.globals.get? d.name with
    | some prev =>
      report m.file d.span Code.duplicate
        s!"`{d.name}` is already declared at {prev.file}:{prev.span.line}:{prev.span.col}"
    | none =>
      let sym : Sym :=
        { name := d.name, qualified := renderPath (m.name ++ [d.name]), kind := d.kind,
          file := m.file, span := d.span, module := m.name }
      modify fun s =>
        { s with globals := (s.globals.insert d.name sym).insert sym.qualified sym }

/-- 経路を解決する。`none` = 未解決、`some none` = 組み込み、`some (some sym)` = 宣言。
最長の接頭辞から試す(`Phase.Tick` は `Phase` で解決し、残りは variant / 欄)。 -/
def lookupPath (segs : List String) : R (Option (Option Sym)) := do
  match segs with
  | [] => return none
  | head :: _ =>
    if isBuiltinHead head then return some none
    let s ← get
    let mut k := segs.length
    while k > 0 do
      let key := renderPath (segs.take k)
      match s.globals.get? key with
      | some sym => return some (some sym)
      | none => k := k - 1
    return none

/-- 値の位置の参照。E011 と E001 を報告する。 -/
def checkRef (ctx : Ctx) (span : Span) (segs : List String) : R Unit := do
  match segs with
  | [] => return
  | head :: _ =>
    if ctx.locals.contains head then return
    match ← lookupPath segs with
    | none =>
      report ctx.file span Code.unresolved s!"cannot find `{renderPath segs}` in this scope"
    | some none => return
    | some (some sym) =>
      record ctx span sym
      if ctx.declKind.phase == .runtime && sym.kind.phase == .spec then
        report ctx.file span Code.phaseLeak
          s!"{ctx.declKind.describe} `{ctx.declName}` is a runtime declaration but refers to spec {sym.kind.describe} `{sym.name}`; runtime declarations cannot depend on spec declarations (phase leak)"

/-- ユーザ定義の型の経路。**完全一致**で解決する(`Block` / `Mod.Block`)。
接頭辞だけが一致する経路(`Block.whatever`)は型ではない(E011)。接頭辞の一致を許すと、
型検査が解決できない型を「不明」として黙り、E003 / E004 などの検査を素通りさせる抜け穴になる。 -/
def checkTyPath (ctx : Ctx) (span : Span) (name : List String) : R Unit := do
  let s ← get
  match s.globals.get? (renderPath name) with
  | some sym =>
    record ctx span sym
    if !sym.kind.isType then
      report ctx.file span Code.notAType s!"`{sym.name}` is a {sym.kind.describe}, not a type"
  | none =>
    match ← lookupPath name with
    | some (some sym) =>
      report ctx.file span Code.unresolved
        s!"cannot find type `{renderPath name}`: `{sym.name}` is a {sym.kind.describe} and has no member types"
    | _ =>
      report ctx.file span Code.unresolved s!"cannot find type `{renderPath name}` in this scope"

/-- 型の位置の参照。E011 と E013 を報告する。 -/
partial def checkTy (ctx : Ctx) : Ty → R Unit
  | .named span name args => do
    for a in args do checkTy ctx a
    match name with
    | [] => return
    | [head] =>
      if builtinTypes.contains head then return
      if isBuiltinHead head then
        report ctx.file span Code.notAType s!"`{head}` is not a type"
        return
      checkTyPath ctx span name
    | head :: _ =>
      if isBuiltinHead head then
        report ctx.file span Code.unresolved
          s!"cannot find type `{renderPath name}` in this scope (`{head}` has no member types)"
        return
      checkTyPath ctx span name
  | .tuple _ elems => do
    for e in elems do checkTy ctx e
  | .fn _ params ret => do
    for p in params do checkTy ctx p
    checkTy ctx ret

def Ctx.bind (ctx : Ctx) (names : List String) : Ctx :=
  { ctx with locals := names ++ ctx.locals }

mutual

partial def checkExpr (ctx : Ctx) : Expr → R Unit
  | .lit .. => return
  | .var span name => checkRef ctx span name
  | .call _ f args => do
    checkExpr ctx f
    for a in args do checkArg ctx a
  | .field _ r _ => checkExpr ctx r
  | .method span r name args => do
    checkExpr ctx r
    -- `x.f(args)` は、`f` がユーザ宣言の大域名なら `f(x, args)` の糖衣(UFCS)。phase 検査の対象。
    -- 大域名でなければ stdlib のメソッドで、型検査の段で解決する。
    if !ctx.locals.contains name then
      if let some (some _) ← lookupPath [name] then checkRef ctx span [name]
    for a in args do checkArg ctx a
  | .binop _ _ l r => do
    checkExpr ctx l
    checkExpr ctx r
  | .unop _ _ e => checkExpr ctx e
  | .ite _ c t e => do
    checkExpr ctx c
    checkExpr ctx t
    checkExpr ctx e
  | .matchE _ s arms => do
    checkExpr ctx s
    for arm in arms do checkArm ctx arm
  | .block _ stmts tail => do
    let mut c := ctx
    for st in stmts do
      match st with
      | .letS _ name ty val =>
        if let some t := ty then checkTy c t
        checkExpr c val
        c := c.bind [name]
      | .exprS e => checkExpr c e
      | .inputS span name params val =>
        -- scenario の `input f(x) = e;`: `f` は input 宣言でなければならない
        match ← lookupPath [name] with
        | none => report c.file span Code.unresolved s!"cannot find input `{name}` in this scope"
        | some none =>
          report c.file span Code.typeMismatch
            s!"`{name}` is a built-in name, not an input; only inputs (`input {name}(…) -> …`) can be given a value in a scenario"
        | some (some sym) =>
          if sym.kind != .input then
            report c.file span Code.typeMismatch
              s!"`{name}` is a {sym.kind.describe}, not an input; only inputs (`input {name}(…) -> …`) can be given a value in a scenario"
        checkExpr (c.bind (params.toList.map (·.1))) val
      | .observeS _ e => checkExpr c e
    if let some t := tail then checkExpr c t
  | .recordLit span name fields base => do
    checkRef ctx span name
    for (_, e) in fields do checkExpr ctx e
    if let some b := base then checkExpr ctx b
  | .listLit _ es => do
    for e in es do checkExpr ctx e
  | .tupleLit _ es => do
    for e in es do checkExpr ctx e
  | .lambda _ params body => do
    for p in params do
      if let some t := p.ty then checkTy ctx t
    checkExpr (ctx.bind (params.toList.map (·.name))) body
  | .quant _ _ binders body => do
    for b in binders do
      if let some t := b.ty then checkTy ctx t
    checkExpr (ctx.bind (binders.toList.map (·.name))) body

partial def checkArg (ctx : Ctx) : Arg → R Unit
  | .pos e => checkExpr ctx e
  | .named _ e => checkExpr ctx e

partial def checkArm (ctx : Ctx) : Arm → R Unit
  | .mk pat guard body => do
    let names ← checkPat ctx pat
    let c := ctx.bind names
    if let some g := guard then checkExpr c g
    checkExpr c body

/-- パターンを検査し、束縛する名前を返す。 -/
partial def checkPat (ctx : Ctx) : Pattern → R (List String)
  | .wild _ => return []
  | .bind _ n => return [n]
  | .lit .. => return []
  | .ctor span name args => do
    checkRef ctx span name
    let mut ns := []
    for a in args do ns := (← checkPat ctx a) ++ ns
    return ns
  | .tuple _ elems => do
    let mut ns := []
    for a in elems do ns := (← checkPat ctx a) ++ ns
    return ns

end

def checkDecl (m : Module) (d : Decl) : R Unit := do
  let ctx : Ctx :=
    { file := m.file, declKind := d.kind, declName := d.name,
      locals := d.params.toList.map (·.name) }
  for p in d.params do checkTy ctx p.ty
  if let some t := d.ret then checkTy ctx t
  if let some t := d.aliasOf then checkTy ctx t
  for f in d.fields do checkTy ctx f.ty
  for v in d.variants do
    for t in v.args do checkTy ctx t
  for (_, e) in d.items do checkExpr ctx e
  if let some b := d.body then checkExpr ctx b

end Resolve

/-- コンパイル単位全体の名前解決と phase 検査。診断(空なら合格)と、解決した参照の索引(出現順)を返す。 -/
def resolveAll (mods : Array Module) : Array Diagnostic × Array Resolve.Ref :=
  let run : Resolve.R Unit := do
    for m in mods do Resolve.collect m
    for m in mods do
      for d in m.decls do Resolve.checkDecl m d
  let ((), st) := run.run {}
  (st.diags, st.refs)

end Naru
