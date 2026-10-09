import Naru.Core

/-!
# 今回の保存対象の範囲と整形性(IDEAL.md C39、用語「今回の保存対象」)

コンパイラの Typed Core IR(`compiler/Naru/Core.lean` の `Naru.Core.Expr`)のうち、コンパイラ意味論保存の限定範囲に入る構文と演算を、
backend(`Backend/Model.lean` / `Backend/Statements.lean`)から独立に定める。ここで定めるのは次の 3 つ。

- **対象範囲と型付け(runtime)**: `wtR Γ e = some t` — 局所名の文脈 `Γ`(名前 → Nat / Bool)の下で、`e` が今回の保存対象の構文だけから成り、
  正しく型付けされ、スコープ内の名前だけを参照し、`match` が網羅的であること。`none` は「保証対象でない」(対象外の構文、型の不一致、
  スコープ外の名前、網羅しない `match`)。
- **対象範囲と型付け(spec)**: `wtS Γ e = some τ` — spec 宣言の本体のための判定。文脈は名前を **値**(`.val Nat` / `.val Bool`)と
  **命題**(`.prop`)に区別し、値を要求する位置(算術・比較の被演算子、`min` / `max`、`match` の scrutinee、Nat の `let` の値)には
  命題を戻さない。論理の位置の式は Bool の値(`.val .bool`)か命題(`.prop`)で、量化・命題に束ねた局所名を含めば命題になる。
- **演算の一覧**: `BinOp.ofString?` / `NatMethod.ofString?` が文字列の演算子をこの範囲の演算に写す(写らない演算子は対象外)。

対象の constructor は `Core.Expr` の `.lit`(Nat / Bool)、`.var`、`.let_`、`.ite`、`.binop`、`.unop`(`!`)、`.method`(Nat の `min` / `max`)、
`.match_`(`Core.Arm.mk`、パターンは `Core.Pat` の `.lit` / `.bind` / `.wild`)、spec では加えて `.quant`(forall / exists、束縛型 Nat / Bool)。
演算は Nat の算術 `+` `-` `*` `/` `%` と `min` / `max`、Nat / Bool の比較 `<` `<=` `>` `>=`、値の等値 `==` `!=`、Bool の論理 `&&` `||` `!` `implies`。
これ以外(呼出し・input・record・enum・コレクション・lambda・文字列・Int …)は `none`(対象外)で、保証の対象にならない。

意味(評価)は `Eval.lean`(runtime の表示的意味論)と `Sem.lean`(spec の評価関係)が定め、`Totality.lean` が適格な式と環境について
意味が定まる(評価結果が存在して一意)ことを証明する。これらは backend の出力を参照しない(翻訳の正しさを仮定しない)。
-/

namespace NaruSem
open Naru

/-- runtime の値の型。今回の保存対象は Nat と Bool だけ。 -/
inductive Ty where
  | nat
  | bool
deriving DecidableEq, Repr

/-- Core の型表現のうち対象の型。 -/
def TyV.toTy? : TyV → Option Ty
  | .nat => some .nat
  | .bool => some .bool
  | _ => none

/-- spec の束縛文脈の型: 値(Nat / Bool)か命題。 -/
inductive STy where
  | val (t : Ty)
  | prop
deriving DecidableEq, Repr

/-! ## 対象の演算 -/

inductive ArithOp where
  | add | sub | mul | div | mod
deriving DecidableEq, Repr

inductive CmpOp where
  | lt | le | gt | ge
deriving DecidableEq, Repr

inductive EqOp where
  | eq | ne
deriving DecidableEq, Repr

inductive LogicOp where
  | and | or | implies
deriving DecidableEq, Repr

/-- 対象の二項演算。 -/
inductive BinOp where
  | arith (k : ArithOp)
  | cmp (k : CmpOp)
  | eq (k : EqOp)
  | logic (k : LogicOp)
deriving DecidableEq, Repr

/-- Core の演算子の文字列 → 対象の二項演算。写らない演算子は対象外。 -/
def BinOp.ofString? : String → Option BinOp
  | "+" => some (.arith .add)
  | "-" => some (.arith .sub)
  | "*" => some (.arith .mul)
  | "/" => some (.arith .div)
  | "%" => some (.arith .mod)
  | "<" => some (.cmp .lt)
  | "<=" => some (.cmp .le)
  | ">" => some (.cmp .gt)
  | ">=" => some (.cmp .ge)
  | "==" => some (.eq .eq)
  | "!=" => some (.eq .ne)
  | "&&" => some (.logic .and)
  | "||" => some (.logic .or)
  | "implies" => some (.logic .implies)
  | _ => none

/-- 対象の Nat のメソッド。 -/
inductive NatMethod where
  | min | max
deriving DecidableEq, Repr

def NatMethod.ofString? : String → Option NatMethod
  | "min" => some .min
  | "max" => some .max
  | _ => none

/-- 二項演算の型付け: 被演算子の型 `tl` / `tr` と Core の注釈 `ta`(被演算子の型)から結果の型。 -/
def BinOp.result : BinOp → Ty → Ty → Ty → Option Ty
  | .arith _, .nat, .nat, .nat => some .nat
  | .cmp _, .nat, .nat, .nat => some .bool
  | .cmp _, .bool, .bool, .bool => some .bool
  | .eq _, .nat, .nat, .nat => some .bool
  | .eq _, .bool, .bool, .bool => some .bool
  | .logic _, .bool, .bool, .bool => some .bool
  | _, _, _, _ => none

/-! ## 文脈 -/

/-- runtime の束縛文脈: 局所名 → 型(スコープ外は `none`)。 -/
abbrev Ctx := String → Option Ty

def Ctx.empty : Ctx := fun _ => none

/-- 束縛(同名の外側の束縛を隠す)。 -/
def Ctx.ext (Γ : Ctx) (x : String) (t : Ty) : Ctx := fun y => if y = x then some t else Γ y

def Ctx.extList (Γ : Ctx) : List (String × Ty) → Ctx
  | [] => Γ
  | (x, t) :: rest => (Γ.ext x t).extList rest

/-- 仮引数の並びから文脈を作る(後ろが前を隠す)。 -/
def Ctx.ofList (xs : List (String × Ty)) : Ctx := Ctx.empty.extList xs

/-- spec の束縛文脈: 局所名 → 値の型か命題。 -/
abbrev SCtx := String → Option STy

def SCtx.empty : SCtx := fun _ => none

def SCtx.ext (Γ : SCtx) (x : String) (t : STy) : SCtx := fun y => if y = x then some t else Γ y

def SCtx.extList (Γ : SCtx) : List (String × STy) → SCtx
  | [] => Γ
  | (x, t) :: rest => (Γ.ext x t).extList rest

def SCtx.ofList (xs : List (String × STy)) : SCtx := SCtx.empty.extList xs

/-- パターンの束縛(値)を足す。 -/
def SCtx.extVals (Γ : SCtx) (bs : List (String × Ty)) : SCtx :=
  Γ.extList (bs.map fun (x, t) => (x, STy.val t))

/-- 値の位置から見た文脈: 命題に束ねた名前はスコープ外(値を要求する位置に命題を戻さない)。 -/
def SCtx.vals (Γ : SCtx) : Ctx := fun x =>
  match Γ x with
  | some (.val t) => some t
  | _ => none

/-- パターンの束縛を文脈に足す(束縛はパターンの腕のガードと本体だけで有効)。 -/
def Ctx.extPat (Γ : Ctx) (bs : List (String × Ty)) : Ctx := Γ.extList bs

/-! ## パターン -/

/-- 対象のパターン(`_` / 変数 / Nat・Bool のリテラル)の型付け: scrutinee の型 `t` に対して、束縛する名前と型。 -/
def wtPat (t : Ty) : Core.Pat → Option (List (String × Ty))
  | .wild => some []
  | .bind x => some [(x, t)]
  | .lit (.nat _) => if t = .nat then some [] else none
  | .lit (.bool _) => if t = .bool then some [] else none
  | _ => none

/-- 必ず一致するパターン。 -/
def irrefutable : Core.Pat → Bool
  | .wild | .bind _ => true
  | _ => false

/-- `match` の網羅性。腕を前から見て、ガードの無い必ず一致する腕(`_` / 変数)に達すれば網羅的。Bool の scrutinee では、
ガードの無いリテラルの腕 `true` と `false` の両方に達しても網羅的(`sawT` / `sawF` はそれまでに見たリテラル)。
Nat のリテラルは全体を覆えない。ガードのある腕は(偽になりうるので)数えない。 -/
def exhaustiveFrom (t : Ty) (sawT sawF : Bool) : List Core.Arm → Bool
  | [] => false
  | .mk p none _ :: rest =>
    match p with
    | .wild | .bind _ => true
    | .lit (.bool true) => (t = .bool && sawF) || exhaustiveFrom t true sawF rest
    | .lit (.bool false) => (t = .bool && sawT) || exhaustiveFrom t sawT true rest
    | _ => exhaustiveFrom t sawT sawF rest
  | .mk _ (some _) _ :: rest => exhaustiveFrom t sawT sawF rest

def exhaustive (t : Ty) (arms : List Core.Arm) : Bool := exhaustiveFrom t false false arms

/-! ## runtime の型付けと対象範囲 -/

mutual

/-- runtime の式の型付け(対象範囲の判定を兼ねる)。`some t` なら対象の構文だけから成り、`Γ` の下で型 `t` を持つ。 -/
def wtR (Γ : Ctx) : Core.Expr → Option Ty
  | .lit (.nat _) .nat => some .nat
  | .lit (.bool _) .bool => some .bool
  | .var x => Γ x
  | .let_ x ty v b =>
    match wtR Γ v, TyV.toTy? ty with
    | some tv, some ta => if tv = ta then wtR (Γ.ext x tv) b else none
    | _, _ => none
  | .ite c t e =>
    match wtR Γ c, wtR Γ t, wtR Γ e with
    | some .bool, some tt, some te => if tt = te then some tt else none
    | _, _, _ => none
  | .binop op l r ty =>
    match BinOp.ofString? op, wtR Γ l, wtR Γ r, TyV.toTy? ty with
    | some k, some tl, some tr, some ta => k.result tl tr ta
    | _, _, _, _ => none
  | .unop op a =>
    if op = "!" then
      match wtR Γ a with
      | some .bool => some .bool
      | _ => none
    else none
  | .method tn m r [a] rt =>
    if tn = "Nat" then
      match NatMethod.ofString? m, wtR Γ r, wtR Γ a, rt with
      | some _, some .nat, some .nat, .nat => some .nat
      | _, _, _, _ => none
    else none
  | .match_ s st arms =>
    match wtR Γ s, TyV.toTy? st with
    | some ts, some ta => if ts = ta && exhaustive ts arms then wtArmsR Γ ts arms else none
    | _, _ => none
  | _ => none

/-- `match` の腕の型付け: 各腕のパターンが scrutinee の型 `ts` に合い、ガードは Bool、本体の型がすべて同じ。腕が無ければ `none`。 -/
def wtArmsR (Γ : Ctx) (ts : Ty) : List Core.Arm → Option Ty
  | [] => none
  | arm :: rest =>
    match wtArmR Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsR Γ ts rest with
      | some t2 => if t1 = t2 then some t1 else none
      | none => none

/-- 1 つの腕: パターンが scrutinee の型に合い、束縛を足した文脈でガードは Bool、結果は本体の型。 -/
def wtArmR (Γ : Ctx) (ts : Ty) : Core.Arm → Option Ty
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none => wtR (Γ.extPat bs) b
      | some g =>
        match wtR (Γ.extPat bs) g with
        | some .bool => wtR (Γ.extPat bs) b
        | _ => none

end

/-! ## spec の型付けと対象範囲 -/

/-- 論理の位置の 2 つの型の結び: どちらも Bool の値なら Bool の値、どちらかが命題なら命題。値の Nat は論理の位置に置けない。 -/
def STy.join : STy → STy → Option STy
  | .val .bool, .val .bool => some (.val .bool)
  | .val .bool, .prop => some .prop
  | .prop, .val .bool => some .prop
  | .prop, .prop => some .prop
  | _, _ => none

/-- 論理の位置に置ける型か(Bool の値か命題)。 -/
def STy.isForm : STy → Bool
  | .val .bool => true
  | .prop => true
  | .val .nat => false

/-- 量化の束縛を文脈に足す。束縛型が Nat / Bool でなければ `none`。 -/
def SCtx.extBinders (Γ : SCtx) : List (String × TyV) → Option SCtx
  | [] => some Γ
  | (x, tv) :: rest =>
    match TyV.toTy? tv with
    | some t => (Γ.ext x (.val t)).extBinders rest
    | none => none

mutual

/-- spec の式が命題でしか表せないか(量化、命題に束ねた局所名を含む)。コンパイラ(`Typecheck.proppy` / Statements backend の `proppy`)と
同じ構文的な区分で、Bool の `let` の値がこれなら名前は命題に束ね、そうでなければ Bool の値に束ねる。 -/
def proppyS (Γ : SCtx) : Core.Expr → Bool
  | .quant .. => true
  | .var x => match Γ x with | some .prop => true | _ => false
  | .let_ x _ v b =>
    -- 値が命題なら全体が命題。そうでなければ名前は値に束なるので、本体の中では同名の命題の局所名を隠す
    proppyS Γ v || proppyS (Γ.ext x (.val .nat)) b
  | .ite c t e => proppyS Γ c || proppyS Γ t || proppyS Γ e
  | .binop _ l r _ => proppyS Γ l || proppyS Γ r
  | .unop _ a => proppyS Γ a
  | .match_ s _ arms => proppyS Γ s || proppyArms Γ arms
  | .method _ _ r [a] _ => proppyS Γ r || proppyS Γ a
  | _ => false

/-- 腕の中では、パターンの束縛(値)が同名の命題の局所名を隠す。 -/
def proppyArms (Γ : SCtx) : List Core.Arm → Bool
  | [] => false
  | .mk p g b :: rest =>
    let Γ' := match p with
      | .bind x => Γ.ext x (.val .nat)
      | _ => Γ
    (match g with | some g => proppyS Γ' g | none => false) || proppyS Γ' b || proppyArms Γ rest

end

mutual

/-- spec の式の型付け(対象範囲の判定を兼ねる)。`some (.val t)` なら Bool / Nat の値、`some .prop` なら命題。
値を要求する位置(算術・比較・等値(Nat)・`min` / `max` の被演算子、`match` の scrutinee、Nat の `let` の値)は `wtR Γ.vals`
(命題に束ねた名前はスコープ外)で判定し、命題を戻さない。 -/
def wtS (Γ : SCtx) : Core.Expr → Option STy
  | .lit (.nat _) .nat => some (.val .nat)
  | .lit (.bool _) .bool => some (.val .bool)
  | .var x => Γ x
  | .let_ x ty v b =>
    match TyV.toTy? ty with
    | some .nat =>
      match wtR Γ.vals v with
      | some .nat => wtS (Γ.ext x (.val .nat)) b
      | _ => none
    | some .bool =>
      if proppyS Γ v then
        match wtS Γ v with
        | some .prop => wtS (Γ.ext x .prop) b
        | _ => none
      else
        match wtR Γ.vals v with
        | some .bool => wtS (Γ.ext x (.val .bool)) b
        | _ => none
    | none => none
  | .ite c t e =>
    match wtS Γ c, wtS Γ t, wtS Γ e with
    | some tc, some tt, some te =>
      match tc.join tt with
      | some j => j.join te
      | none => none
    | _, _, _ => none
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.logic _), some .bool =>
      match wtS Γ l, wtS Γ r with
      | some tl, some tr => tl.join tr
      | _, _ => none
    | some (.eq _), some .bool =>
      match wtS Γ l, wtS Γ r with
      | some tl, some tr => tl.join tr
      | _, _ => none
    | some (.eq _), some .nat =>
      match wtR Γ.vals l, wtR Γ.vals r with
      | some .nat, some .nat => some (.val .bool)
      | _, _ => none
    | some (.cmp _), some ta =>
      match wtR Γ.vals l, wtR Γ.vals r with
      | some tl, some tr => if tl = ta && tr = ta then some (.val .bool) else none
      | _, _ => none
    | some (.arith _), some .nat =>
      match wtR Γ.vals l, wtR Γ.vals r with
      | some .nat, some .nat => some (.val .nat)
      | _, _ => none
    | _, _ => none
  | .unop op a =>
    if op = "!" then
      match wtS Γ a with
      | some t => if t.isForm then some t else none
      | none => none
    else none
  | .method tn m r [a] rt =>
    if tn = "Nat" then
      match NatMethod.ofString? m, wtR Γ.vals r, wtR Γ.vals a, rt with
      | some _, some .nat, some .nat, .nat => some (.val .nat)
      | _, _, _, _ => none
    else none
  | .match_ s st arms =>
    match wtR Γ.vals s, TyV.toTy? st with
    | some ts, some ta => if ts = ta && exhaustive ts arms then wtArmsS Γ ts arms else none
    | _, _ => none
  | .quant _ bs b =>
    match bs with
    | [] => none
    | _ =>
      match Γ.extBinders bs with
      | some Γ' =>
        match wtS Γ' b with
        | some t => if t.isForm then some .prop else none
        | none => none
      | none => none
  | _ => none

/-- `match` の腕(spec): パターンの束縛は値、ガードと本体は論理の位置。結果は全腕の結び。 -/
def wtArmsS (Γ : SCtx) (ts : Ty) : List Core.Arm → Option STy
  | [] => none
  | arm :: rest =>
    match wtArmS Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsS Γ ts rest with
      | some t2 => t1.join t2
      | none => none

/-- 1 つの腕: パターンの束縛は値、束縛を足した文脈でガードと本体は論理の位置で、結果はその結び。 -/
def wtArmS (Γ : SCtx) (ts : Ty) : Core.Arm → Option STy
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none =>
        match wtS (Γ.extVals bs) b with
        | some t => if t.isForm then some t else none
        | none => none
      | some g =>
        match wtS (Γ.extVals bs) g, wtS (Γ.extVals bs) b with
        | some tg, some tb => tg.join tb
        | _, _ => none

end

end NaruSem
