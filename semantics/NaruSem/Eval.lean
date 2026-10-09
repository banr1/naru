import NaruSem.Scope

/-!
# runtime の表示的意味論(IDEAL.md C39)

今回の保存対象の runtime の式に、Lean の関数 `eval ρ e : Option Val` で意味を与える。`ρ` は局所名 → 値の環境、`Val` は Nat / Bool の値。
`none` は「意味が定まらない」(行き詰まり: スコープ外の名前、型の合わない演算、対象外の構文、どの腕も一致しない `match`)で、
既定値・panic の値で埋めない。`Totality.lean` は、`Scope.lean` の `wtR` で適格な式と文脈に合う環境について `eval` が必ず `some` を返す
(全域性)ことを証明する。

境界の挙動は naru の言語の意味(`docs/language.md`「式」)として明示する: Nat の `-` は 0 で切り詰め(`3 - 5 = 0`)、除数 0 の `/` は 0、
除数 0 の `%` は被除数、Bool の順序は `false < true`。`==` / `!=` は値の等しさ、`implies` は `!a || b`。
この意味論は backend の出力(`Backend.Model.emitE` が書く Lean)を参照しない。
-/

namespace NaruSem
open Naru

/-- runtime の値。 -/
inductive Val where
  | nat (n : Nat)
  | bool (b : Bool)
deriving DecidableEq, Repr

def Val.ty : Val → Ty
  | .nat _ => .nat
  | .bool _ => .bool

/-- 型の担い手(量化の範囲にも使う)。 -/
def Ty.carrier : Ty → Type
  | .nat => Nat
  | .bool => Bool

def Val.of : (t : Ty) → t.carrier → Val
  | .nat, n => .nat n
  | .bool, b => .bool b

/-- 環境: 局所名 → 値(スコープ外は `none`)。 -/
abbrev Env := String → Option Val

def Env.empty : Env := fun _ => none

def Env.ext (ρ : Env) (x : String) (v : Val) : Env := fun y => if y = x then some v else ρ y

def Env.extList (ρ : Env) : List (String × Val) → Env
  | [] => ρ
  | (x, v) :: rest => (ρ.ext x v).extList rest

def Env.ofList (xs : List (String × Val)) : Env := Env.empty.extList xs

/-! ## 演算の意味 -/

/-- Nat の算術。`-` は 0 で切り詰め、`/ 0 = 0`、`% 0 = a`(Lean の `Nat` と同じ)。 -/
def ArithOp.eval : ArithOp → Nat → Nat → Nat
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b

def CmpOp.evalNat : CmpOp → Nat → Nat → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

/-- Bool の順序 `false < true`。 -/
def CmpOp.evalBool : CmpOp → Bool → Bool → Bool
  | .lt, a, b => !a && b
  | .le, a, b => !a || b
  | .gt, a, b => a && !b
  | .ge, a, b => a || !b

def EqOp.evalNat : EqOp → Nat → Nat → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

def EqOp.evalBool : EqOp → Bool → Bool → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

def LogicOp.eval : LogicOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .implies, a, b => !a || b

/-- 二項演算の値への適用。型の合わない組は `none`。 -/
def BinOp.apply : BinOp → Val → Val → Option Val
  | .arith k, .nat a, .nat b => some (.nat (k.eval a b))
  | .cmp k, .nat a, .nat b => some (.bool (k.evalNat a b))
  | .cmp k, .bool a, .bool b => some (.bool (k.evalBool a b))
  | .eq k, .nat a, .nat b => some (.bool (k.evalNat a b))
  | .eq k, .bool a, .bool b => some (.bool (k.evalBool a b))
  | .logic k, .bool a, .bool b => some (.bool (k.eval a b))
  | _, _, _ => none

def NatMethod.eval : NatMethod → Nat → Nat → Nat
  | .min, a, b => Min.min a b
  | .max, a, b => Max.max a b

/-- パターンと値の照合: 一致すれば束縛(名前, 値)の列。 -/
def matchPat : Core.Pat → Val → Option (List (String × Val))
  | .wild, _ => some []
  | .bind x, v => some [(x, v)]
  | .lit (.nat n), .nat m => if n = m then some [] else none
  | .lit (.bool b), .bool c => if b = c then some [] else none
  | _, _ => none

/-! ## 評価 -/

mutual

/-- runtime の式の意味。`none` は行き詰まり(意味が定まらない)。 -/
def eval (ρ : Env) : Core.Expr → Option Val
  | .lit (.nat n) .nat => some (.nat n)
  | .lit (.bool b) .bool => some (.bool b)
  | .var x => ρ x
  | .let_ x _ v b =>
    match eval ρ v with
    | some w => eval (ρ.ext x w) b
    | none => none
  | .ite c t e =>
    match eval ρ c with
    | some (.bool true) => eval ρ t
    | some (.bool false) => eval ρ e
    | _ => none
  | .binop op l r _ =>
    match BinOp.ofString? op, eval ρ l, eval ρ r with
    | some k, some a, some b => k.apply a b
    | _, _, _ => none
  | .unop op a =>
    if op = "!" then
      match eval ρ a with
      | some (.bool x) => some (.bool (!x))
      | _ => none
    else none
  | .method tn m r [a] _ =>
    if tn = "Nat" then
      match NatMethod.ofString? m, eval ρ r, eval ρ a with
      | some k, some (.nat x), some (.nat y) => some (.nat (k.eval x y))
      | _, _, _ => none
    else none
  | .match_ s _ arms =>
    match eval ρ s with
    | some v => evalArms ρ v arms
    | none => none
  | _ => none

/-- 腕を前から試す: パターンが一致し(ガードがあれば)ガードが真なら本体、ガードが偽なら次の腕へ(パターンの束縛は
その腕のガードと本体だけで有効で、次の腕には漏れない)。どの腕も一致しなければ `none`(既定値で埋めない)。 -/
def evalArms (ρ : Env) (v : Val) : List Core.Arm → Option Val
  | [] => none
  | .mk p g b :: rest =>
    match matchPat p v with
    | none => evalArms ρ v rest
    | some bs =>
      match g with
      | none => eval (ρ.extList bs) b
      | some g =>
        match eval (ρ.extList bs) g with
        | some (.bool true) => eval (ρ.extList bs) b
        | some (.bool false) => evalArms ρ v rest
        | _ => none

end

/-- 評価関係の形(表示的意味論から導く): `Eval ρ e v` は `eval ρ e = some v`。 -/
def Eval (ρ : Env) (e : Core.Expr) (v : Val) : Prop := eval ρ e = some v

end NaruSem
