import NaruSem.Eval

/-!
# spec の評価関係(IDEAL.md C39)

今回の保存対象の spec の式(spec 宣言の本体: 論理の位置の式)に、Lean の帰納的な関係 `Sem ρ e P` で意味を与える。
`ρ` は局所名 → **値**(`.val`)か**命題**(`.prop`)の環境、`P : Prop` がその式の意味(命題)。
runtime の Nat / Bool 値と spec の命題は環境と意味の両方で区別し、値を要求する位置(算術・比較・Nat の等値の被演算子、
`match` の scrutinee、Nat の `let` の値)は runtime の表示的意味論 `eval`(`Eval.lean`)を `ρ.vals`(命題に束ねた名前はスコープ外)で
評価した値を使う。命題を実行可能な Bool に戻す規則は無い。

関係にしたのは量化のため: `forall n: Nat { … }` の意味は `∀ n, F n` で、`F n` は本体の意味。本体に意味が定まらない場合を
`False` / `True` で埋めず、規則が無い(導出できない)ことで「意味が定まらない」を表す。`Totality.lean` は、`Scope.lean` の `wtS` で
適格な式と環境について意味が存在し(`Sem_exists`)、意味は一意である(`Sem_unique`)ことを証明する。

導出は決定的: 各構文につき規則は 1 つか、互いに排他的な前提(演算子、`let` の値が命題か、パターンの一致、ガードの有無)で分かれる。
`match` は腕を前から 1 つずつ剥がす(`matchSkip` / `matchHit` / `matchGuard`): ガード付きの腕 `p if g => b` の意味は
`(G → B) ∧ (¬ G → R)`(R = 残りの腕の意味)で、パターンの束縛 `bs` はその腕のガードと本体(`ρ.extVals bs`)だけで有効で、
R は外側の環境 `ρ` で解釈する(束縛は他の腕へ漏れない)。
この意味論は backend の出力(`Backend.Statements.emitProp` が書く Lean)を参照しない。
-/

namespace NaruSem
open Naru

/-- spec の環境の束縛: 値か命題。 -/
inductive SVal where
  | val (v : Val)
  | prop (P : Prop)

def SVal.ty : SVal → STy
  | .val v => .val v.ty
  | .prop _ => .prop

abbrev SEnv := String → Option SVal

def SEnv.empty : SEnv := fun _ => none

def SEnv.ext (ρ : SEnv) (x : String) (s : SVal) : SEnv := fun y => if y = x then some s else ρ y

def SEnv.extList (ρ : SEnv) : List (String × SVal) → SEnv
  | [] => ρ
  | (x, s) :: rest => (ρ.ext x s).extList rest

def SEnv.ofList (xs : List (String × SVal)) : SEnv := SEnv.empty.extList xs

/-- パターンの束縛(値)を足す。 -/
def SEnv.extVals (ρ : SEnv) (bs : List (String × Val)) : SEnv :=
  ρ.extList (bs.map fun (x, v) => (x, SVal.val v))

/-- 値の位置から見た環境: 命題に束ねた名前はスコープ外。 -/
def SEnv.vals (ρ : SEnv) : Env := fun x =>
  match ρ x with
  | some (.val v) => some v
  | _ => none

/-- 環境に対応する束縛文脈(名前 → 値の型か命題)。 -/
def SEnv.ctx (ρ : SEnv) : SCtx := fun x => (ρ x).map SVal.ty

/-! ## 演算の命題 -/

def CmpOp.propNat : CmpOp → Nat → Nat → Prop
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

def EqOp.propNat : EqOp → Nat → Nat → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b

/-- 論理の位置の `==` / `!=`: 命題の同値とその否定。 -/
def EqOp.propIff : EqOp → Prop → Prop → Prop
  | .eq, P, Q => P ↔ Q
  | .ne, P, Q => ¬ (P ↔ Q)

def LogicOp.prop : LogicOp → Prop → Prop → Prop
  | .and, P, Q => P ∧ Q
  | .or, P, Q => P ∨ Q
  | .implies, P, Q => P → Q

/-! ## 評価関係 -/

/-- spec の式の意味。`Sem ρ e P`: 環境 `ρ` の下で論理の位置の式 `e` の意味は命題 `P`。 -/
inductive Sem : SEnv → Core.Expr → Prop → Prop where
  /-- Bool のリテラルは「true である」という命題。 -/
  | lit {ρ : SEnv} {b : Bool} : Sem ρ (.lit (.bool b) .bool) (b = true)
  /-- Bool の値に束ねた名前は「true である」という命題。 -/
  | varVal {ρ : SEnv} {x : String} {b : Bool} (h : ρ x = some (.val (.bool b))) : Sem ρ (.var x) (b = true)
  /-- 命題に束ねた名前はその命題。 -/
  | varProp {ρ : SEnv} {x : String} {P : Prop} (h : ρ x = some (.prop P)) : Sem ρ (.var x) P
  /-- `&&` / `||` / `implies`。 -/
  | logic {ρ : SEnv} {op : String} {k : LogicOp} {l r : Core.Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.logic k)) (hl : Sem ρ l P) (hr : Sem ρ r Q) :
      Sem ρ (.binop op l r .bool) (k.prop P Q)
  /-- Nat の `==` / `!=`: 値の等しさ。 -/
  | eqNat {ρ : SEnv} {op : String} {k : EqOp} {l r : Core.Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : eval ρ.vals l = some (.nat a)) (hr : eval ρ.vals r = some (.nat b)) :
      Sem ρ (.binop op l r .nat) (k.propNat a b)
  /-- 論理の位置の Bool の `==` / `!=`: 両辺の命題の同値とその否定。 -/
  | eqForm {ρ : SEnv} {op : String} {k : EqOp} {l r : Core.Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : Sem ρ l P) (hr : Sem ρ r Q) :
      Sem ρ (.binop op l r .bool) (k.propIff P Q)
  /-- Nat の比較。 -/
  | cmpNat {ρ : SEnv} {op : String} {k : CmpOp} {l r : Core.Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval ρ.vals l = some (.nat a)) (hr : eval ρ.vals r = some (.nat b)) :
      Sem ρ (.binop op l r .nat) (k.propNat a b)
  /-- Bool の比較(`false < true`)。被演算子は値。 -/
  | cmpBool {ρ : SEnv} {op : String} {k : CmpOp} {l r : Core.Expr} {a b : Bool}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval ρ.vals l = some (.bool a)) (hr : eval ρ.vals r = some (.bool b)) :
      Sem ρ (.binop op l r .bool) (k.evalBool a b = true)
  /-- `!`。 -/
  | not {ρ : SEnv} {a : Core.Expr} {P : Prop} (h : Sem ρ a P) : Sem ρ (.unop "!" a) (¬ P)
  /-- `if c { t } else { e }`: `(C → T) ∧ (¬ C → E)`。 -/
  | ite {ρ : SEnv} {c t e : Core.Expr} {C P Q : Prop} (hc : Sem ρ c C) (ht : Sem ρ t P) (he : Sem ρ e Q) :
      Sem ρ (.ite c t e) ((C → P) ∧ (¬ C → Q))
  /-- Nat の `let`: 値に束ねる。 -/
  | letNat {ρ : SEnv} {x : String} {v b : Core.Expr} {n : Nat} {Q : Prop}
      (hv : eval ρ.vals v = some (.nat n)) (hb : Sem (ρ.ext x (.val (.nat n))) b Q) :
      Sem ρ (.let_ x .nat v b) Q
  /-- Bool の `let`、値が命題でなければ(`proppyS`)Bool の値に束ねる。 -/
  | letBoolVal {ρ : SEnv} {x : String} {v b : Core.Expr} {w : Bool} {Q : Prop}
      (hp : proppyS ρ.ctx v = false) (hv : eval ρ.vals v = some (.bool w)) (hb : Sem (ρ.ext x (.val (.bool w))) b Q) :
      Sem ρ (.let_ x .bool v b) Q
  /-- Bool の `let`、値が命題なら命題に束ねる(以後その名前は命題)。 -/
  | letProp {ρ : SEnv} {x : String} {v b : Core.Expr} {P Q : Prop}
      (hp : proppyS ρ.ctx v = true) (hv : Sem ρ v P) (hb : Sem (ρ.ext x (.prop P)) b Q) :
      Sem ρ (.let_ x .bool v b) Q
  /-- `match`: 先頭の腕のパターンが一致しなければ残りの腕へ。 -/
  | matchSkip {ρ : SEnv} {s : Core.Expr} {st : TyV} {p : Core.Pat} {g : Option Core.Expr} {b : Core.Expr} {rest : List Core.Arm}
      {v : Val} {P : Prop}
      (hs : eval ρ.vals s = some v) (hp : matchPat p v = none) (hr : Sem ρ (.match_ s st rest) P) :
      Sem ρ (.match_ s st (.mk p g b :: rest)) P
  /-- `match`: ガード無しの腕が一致すれば、その本体(束縛の下)。 -/
  | matchHit {ρ : SEnv} {s : Core.Expr} {st : TyV} {p : Core.Pat} {b : Core.Expr} {rest : List Core.Arm}
      {v : Val} {bs : List (String × Val)} {P : Prop}
      (hs : eval ρ.vals s = some v) (hp : matchPat p v = some bs) (hb : Sem (ρ.extVals bs) b P) :
      Sem ρ (.match_ s st (.mk p none b :: rest)) P
  /-- `match`: ガード付きの腕が一致すれば `(G → B) ∧ (¬ G → R)`。束縛はガードと本体だけで有効で、残りの腕 R は外側の環境。 -/
  | matchGuard {ρ : SEnv} {s : Core.Expr} {st : TyV} {p : Core.Pat} {g b : Core.Expr} {rest : List Core.Arm}
      {v : Val} {bs : List (String × Val)} {G P R : Prop}
      (hs : eval ρ.vals s = some v) (hp : matchPat p v = some bs) (hg : Sem (ρ.extVals bs) g G)
      (hb : Sem (ρ.extVals bs) b P) (hr : Sem ρ (.match_ s st rest) R) :
      Sem ρ (.match_ s st (.mk p (some g) b :: rest)) ((G → P) ∧ (¬ G → R))
  /-- 量化の束縛を使い切ったら本体。 -/
  | quantNil {ρ : SEnv} {q : Quant} {b : Core.Expr} {P : Prop} (h : Sem ρ b P) : Sem ρ (.quant q [] b) P
  /-- `forall x: T { … }`: `T`(Nat / Bool)の全要素について。 -/
  | forallCons {ρ : SEnv} {x : String} {tv : TyV} {t : Ty} {bs : List (String × TyV)} {b : Core.Expr} {F : t.carrier → Prop}
      (ht : TyV.toTy? tv = some t)
      (h : ∀ a : t.carrier, Sem (ρ.ext x (.val (Val.of t a))) (.quant .forall_ bs b) (F a)) :
      Sem ρ (.quant .forall_ ((x, tv) :: bs) b) (∀ a, F a)
  /-- `exists x: T { … }`。 -/
  | existsCons {ρ : SEnv} {x : String} {tv : TyV} {t : Ty} {bs : List (String × TyV)} {b : Core.Expr} {F : t.carrier → Prop}
      (ht : TyV.toTy? tv = some t)
      (h : ∀ a : t.carrier, Sem (ρ.ext x (.val (Val.of t a))) (.quant .exists_ bs b) (F a)) :
      Sem ρ (.quant .exists_ ((x, tv) :: bs) b) (∃ a, F a)

end NaruSem
