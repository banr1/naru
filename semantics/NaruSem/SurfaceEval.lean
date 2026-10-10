import NaruSem.Surface
import NaruSem.Sem

/-!
# Surface AST の意味(IDEAL.md C48)

`Surface.lean` の対象の式に、Core の意味論(`Eval.lean` / `Sem.lean`)とは独立に意味を与える。環境・値・演算の意味は Core の意味論と同じ
Lean の定義(`Val` / `Env` / `SEnv`、`ArithOp.eval` / `CmpOp.propNat` …)を共有する — それらは naru の言語の意味(`docs/language.md`「式」)であって、
frontend の変換(Core)や backend の出力ではない。AST の構文(ブロックの `let` の列と末尾式、注釈の無い `==`、位置引数のメソッド)に対する
規則はここで独立に定める。

- runtime: 表示的意味論 `eval ρ e : Option Val`。`none` は行き詰まり(スコープ外の名前、型の合わない演算、対象外の構文、どの腕も一致しない
  `match`)で、既定値・panic の値で埋めない。ブロックは `let` を前から評価して環境を伸ばし(`evalStmts`)、末尾式を評価する。
- spec: 評価関係 `Sem ρ e P`(`ρ : SEnv` = 名前 → 値か命題、`P : Prop`)。Core の `Sem` と同じ読み方(Bool の値は「true である」という命題、
  論理は `∧ ∨ → ¬`、Nat の比較・等値は `< = ≠` …、`if` は `(C → P) ∧ (¬ C → Q)`、`match` は腕を 1 つずつ剥がし、量化は型の全要素)で、
  ブロックの `let` は値が命題(`proppyS`)なら名前を命題に、そうでなければ値に束ねる。注釈の無い `==` / `!=` は、両辺が Nat の値なら値の等しさ
  (`eqNat`)、そうでなければ両辺の命題の同値とその否定(`eqForm`)。この 2 つの規則が重ならない(論理の位置の式は Nat の値に評価されない)
  ことは `SurfaceTotality.lean` の `Sem_not_nat` が証明し、意味の一意性に使う。命題を実行可能な Bool に戻す規則は無い。
-/

namespace NaruSem.Surf
open Naru

/-- パターンと値の照合: 一致すれば束縛(名前, 値)の列。 -/
def matchPat : Pat → Val → Option (List (String × Val))
  | .wild _, _ => some []
  | .bind _ x, v => some [(x, v)]
  | .lit _ (.nat n), .nat m => if n = m then some [] else none
  | .lit _ (.bool b), .bool c => if b = c then some [] else none
  | _, _ => none

/-! ## runtime の評価 -/

mutual

/-- runtime の式の意味。`none` は行き詰まり(意味が定まらない)。 -/
def eval (ρ : Env) : Expr → Option Val
  | .lit _ (.nat n) => some (.nat n)
  | .lit _ (.bool b) => some (.bool b)
  | .var _ [x] => ρ x
  | .binop _ op l r =>
    match BinOp.ofString? op, eval ρ l, eval ρ r with
    | some k, some a, some b => k.apply a b
    | _, _, _ => none
  | .unop _ op a =>
    if op = "!" then
      match eval ρ a with
      | some (.bool x) => some (.bool (!x))
      | _ => none
    else none
  | .method _ r m [a] =>
    match NatMethod.ofString? m, eval ρ r, eval ρ a with
    | some k, some (.nat x), some (.nat y) => some (.nat (k.eval x y))
    | _, _, _ => none
  | .ite _ c t e =>
    match eval ρ c with
    | some (.bool true) => eval ρ t
    | some (.bool false) => eval ρ e
    | _ => none
  | .matchE _ s arms =>
    match eval ρ s with
    | some v => evalArms ρ v arms
    | none => none
  | .block _ stmts (some e) =>
    match evalStmts ρ stmts with
    | some ρ' => eval ρ' e
    | none => none
  | _ => none

/-- ブロックの `let` の列: 前から値を評価して環境を伸ばす。 -/
def evalStmts (ρ : Env) : List Stmt → Option Env
  | [] => some ρ
  | .letS _ x _ v :: rest =>
    match eval ρ v with
    | some w => evalStmts (ρ.ext x w) rest
    | none => none

/-- 腕を前から試す: パターンが一致し(ガードがあれば)ガードが真なら本体、ガードが偽なら次の腕へ(パターンの束縛はその腕のガードと本体だけで
有効で、次の腕には漏れない)。どの腕も一致しなければ `none`。 -/
def evalArms (ρ : Env) (v : Val) : List Arm → Option Val
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

/-- 評価関係の形: `Eval ρ e v` は `eval ρ e = some v`。 -/
def Eval (ρ : Env) (e : Expr) (v : Val) : Prop := eval ρ e = some v

/-! ## spec の評価関係 -/

/-- spec の式の意味。`Sem ρ e P`: 環境 `ρ` の下で論理の位置の式 `e` の意味は命題 `P`。 -/
inductive Sem : SEnv → Expr → Prop → Prop where
  /-- Bool のリテラルは「true である」という命題。 -/
  | lit {ρ : SEnv} {sp : Span} {b : Bool} : Sem ρ (.lit sp (.bool b)) (b = true)
  /-- Bool の値に束ねた名前は「true である」という命題。 -/
  | varVal {ρ : SEnv} {sp : Span} {x : String} {b : Bool} (h : ρ x = some (.val (.bool b))) : Sem ρ (.var sp [x]) (b = true)
  /-- 命題に束ねた名前はその命題。 -/
  | varProp {ρ : SEnv} {sp : Span} {x : String} {P : Prop} (h : ρ x = some (.prop P)) : Sem ρ (.var sp [x]) P
  /-- `&&` / `||` / `implies`。 -/
  | logic {ρ : SEnv} {sp : Span} {op : String} {k : LogicOp} {l r : Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.logic k)) (hl : Sem ρ l P) (hr : Sem ρ r Q) :
      Sem ρ (.binop sp op l r) (k.prop P Q)
  /-- `==` / `!=`、両辺が Nat の値: 値の等しさ。 -/
  | eqNat {ρ : SEnv} {sp : Span} {op : String} {k : EqOp} {l r : Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : eval ρ.vals l = some (.nat a)) (hr : eval ρ.vals r = some (.nat b)) :
      Sem ρ (.binop sp op l r) (k.propNat a b)
  /-- `==` / `!=`、両辺が論理の位置の式(Bool の値か命題): 両辺の命題の同値とその否定。 -/
  | eqForm {ρ : SEnv} {sp : Span} {op : String} {k : EqOp} {l r : Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : Sem ρ l P) (hr : Sem ρ r Q) :
      Sem ρ (.binop sp op l r) (k.propIff P Q)
  /-- Nat の比較。 -/
  | cmpNat {ρ : SEnv} {sp : Span} {op : String} {k : CmpOp} {l r : Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval ρ.vals l = some (.nat a)) (hr : eval ρ.vals r = some (.nat b)) :
      Sem ρ (.binop sp op l r) (k.propNat a b)
  /-- Bool の比較(`false < true`)。被演算子は値。 -/
  | cmpBool {ρ : SEnv} {sp : Span} {op : String} {k : CmpOp} {l r : Expr} {a b : Bool}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval ρ.vals l = some (.bool a)) (hr : eval ρ.vals r = some (.bool b)) :
      Sem ρ (.binop sp op l r) (k.evalBool a b = true)
  /-- `!`。 -/
  | not {ρ : SEnv} {sp : Span} {a : Expr} {P : Prop} (h : Sem ρ a P) : Sem ρ (.unop sp "!" a) (¬ P)
  /-- `if c { t } else { e }`: `(C → T) ∧ (¬ C → E)`。 -/
  | ite {ρ : SEnv} {sp : Span} {c t e : Expr} {C P Q : Prop} (hc : Sem ρ c C) (ht : Sem ρ t P) (he : Sem ρ e Q) :
      Sem ρ (.ite sp c t e) ((C → P) ∧ (¬ C → Q))
  /-- ブロックの末尾式。 -/
  | blockTail {ρ : SEnv} {sp : Span} {e : Expr} {P : Prop} (h : Sem ρ e P) : Sem ρ (.block sp [] (some e)) P
  /-- ブロックの `let`、値が命題でなければ(`proppyS`)値に束ねる。 -/
  | blockLetVal {ρ : SEnv} {sp lsp : Span} {x : String} {ty : Option Ty} {v : Expr} {rest : List Stmt} {tail : Option Expr}
      {w : Val} {Q : Prop}
      (hp : proppyS ρ.ctx v = false) (hv : eval ρ.vals v = some w) (hb : Sem (ρ.ext x (.val w)) (.block sp rest tail) Q) :
      Sem ρ (.block sp (.letS lsp x ty v :: rest) tail) Q
  /-- ブロックの `let`、値が命題なら命題に束ねる(以後その名前は命題)。 -/
  | blockLetProp {ρ : SEnv} {sp lsp : Span} {x : String} {ty : Option Ty} {v : Expr} {rest : List Stmt} {tail : Option Expr}
      {P Q : Prop}
      (hp : proppyS ρ.ctx v = true) (hv : Sem ρ v P) (hb : Sem (ρ.ext x (.prop P)) (.block sp rest tail) Q) :
      Sem ρ (.block sp (.letS lsp x ty v :: rest) tail) Q
  /-- `match`: 先頭の腕のパターンが一致しなければ残りの腕へ。 -/
  | matchSkip {ρ : SEnv} {sp : Span} {s : Expr} {p : Pat} {g : Option Expr} {b : Expr} {rest : List Arm} {v : Val} {P : Prop}
      (hs : eval ρ.vals s = some v) (hp : matchPat p v = none) (hr : Sem ρ (.matchE sp s rest) P) :
      Sem ρ (.matchE sp s (.mk p g b :: rest)) P
  /-- `match`: ガード無しの腕が一致すれば、その本体(束縛の下)。 -/
  | matchHit {ρ : SEnv} {sp : Span} {s : Expr} {p : Pat} {b : Expr} {rest : List Arm} {v : Val} {bs : List (String × Val)} {P : Prop}
      (hs : eval ρ.vals s = some v) (hp : matchPat p v = some bs) (hb : Sem (ρ.extVals bs) b P) :
      Sem ρ (.matchE sp s (.mk p none b :: rest)) P
  /-- `match`: ガード付きの腕が一致すれば `(G → B) ∧ (¬ G → R)`。束縛はガードと本体だけで有効で、残りの腕 R は外側の環境。 -/
  | matchGuard {ρ : SEnv} {sp : Span} {s : Expr} {p : Pat} {g b : Expr} {rest : List Arm} {v : Val} {bs : List (String × Val)}
      {G P R : Prop}
      (hs : eval ρ.vals s = some v) (hp : matchPat p v = some bs) (hg : Sem (ρ.extVals bs) g G)
      (hb : Sem (ρ.extVals bs) b P) (hr : Sem ρ (.matchE sp s rest) R) :
      Sem ρ (.matchE sp s (.mk p (some g) b :: rest)) ((G → P) ∧ (¬ G → R))
  /-- 量化の束縛を使い切ったら本体。 -/
  | quantNil {ρ : SEnv} {sp : Span} {q : Quant} {b : Expr} {P : Prop} (h : Sem ρ b P) : Sem ρ (.quant sp q [] b) P
  /-- `forall x: T { … }`: `T`(Nat / Bool)の全要素について。 -/
  | forallCons {ρ : SEnv} {sp bsp : Span} {x : String} {ty : Ty} {t : NaruSem.Ty} {bs : List Binder} {b : Expr} {F : t.carrier → Prop}
      (ht : ty.toTy? = some t)
      (h : ∀ a : t.carrier, Sem (ρ.ext x (.val (Val.of t a))) (.quant sp .forall_ bs b) (F a)) :
      Sem ρ (.quant sp .forall_ ({ name := x, ty := some ty, span := bsp } :: bs) b) (∀ a, F a)
  /-- `exists x: T { … }`。 -/
  | existsCons {ρ : SEnv} {sp bsp : Span} {x : String} {ty : Ty} {t : NaruSem.Ty} {bs : List Binder} {b : Expr} {F : t.carrier → Prop}
      (ht : ty.toTy? = some t)
      (h : ∀ a : t.carrier, Sem (ρ.ext x (.val (Val.of t a))) (.quant sp .exists_ bs b) (F a)) :
      Sem ρ (.quant sp .exists_ ({ name := x, ty := some ty, span := bsp } :: bs) b) (∃ a, F a)

end NaruSem.Surf
