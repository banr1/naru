import NaruSem.LowerSpec
import NaruSem.LowerExamples

/-!
# spec の Surface AST → Core の変換の検体(IDEAL.md C50 / C52)

一般定理 `lowerS_sound` / `Sem_lowerS_iff` が空虚でないこと(spec の各構文の変換が定まり、その形が frontend の Core と同じ形 — 量化の束縛、命題の `let` の
注釈 `.bool`、注釈の無い `==` の注釈、ガード付き `match`)、対象外の構文は変換されないこと、意味の異なる(適格な)Core は変換結果にならないことを、
手書きの AST で kernel に検査させる(変換の等式は `rfl`)。実際の構文解析の出力と実際の Core の検体は `lake exe naru_test semantics`
(`tests/accept/sem_core.naru`)が `lows_<f>` で検査する。
-/

namespace NaruSem.Surf
open Naru

/-! ## 変換が定まる(spec の各構文) -/

/-- `forall n: Nat { n + x >= x }` の変換: 束縛は (名前, 型)、本体のブロックは末尾式そのもの、比較の注釈は被演算子の型。 -/
def coreForall : Core.Expr :=
  .quant .forall_ [("n", .nat)] (.binop ">=" (.binop "+" (.var "n") (.var "x") .nat) (.var "x") .nat)

theorem ex_lowerS_forall : lowerS (SCtx.ofList [("x", .val .nat)]) exForall = some coreForall := rfl

/-- 一般定理の実例: 変換結果は適格。 -/
theorem ex_lowerS_forall_wt : NaruSem.wtS (SCtx.ofList [("x", .val .nat)]) coreForall = some .prop :=
  lowerS_wt ex_wtS_forall ex_lowerS_forall

/-- 一般定理の実例: 任意の対応する環境・任意の命題について、AST の意味であることと Core の意味であることは同値(双方向)。 -/
theorem ex_Sem_lowerS_forall (x : Nat) (P : Prop) :
    Sem (SEnv.ofList [("x", .val (.nat x))]) exForall P ↔ NaruSem.Sem (SEnv.ofList [("x", .val (.nat x))]) coreForall P :=
  Sem_lowerS_iff ex_wtS_forall rfl ex_lowerS_forall _ (by rw [SEnv.ctx_ofList]; rfl) P

/-- 生成 Lean への接続の実例: AST の意味 `∀ n, n + x ≥ x` は Core の読み `denoteP` と同値。 -/
theorem ex_preserve_forall (x : Nat) :
    (∀ n : Nat, n + x ≥ x) ↔ denoteP (SEnv.ofList [("x", .val (.nat x))]) coreForall :=
  preserve_prop ex_wtS_forall ex_lowerS_forall _ (by rw [SEnv.ctx_ofList]; rfl)
    (.forallCons (t := .nat) (F := fun (n : Nat) => n + x ≥ x) rfl fun _ => .quantNil (.blockTail (.cmpNat (k := .ge) rfl rfl rfl)))

/-- 命題の `let`(`let p = forall …; let q = p && x >= 1; q`): 値が命題の `let` は注釈 `.bool` の `let_`(frontend と同じ)、論理の注釈は `.bool`。 -/
def coreLetProp : Core.Expr :=
  .let_ "p" .bool coreForall
    (.let_ "q" .bool (.binop "&&" (.var "p") (.binop ">=" (.var "x") (.lit (.nat 1) .nat) .nat) .bool) (.var "q"))

theorem ex_lowerS_let_prop : lowerS (SCtx.ofList [("x", .val .nat)]) exLetProp = some coreLetProp := rfl

/-- 注釈 `Bool` の命題の `let` と値の `let`(`let p: Bool = forall …; let b: Bool = x > 0; p && b`)。 -/
def coreLetAnnot : Core.Expr :=
  .let_ "p" .bool coreForall
    (.let_ "b" .bool (.binop ">" (.var "x") (.lit (.nat 0) .nat) .nat) (.binop "&&" (.var "p") (.var "b") .bool))

theorem ex_lowerS_let_annot : lowerS (SCtx.ofList [("x", .val .nat)]) exLetAnnot = some coreLetAnnot := rfl

/-- 注釈の無い `==`: 両辺が Nat の値なら注釈 `.nat`(値の等値)、命題を含めば `.bool`(命題の同値)。 -/
theorem ex_lowerS_eq_nat :
    lowerS (SCtx.ofList [("x", .val .nat)]) (.binop {} "==" (.var {} ["x"]) (.lit {} (.nat 1))) =
      some (.binop "==" (.var "x") (.lit (.nat 1) .nat) .nat) := rfl

theorem ex_lowerS_eq_prop :
    lowerS (SCtx.ofList [("p", .prop), ("a", .val .bool)]) (.binop {} "==" (.var {} ["p"]) (.var {} ["a"])) =
      some (.binop "==" (.var "p") (.var "a") .bool) := rfl

/-- 命題のガード付き `match`: `match x { n if exists m: Nat { m + 1 == n } => n > 0, _ => x == 0 }`。 -/
def exMatchGuardProp : Expr :=
  .matchE {} (.var {} ["x"])
    [ .mk (.bind {} "n")
        (some (.quant {} .exists_ [{ name := "m", ty := some tyNat, span := {} }]
          (.block {} [] (some (.binop {} "==" (.binop {} "+" (.var {} ["m"]) (.lit {} (.nat 1))) (.var {} ["n"]))))))
        (.binop {} ">" (.var {} ["n"]) (.lit {} (.nat 0))),
      .mk (.wild {}) none (.binop {} "==" (.var {} ["x"]) (.lit {} (.nat 0))) ]

def coreMatchGuardProp : Core.Expr :=
  .match_ (.var "x") .nat
    [ .mk (.bind "n")
        (some (.quant .exists_ [("m", .nat)] (.binop "==" (.binop "+" (.var "m") (.lit (.nat 1) .nat) .nat) (.var "n") .nat)))
        (.binop ">" (.var "n") (.lit (.nat 0) .nat) .nat),
      .mk .wild none (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat) ]

theorem ex_wtS_match_guard_prop : wtS (SCtx.ofList [("x", .val .nat)]) exMatchGuardProp = some .prop := by decide

theorem ex_lowerS_match_guard_prop : lowerS (SCtx.ofList [("x", .val .nat)]) exMatchGuardProp = some coreMatchGuardProp := rfl

/-! ## 変換されない(対象外・型が定まらない) -/

/-- 束縛型の注釈が無い量化。 -/
theorem neg_lowerS_quant_untyped :
    lowerS SCtx.empty (.quant {} .forall_ [{ name := "n", ty := none, span := {} }] (.lit {} (.bool true))) = none := rfl

/-- 命題の scrutinee(値の位置の命題)は変換されない。 -/
theorem neg_lowerS_prop_scrutinee :
    lowerS (SCtx.ofList [("p", .prop)]) (.matchE {} (.var {} ["p"]) [.mk (.wild {}) none (.lit {} (.bool true))]) = none := rfl

/-- 算術の被演算子の命題: AST として不適格(`neg_wtS_prop_in_value`)で一般定理の対象外。変換は型に導かれるので定まることがあるが、その Core は
Core としても不適格(命題に束ねた名前は値の位置でスコープ外)で、保証対象にならない。 -/
theorem neg_lowerS_prop_in_value :
    ∀ c, lowerS (SCtx.ofList [("p", .prop)]) (.binop {} "+" (.var {} ["p"]) (.lit {} (.nat 1))) = some c →
      NaruSem.wtS (SCtx.ofList [("p", .prop)]) c = none := by
  intro c hc
  rw [show lowerS (SCtx.ofList [("p", .prop)]) (.binop {} "+" (.var {} ["p"]) (.lit {} (.nat 1))) =
      some (.binop "+" (.var "p") (.lit (.nat 1) .nat) .nat) from rfl] at hc
  cases hc
  decide

/-- 末尾式の無いブロック、修飾名。 -/
theorem neg_lowerS_block_no_tail : lowerS SCtx.empty (.block {} [] none) = none := rfl

theorem neg_lowerS_path : lowerS SCtx.empty (.var {} ["A", "f"]) = none := rfl

/-! ## 意味の異なる Core は変換結果でない -/

/-- `forall` を `exists` に取り違えた(適格な)Core は `forall n: Nat { … }` の変換結果でない。 -/
def coreForallWrong : Core.Expr :=
  .quant .exists_ [("n", .nat)] (.binop ">=" (.binop "+" (.var "n") (.var "x") .nat) (.var "x") .nat)

theorem ex_wtS_forall_wrong : NaruSem.wtS (SCtx.ofList [("x", .val .nat)]) coreForallWrong = some .prop := by decide

theorem neg_lowerS_swapped_quant : lowerS (SCtx.ofList [("x", .val .nat)]) exForall ≠ some coreForallWrong := by
  rw [ex_lowerS_forall]
  simp [coreForall, coreForallWrong]

/-- 命題の `let` の束縛を取り違えた(末尾が `q` でなく `p`)Core は変換結果でない。 -/
def coreLetPropWrong : Core.Expr :=
  .let_ "p" .bool coreForall
    (.let_ "q" .bool (.binop "&&" (.var "p") (.binop ">=" (.var "x") (.lit (.nat 1) .nat) .nat) .bool) (.var "p"))

theorem ex_wtS_let_prop_wrong : NaruSem.wtS (SCtx.ofList [("x", .val .nat)]) coreLetPropWrong = some .prop := by decide

theorem neg_lowerS_let_prop_wrong : lowerS (SCtx.ofList [("x", .val .nat)]) exLetProp ≠ some coreLetPropWrong := by
  rw [ex_lowerS_let_prop]
  simp [coreLetProp, coreLetPropWrong]

end NaruSem.Surf
