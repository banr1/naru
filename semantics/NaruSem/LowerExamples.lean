import NaruSem.Lower
import NaruSem.SurfaceExamples

/-!
# Surface AST → Core の変換の検体(IDEAL.md C49 / C52)

一般定理 `lower_sound` が空虚でないこと(対象の各構文の変換が定まり、その形が frontend の Core と同じ形 — `let_` の入れ子、`Nat` のメソッド、被演算子の型の
注釈)、対象外の構文は変換されないこと、意味の異なる Core は変換結果にならないことを、手書きの AST で kernel に検査させる(変換の等式は `rfl`: `lower` は
構造的再帰の関数なので kernel が計算する)。実際の構文解析の出力と実際の Core の検体は `lake exe naru_test semantics`(`tests/accept/sem_core.naru`)が
`low_<f>` で検査する。
-/

namespace NaruSem.Surf
open Naru

/-! ## 変換が定まる(対象の各構文) -/

/-- `{ let y = x + 1; y * 2 }` の変換: `let` の列は `let_` の入れ子で、型の注釈は値の型。 -/
def coreBlock : Core.Expr :=
  .let_ "y" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat) (.binop "*" (.var "y") (.lit (.nat 2) .nat) .nat)

theorem ex_lower_block : lower (Ctx.ofList [("x", .nat)]) exBlock = some coreBlock := rfl

/-- 一般定理の実例: 変換結果は適格で、任意の環境で AST の意味と Core の意味が一致する。 -/
theorem ex_lower_block_wt : NaruSem.wtR (Ctx.ofList [("x", .nat)]) coreBlock = some .nat :=
  lower_wt ex_wtR_block ex_lower_block

theorem ex_lower_block_eval (x : Nat) :
    eval (Env.ofList [("x", .nat x)]) exBlock = NaruSem.eval (Env.ofList [("x", .nat x)]) coreBlock :=
  lower_eval ex_wtR_block ex_lower_block _

/-- 生成 Lean への接続の実例: AST の意味は Core の読み(`denoteN`)の値。 -/
theorem ex_preserve_block (x : Nat) :
    eval (Env.ofList [("x", .nat x)]) exBlock = some (.nat (denoteN (Env.ofList [("x", .nat x)]) coreBlock)) :=
  preserve_nat ex_wtR_block ex_lower_block _ (Env.ty_ofList [("x", .nat x)]).symm

/-- 型注釈つきの `let`: 注釈は Core の `let_` の型に(値の型と一致する)。`if` の分岐のブロックは末尾式そのもの。 -/
def coreAnnot : Core.Expr :=
  .let_ "y" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat)
    (.let_ "b" .bool (.binop ">" (.var "y") (.lit (.nat 2) .nat) .nat)
      (.ite (.var "b") (.var "y") (.lit (.nat 0) .nat)))

theorem ex_lower_annot : lower (Ctx.ofList [("x", .nat)]) exAnnot = some coreAnnot := rfl

/-- ガード付き `match`: パターンは位置情報を落とし、scrutinee の型が注釈になる。 -/
def coreMatchGuard : Core.Expr :=
  .match_ (.lit (.nat 7) .nat) .nat
    [ .mk (.bind "x") (some (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat)) (.lit (.bool false) .bool),
      .mk .wild none (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat) ]

theorem ex_lower_match_guard : lower (Ctx.ofList [("x", .nat)]) exMatchGuard = some coreMatchGuard := rfl

/-- `x.min(y)` は Nat のメソッド `.method "Nat" "min"`。 -/
theorem ex_lower_min :
    lower (Ctx.ofList [("x", .nat), ("y", .nat)]) (.method {} (.var {} ["x"]) "min" [.var {} ["y"]]) =
      some (.method "Nat" "min" (.var "x") [.var "y"] .nat) := rfl

/-- 注釈の無い二項演算の注釈は被演算子の型(Bool の比較は `.bool`、Nat の等値は `.nat`)。 -/
theorem ex_lower_cmp_bool :
    lower (Ctx.ofList [("a", .bool), ("b", .bool)]) (.binop {} "<" (.var {} ["a"]) (.var {} ["b"])) =
      some (.binop "<" (.var "a") (.var "b") .bool) := rfl

theorem ex_lower_eq_nat :
    lower (Ctx.ofList [("x", .nat)]) (.binop {} "==" (.var {} ["x"]) (.lit {} (.nat 1))) =
      some (.binop "==" (.var "x") (.lit (.nat 1) .nat) .nat) := rfl

/-! ## 変換されない(対象外・型が定まらない) -/

/-- 量化(runtime の対象外)。 -/
theorem neg_lower_quant : lower Ctx.empty exForall = none := rfl

/-- 末尾式の無いブロック。 -/
theorem neg_lower_block_no_tail : lower Ctx.empty (.block {} [] none) = none := rfl

/-- `min` / `max` 以外のメソッド。 -/
theorem neg_lower_method : lower (Ctx.ofList [("x", .nat)]) (.method {} (.var {} ["x"]) "size" []) = none := rfl

/-- 修飾名(大域名)。 -/
theorem neg_lower_path : lower Ctx.empty (.var {} ["A", "f"]) = none := rfl

/-- 変換は型に導かれる: 被演算子の型が定まらない(スコープ外の名前)二項演算と、値の型が定まらない `let` は変換されない。 -/
theorem neg_lower_unbound : lower Ctx.empty (.binop {} "+" (.var {} ["x"]) (.lit {} (.nat 1))) = none := rfl

theorem neg_lower_let_unbound :
    lower Ctx.empty (.block {} [.letS {} "y" none (.var {} ["x"])] (some (.var {} ["y"]))) = none := rfl

/-! ## 意味の異なる Core は変換結果でない -/

/-- `a && b` の変換は `.binop "&&"` であって、`&&` を `||` に取り違えた(適格な)Core ではない。 -/
def coreLogicWrong : Core.Expr := .binop "||" (.var "a") (.var "b") .bool

theorem ex_wtR_logic_wrong : NaruSem.wtR (Ctx.ofList [("a", .bool), ("b", .bool)]) coreLogicWrong = some .bool := by decide

theorem neg_lower_swapped :
    lower (Ctx.ofList [("a", .bool), ("b", .bool)]) (.binop {} "&&" (.var {} ["a"]) (.var {} ["b"])) ≠ some coreLogicWrong := by
  rw [show lower (Ctx.ofList [("a", .bool), ("b", .bool)]) (.binop {} "&&" (.var {} ["a"]) (.var {} ["b"])) =
      some (.binop "&&" (.var "a") (.var "b") .bool) from rfl]
  simp [coreLogicWrong]

/-- `{ let x = x + 1; let x = x * 2; x }` の変換は 2 つ目の束縛も `x` であって、`y` に改名した(適格な)Core ではない。 -/
def exLetShadow : Expr :=
  .block {} [ .letS {} "x" none (.binop {} "+" (.var {} ["x"]) (.lit {} (.nat 1))),
              .letS {} "x" none (.binop {} "*" (.var {} ["x"]) (.lit {} (.nat 2))) ]
    (some (.var {} ["x"]))

def coreLetShadow : Core.Expr :=
  .let_ "x" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat)
    (.let_ "x" .nat (.binop "*" (.var "x") (.lit (.nat 2) .nat) .nat) (.var "x"))

def coreLetShadowWrong : Core.Expr :=
  .let_ "x" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat)
    (.let_ "y" .nat (.binop "*" (.var "x") (.lit (.nat 2) .nat) .nat) (.var "x"))

theorem ex_lower_let_shadow : lower (Ctx.ofList [("x", .nat)]) exLetShadow = some coreLetShadow := rfl

theorem ex_wtR_let_shadow_wrong : NaruSem.wtR (Ctx.ofList [("x", .nat)]) coreLetShadowWrong = some .nat := by decide

theorem neg_lower_let_shadow : lower (Ctx.ofList [("x", .nat)]) exLetShadow ≠ some coreLetShadowWrong := by
  rw [ex_lower_let_shadow]
  simp [coreLetShadow, coreLetShadowWrong]

end NaruSem.Surf
