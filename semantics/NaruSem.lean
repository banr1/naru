import NaruSem.Scope
import NaruSem.Eval
import NaruSem.Sem
import NaruSem.Totality
import NaruSem.SemTotality
import NaruSem.Examples
import NaruSem.Quote
import NaruSem.Audit

/-!
# `NaruSem` — naru の Core IR の独立した意味論とコンパイラ意味論保存の証明(IDEAL.md C39〜C47)

`lake build NaruSem` が、意味論・適格性の定義、一般定理、検体、公理監査をまとめて Lean kernel に検査させる(C45 の検査入口。
走らせ方は `docs/testing.md`「コンパイラ意味論保存」、構成と定理の一覧は `docs/architecture.md`「コンパイラ意味論保存」)。
backend の出力を意味と定義せず、翻訳の正しさを仮定しない。

- `NaruSem/Scope.lean` — 今回の保存対象の範囲と整形性: 型 `Ty` / `STy`、演算 `BinOp` / `NatMethod`、文脈 `Ctx` / `SCtx`、
  runtime の型付け `wtR`(+ `wtArmsR` / `wtArmR`)、spec の型付け `wtS`(+ `wtArmsS` / `wtArmS`)、パターン `wtPat`、網羅性 `exhaustive`、
  命題の区分 `proppyS`。
- `NaruSem/Eval.lean` — runtime の表示的意味論 `eval`(値 `Val`、環境 `Env`、演算の意味、`matchPat` / `evalArms`)。
- `NaruSem/Sem.lean` — spec の評価関係 `Sem`(環境 `SEnv`: 値と命題を区別)。
- `NaruSem/Totality.lean` — runtime の全域性 `eval_total` と一意性 `Eval_unique`。
- `NaruSem/SemTotality.lean` — spec の意味の存在 `Sem_exists` と一意性 `Sem_unique`。
- `NaruSem/Examples.lean` — 対象範囲・境界の挙動・不適格な Core・行き詰まりの検体(`decide`)。
- `NaruSem/Quote.lean` — 実際の compiler 経路の Core を Lean の項として引用し、一致を照合する(`lake exe naru_test semantics` が使う)。
- `NaruSem/Audit.lean` — 公理監査 `#audit_axioms`(許容する標準公理と理由はそこに)。

## 公理監査(C45)

必須の定理・補題・検体をすべて列挙する。欠落(名前解決の失敗)・未完了(`sorryAx`)・`native_decide`(`Lean.ofReduceBool`)・
独自の公理への依存はここでビルドが失敗する。`lake env lean semantics/NaruSem.lean` の出力の `audit ok:` の行が各定数の依存する公理の一覧
(`lake exe naru_test semantics` が必須の定理の行を照合する)。
-/

-- C39: 意味論の全域性・一意性と、環境と文脈の対応の補題
#audit_axioms NaruSem.eval_total NaruSem.Eval_unique NaruSem.wtR_total_all
  NaruSem.Sem_exists NaruSem.Sem_unique NaruSem.Sem_exists_all
  NaruSem.matchPat_types NaruSem.matchPat_irrefutable NaruSem.Env.ty_ext NaruSem.Env.ty_extList
  NaruSem.SEnv.ctx_ext NaruSem.SEnv.ctx_extVals NaruSem.SEnv.ctx_vals NaruSem.evalS_total

-- C39: 対象範囲と境界の挙動・不適格な Core・行き詰まりの検体
#audit_axioms NaruSem.ex_wtR_let NaruSem.ex_eval_let NaruSem.ex_eval_match_guard NaruSem.ex_wtS_forall NaruSem.ex_wtS_prop_and
  NaruSem.ex_nat_sub_truncates NaruSem.ex_nat_div_zero NaruSem.ex_nat_mod_zero NaruSem.ex_bool_order NaruSem.ex_implies
  NaruSem.neg_wtR_unbound NaruSem.neg_wtR_ill_typed NaruSem.neg_wtR_let_annotation NaruSem.neg_wtR_ite_branches
  NaruSem.neg_wtR_call NaruSem.neg_wtR_string NaruSem.neg_wtR_lambda NaruSem.neg_wtR_int
  NaruSem.neg_wtR_match_not_exhaustive NaruSem.neg_wtR_match_guarded_only NaruSem.ex_wtR_match_bool_complete NaruSem.neg_wtR_match_bool_half
  NaruSem.neg_wtS_prop_in_value NaruSem.neg_wtS_prop_scrutinee NaruSem.neg_wtS_quant_string NaruSem.ex_wtS_nat_not_form
  NaruSem.neg_eval_unbound NaruSem.neg_eval_ill_typed NaruSem.neg_eval_match_stuck NaruSem.neg_eval_guard_stuck NaruSem.neg_eval_call
  NaruSem.neg_Sem_unbound NaruSem.neg_Sem_nat_value NaruSem.neg_Sem_match_stuck
