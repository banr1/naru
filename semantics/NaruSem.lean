import NaruSem.Scope
import NaruSem.Eval
import NaruSem.Sem
import NaruSem.Totality
import NaruSem.SemTotality
import NaruSem.Denote
import NaruSem.DenoteProp
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
- `NaruSem/Denote.lean` — Model の保存(C40 / C41 / C44): 生成 Lean の読み `denoteN` / `denoteB` と腕の列の読み `denoteArmsN` / `denoteArmsB`、
  基礎段階の範囲 `basic`(段階の記録)、保存定理 `denote_sound`(`preserve_nat` / `preserve_bool`。基礎の構文と非再帰の Nat / Bool の `match`)、
  腕の列・腕の一般補題 `denoteArms_sound` / `denoteArm_sound`、腕の選択と束縛の形 `denoteArmsV_hit` / `_miss` / `_guard_true` / `_guard_false`、
  実生成宣言への接続検査の健全性 `check_sound_nat` / `check_sound_bool`。
- `NaruSem/DenoteProp.lean` — Statements の保存(C42 / C43 / C44): 生成 Lean の命題の読み `denoteP`(+ 腕の列 `denoteArmsP`、量化 `denoteQuant`)、
  値 / 命題の境界 `denoteP_iff_denoteB_noProp`(`proppyS` が偽の式すべて。`proppyS` の文脈の合同 `proppyS_congr`)、一般同値定理 `Sem_denote`
  (`wtS` で適格な式すべて: 量化・命題の `let` と shadowing・命題の条件の `if`・ガード付き `match` を含む。`Sem_denote_all` は網羅性を要求しない
  型付け `wtSNoExh` を仮定に `Sem` の導出の帰納法。`Sem_denoteP`: 読みは意味である)、腕の選択と束縛の形 `denoteArmsP_hit` / `_miss` / `_guard` /
  `_guard_true` / `_guard_false`、量化の読みの形 `denoteQuant_forall_cons` / `_exists_cons`、接続検査の健全性 `check_sound_prop`、異なる表現の対応関係
  (`CmpOp.leanBoolProp_iff` / `EqOp.propIff_bool`: 値の等値と命題の同値の区別 …)。基礎段階(C42)の `basic` / `SCtx.NoProp` は段階の記録(系)。
- `NaruSem/Examples.lean` — 対象範囲・境界の挙動・不適格な Core・行き詰まり・読みの検体(`decide`)。
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

-- C40 / C44: Model の基礎段階の保存定理と、実生成宣言への接続検査の健全性・異なる表現の対応関係
#audit_axioms NaruSem.denote_sound NaruSem.preserve_nat NaruSem.preserve_bool NaruSem.denote_sound_all
  NaruSem.check_sound_nat NaruSem.check_sound_bool NaruSem.Env.ty_ofList NaruSem.denoteV_ty
  NaruSem.CmpOp.leanBool_eq NaruSem.EqOp.leanNat_eq NaruSem.EqOp.leanBool_eq

-- C40: 基礎段階の範囲と読みの境界の検体
#audit_axioms NaruSem.ex_basic_let NaruSem.neg_basic_match NaruSem.ex_denote_sub_truncates NaruSem.ex_denote_div_zero
  NaruSem.ex_denote_mod_zero NaruSem.ex_denote_bool_order NaruSem.ex_preserve_let

-- C41 / C44: Model の match の保存 — 腕の列・腕の一般補題、腕の選択と束縛の形、腕の列の読みの展開
#audit_axioms NaruSem.denoteArms_sound NaruSem.denoteArm_sound NaruSem.denoteArmsV_hit NaruSem.denoteArmsV_miss
  NaruSem.denoteArmsV_guard_true NaruSem.denoteArmsV_guard_false NaruSem.denoteArmsN_cons NaruSem.denoteArmsB_cons NaruSem.denoteArmsV_ty

-- C41: match の読みの検体(ガード不成立からの継続と束縛の範囲、Bool のリテラルの腕、保存定理の実例)
#audit_axioms NaruSem.ex_wtR_match_guard NaruSem.ex_denote_match_guard NaruSem.ex_denote_match_bool NaruSem.ex_preserve_match

-- C42 / C44: Statements の基礎段階の同値定理、値 / 命題の境界、接続検査の健全性、異なる表現の対応関係、基礎段階の範囲の補題
#audit_axioms NaruSem.Sem_denote NaruSem.Sem_denoteP NaruSem.Sem_denote_basic NaruSem.check_sound_prop NaruSem.denoteP_iff_denoteB
  NaruSem.basic_not_proppy NaruSem.SEnv.vals_ext_val NaruSem.SEnv.ctx_ofList NaruSem.SCtx.NoProp.ofList NaruSem.SCtx.NoProp.ext_val
  NaruSem.CmpOp.leanBoolProp_iff NaruSem.CmpOp.leanBoolProp_iff_leanBool NaruSem.CmpOp.propNat_iff
  NaruSem.EqOp.propNat_iff NaruSem.EqOp.propNat_iff_leanNat NaruSem.EqOp.propBool_iff NaruSem.EqOp.propBool_iff_leanBool
  NaruSem.EqOp.propIff_bool NaruSem.LogicOp.prop_iff

-- C42: Statements の読みの検体(値の let と Bool の条件、値の等値と命題の同値の区別、同値定理の実例)
#audit_axioms NaruSem.ex_wtS_spec_let NaruSem.ex_basic_spec_let NaruSem.ex_denoteP_spec_let NaruSem.ex_Sem_spec_let
  NaruSem.ex_denoteP_iff_denoteB_let NaruSem.ex_denoteP_eq_bool NaruSem.ex_Sem_eq_bool NaruSem.ex_Sem_denote_eq_bool

-- C43 / C44: Statements の一般同値定理(量化・命題の let と shadowing・命題の条件の if・ガード付き match)、値 / 命題の境界の一般形、
-- proppyS の文脈の合同、網羅性を要求しない型付け、読みの形(局所束縛・条件・==、腕の選択と束縛、量化)
#audit_axioms NaruSem.Sem_denote_all NaruSem.Sem_denote_basic NaruSem.denoteP_iff_denoteB_all NaruSem.denoteP_iff_denoteB_noProp
  NaruSem.proppyS_congr_all NaruSem.proppyS_congr NaruSem.proppyArms_congr NaruSem.proppyArms_cons NaruSem.proppyS_var
  NaruSem.SCtx.isProp_ext NaruSem.SCtx.isProp_ext_val NaruSem.SEnv.vals_extVals
  NaruSem.wtS_noExh NaruSem.wtArmsS_head NaruSem.wtArmsS_tail
  NaruSem.denoteP_let_prop NaruSem.denoteP_let_bool NaruSem.denoteP_ite_prop NaruSem.denoteP_ite_bool NaruSem.denoteP_eq_prop NaruSem.denoteP_eq_bool
  NaruSem.denoteArmsP_hit NaruSem.denoteArmsP_miss NaruSem.denoteArmsP_guard NaruSem.denoteArmsP_guard_true NaruSem.denoteArmsP_guard_false
  NaruSem.denoteQuant_nil NaruSem.denoteQuant_forall_cons NaruSem.denoteQuant_exists_cons

-- C43: Statements の読みの検体(命題の let を隠すパターン束縛、Bool の全要素の量化、境界の一般形の実例)
#audit_axioms NaruSem.ex_wtS_pat_shadow NaruSem.ex_denoteP_pat_shadow NaruSem.ex_Sem_pat_shadow
  NaruSem.ex_denoteP_exists_bool NaruSem.ex_Sem_exists_bool NaruSem.ex_denoteP_iff_denoteB_match
