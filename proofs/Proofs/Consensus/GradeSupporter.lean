import Proofs.Consensus.Majority
import Proofs.Consensus.JustificationCertificate
import Mathlib.Tactic

/-!
# grade の通った block には honest な支持者がいる(C71 の補題)

`gradeBool`(`Model/Consensus/Protocol/Grades.lean`)は、validator ごとの `positive`(`supports`)の重みが `opposing`(`opposes`)の
重みより大きいことを言う。ここでは手書き `q20_graded_has_honest_supporter`
(`DecoupledConsensusProofs/Protocol/Grades/Q20_graded_has_honest_supporter.lean`)を生成 Model の定義に対して示す
(周回 196)。

1. **支持か反対か**(`supports_or_opposes`): 早い token の集合が空でなく遅い集合に含まれれば、`supports` か `opposes` が真。
   round が最大の早い token `u` を取り、`u` が `b` を覆わなければ反対の第 1 の枝、`raw` が `u` の round から clean でなければ
   第 2 の枝、`u` より後の遅い token に `b` を覆わないものがあれば第 1 の枝、どれでもなければ支持。手書き `supports_or_opposes`。
2. **cutoff の単調性**: `occurrenceBefore` は cutoff について単調で(`occurrenceBefore_mono`)、`rawInputs` /
   `interpretedInputs` / `readyView` も(`interpretedInputs_mono` / `readyView_mono`。手書き `GradeCutoffMono.readyView_mono`)。
   `0 ≤ Δ` なら phase の早い時刻は遅い時刻以下(`earlyTime_le_lateTime`。手書き `GradeCutoffMono.early_le_late`)。
3. 早い cutoff で解釈済みの入力がある validator は `positive` か `opposing`(`positive_or_opposing`)。
4. **honest な支持者**(`graded_has_honest_positive`): `validators \ H` の重みが、要素がみな `H` にあり早い cutoff で解釈済みの
   入力を持つ集合 `A` の重みより小さく、`gradeBool` が真なら、`H` に `positive` な validator がいる。無ければ
   `A` ⊆ 反対、支持 ⊆ `validators \ H` で、重みが `faulty < A ≤ 反対 < 支持 ≤ faulty` と一周する。手書きの `WindowMajorityAt`
   (faulty の重み < honest present の重み)を、`A` に抽象した形(`A` に awake の窓の honest を置くのが次の段)。
5. 4 の `positive` を開き、honest な `v` の早い cutoff の解釈済みの入力 `y` で、`y.confirmed = some k`、tree の
   `findRoot? k = some head`、`b ⪯ head` のものを返す(`graded_has_honest_supporter_head`。手書きの結論の形)。phase の
   early / late 時刻に置いた版が `phase_graded_has_honest_supporter`。
-/

namespace Proofs.Consensus.GradeSupporter

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Parameters
open Model.Consensus.Objects.Time Model.Consensus.Objects.Weights
open Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.Grades
open Proofs.Consensus.Sets Proofs.Consensus.Weights Proofs.Consensus.Orders

/-! ## 支持か反対か -/

/-- `Token` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem token_compare_eq_iff (a b : Token) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk r k =>
    cases b with
    | mk r' k' =>
      show (compare r r').then ((compare k k').then .eq) = .eq ↔ _
      rw [then_eq_eq, then_eq, Nat.compare_eq_eq, opt_compare_eq_iff bid_compare_eq_iff, Token.mk.injEq]

/-- **支持か反対か**: 早い token の集合 `early` が空でなく遅い集合 `late` に含まれれば、`supports` か `opposes` が真。
手書き `supports_or_opposes`(`Q20_graded_has_honest_supporter.lean`)。 -/
theorem supports_or_opposes (covers : Option BlockId → Block → Bool) (early late raw : NaruStd.Set Token) (b : Block)
    (hne : early.elems ≠ []) (hsub : ∀ x ∈ early.elems, x ∈ late.elems) :
    supports covers early late raw b = true ∨ opposes covers early late raw b = true := by
  obtain ⟨u, hu, hmax⟩ : ∃ u ∈ early.elems, ∀ x ∈ early.elems, x.round ≤ u.round := by
    obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image early.elems.toFinset (fun t => t.round)
      (List.toFinset_nonempty_iff _ |>.mpr hne)
    exact ⟨u, List.mem_toFinset.mp hu, fun x hx => hmax x (List.mem_toFinset.mpr hx)⟩
  have hall : ∀ k, u.round ≤ k → NaruStd.Set.all early (fun x => decide (x.round ≤ k)) = true := by
    intro k hk
    unfold NaruStd.Set.all
    rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (le_trans (hmax x hx) hk)
  by_cases hcov : covers u.key b = true
  · by_cases hclean : cleanFrom raw u.round = true
    · by_cases hsweep : ∀ x ∈ late.elems, u.round < x.round → covers x.key b = true
      · left
        unfold supports NaruStd.Set.any
        rw [List.any_eq_true]
        refine ⟨u, hu, ?_⟩
        simp only [Bool.and_eq_true]
        refine ⟨⟨⟨hall u.round le_rfl, hcov⟩, hclean⟩, ?_⟩
        unfold NaruStd.Set.all
        rw [List.all_eq_true]
        intro x hx
        by_cases hlt : u.round < x.round
        · simp [hsweep x hx hlt]
        · simp [hlt]
      · right
        push Not at hsweep
        obtain ⟨x, hx, hlt, hncov⟩ := hsweep
        unfold opposes NaruStd.Set.any
        rw [Bool.or_eq_true, List.any_eq_true]
        left
        refine ⟨x, hx, ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨hall x.round hlt.le, by simpa using hncov⟩
    · right
      obtain ⟨x, hx, y, hy, hk, hr, hkey⟩ : ∃ x ∈ raw.elems, ∃ y ∈ raw.elems,
          u.round ≤ x.round ∧ x.round = y.round ∧ x.key ≠ y.key := by
        by_contra hne
        apply hclean
        unfold cleanFrom NaruStd.Set.all
        rw [List.all_eq_true]
        intro x hx
        rw [List.all_eq_true]
        intro y hy
        by_cases hk : u.round ≤ x.round
        · by_cases hr : x.round = y.round
          · by_cases hkey : x.key = y.key
            · simp [hkey]
            · exact absurd ⟨x, hx, y, hy, hk, hr, hkey⟩ hne
          · simp [hr]
        · simp [hk]
      unfold opposes NaruStd.Set.any
      rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
      right
      refine ⟨x, hx, ?_⟩
      rw [List.any_eq_true]
      refine ⟨y, hy, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨hall x.round hk, hr⟩, hkey⟩
  · right
    unfold opposes NaruStd.Set.any
    rw [Bool.or_eq_true, List.any_eq_true]
    left
    refine ⟨u, hsub u hu, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hall u.round le_rfl, by simpa using hcov⟩

/-! ## cutoff の単調性 -/

/-- `occurrenceBefore` は cutoff について単調。 -/
theorem occurrenceBefore_mono {x : Option Stamp} {γ γ' : Int} (h : occurrenceBefore x γ = true) (hγ : γ ≤ γ') :
    occurrenceBefore x γ' = true := by
  cases x with
  | none => exact absurd h (by simp [occurrenceBefore])
  | some a =>
    unfold occurrenceBefore at h ⊢
    rw [Proofs.Consensus.Majority.stampBefore_iff] at h ⊢
    rcases h with h | ⟨c, hc, hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, by omega⟩

/-- `rawInputs` の所属: window の round の票の表にあり、送り手が `sender` で、受信の印が cutoff より前。 -/
theorem mem_rawInputs_iff (gv : GradeView) (eta r : Nat) (cutoff : Int) (sender : ValidatorId) (y : SGVote) :
    y ∈ (rawInputs gv eta r cutoff sender).elems ↔
      y ∈ (NaruStd.Set.flatMap (NaruStd.List.toSet (latestWindow eta r)) (fun k =>
          NaruStd.Table.getOr gv.sgVotes k (NaruStd.Set.empty : NaruStd.Set SGVote))).elems ∧
        y.valIndex = sender ∧ occurrenceBefore (NaruStd.Table.get? gv.timestampSgVote y) cutoff = true := by
  unfold rawInputs
  show y ∈ List.filter _ _ ↔ _
  rw [List.mem_filter, Bool.and_eq_true, beq_iff_eq]

/-- `interpretedInputs` の所属: `rawInputs` にあり、`bodyReady`。 -/
theorem mem_interpretedInputs_iff (gv : GradeView) (f : Block) (eta r : Nat) (cutoff : Int) (sender : ValidatorId)
    (y : SGVote) :
    y ∈ (interpretedInputs gv f eta r cutoff sender).elems ↔
      y ∈ (rawInputs gv eta r cutoff sender).elems ∧ bodyReady gv f cutoff y = true := by
  unfold interpretedInputs
  show y ∈ List.filter _ _ ↔ _
  rw [List.mem_filter]

/-- `bodyReady` は cutoff について単調。 -/
theorem bodyReady_mono {gv : GradeView} {f : Block} {c c' : Int} (hc : c ≤ c') {y : SGVote}
    (h : bodyReady gv f c y = true) : bodyReady gv f c' y = true := by
  unfold bodyReady at h ⊢
  cases hconf : y.confirmed with
  | none => rfl
  | some k =>
    rw [hconf] at h
    simp only at h ⊢
    cases hfind : findRoot? gv.tree k with
    | none => rw [hfind] at h; exact h
    | some head =>
      rw [hfind] at h
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨occurrenceBefore_mono h.1 hc, h.2⟩

/-- `interpretedInputs` は cutoff について単調。 -/
theorem interpretedInputs_mono {gv : GradeView} {f : Block} {eta r : Nat} {c c' : Int} (hc : c ≤ c')
    {v : ValidatorId} {y : SGVote} (h : y ∈ (interpretedInputs gv f eta r c v).elems) :
    y ∈ (interpretedInputs gv f eta r c' v).elems := by
  rw [mem_interpretedInputs_iff, mem_rawInputs_iff] at h ⊢
  obtain ⟨⟨hw, hv, ht⟩, hb⟩ := h
  exact ⟨⟨hw, hv, occurrenceBefore_mono ht hc⟩, bodyReady_mono hc hb⟩

/-- `readyView` の所属: 解釈済みの入力の token。 -/
theorem mem_readyView_iff (gv : GradeView) (f : Block) (eta r : Nat) (cutoff : Int) (v : ValidatorId) (x : Token) :
    x ∈ (readyView gv f eta r cutoff v).elems ↔ ∃ y ∈ (interpretedInputs gv f eta r cutoff v).elems, token y = x := by
  unfold readyView NaruStd.Set.map
  rw [mem_of_iff token_compare_eq_iff, List.mem_map]

/-- `readyView` は cutoff について単調。手書き `GradeCutoffMono.readyView_mono`。 -/
theorem readyView_mono {gv : GradeView} {f : Block} {eta r : Nat} {c c' : Int} (hc : c ≤ c') (v : ValidatorId) :
    ∀ x ∈ (readyView gv f eta r c v).elems, x ∈ (readyView gv f eta r c' v).elems := by
  intro x hx
  rw [mem_readyView_iff] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, interpretedInputs_mono hc hy, rfl⟩

/-- `0 ≤ Δ` なら phase の早い時刻は遅い時刻以下。手書き `GradeCutoffMono.early_le_late`。 -/
theorem earlyTime_le_lateTime (e : ProtocolEnv) (hc : HealConfig) (r : Nat) (p : GradePhase) (hδ : 0 ≤ e.delta) :
    earlyTime e hc r p ≤ lateTime e hc r p := by
  unfold earlyTime lateTime
  cases p <;> simp only [earlyOffset, lateOffset] <;> omega

/-- 早い cutoff で解釈済みの入力がある validator は `positive` か `opposing`(`early ≤ late`)。 -/
theorem positive_or_opposing (gv : GradeView) (f : Block) (eta r : Nat) {early late : Int} (hel : early ≤ late)
    (v : ValidatorId) (b : Block) (hne : (interpretedInputs gv f eta r early v).elems ≠ []) :
    positive gv f eta r early late v b = true ∨ opposing gv f eta r early late v b = true := by
  unfold positive opposing
  apply supports_or_opposes
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
    exact List.ne_nil_of_mem ((mem_readyView_iff gv f eta r early v (token y)).mpr ⟨y, hy, rfl⟩)
  · exact readyView_mono hel v

/-! ## honest な支持者 -/

/-- 重みの 0 でない要素がみな `B` にあれば、`A` の重みは `B` の重み以下(`A` は `validators` の部分でなくてよい)。 -/
theorem weightOf_le_of_sub_validators {e : Electorate} {A B : VSet} (hA : Sorted A) (hB : Sorted B)
    (hAB : ∀ x ∈ A.elems, x ∈ (validators e).elems → x ∈ B.elems) : weightOf e A ≤ weightOf e B := by
  rw [weightOf_eq hA, weightOf_eq hB]
  apply Finset.sum_le_sum_of_ne_zero
  intro x hx hne
  rw [List.mem_toFinset] at hx ⊢
  exact hAB x hx (mem_validators_of_weight_ne_zero e x hne)

/-- **grade の通った block には honest な `positive` な validator がいる**: `validators \ H` の重みが、要素がみな `H` にあり
早い cutoff で解釈済みの入力を持つ集合 `A` の重みより小さく(手書きの `WindowMajorityAt` を `A` に抽象した形)、`early ≤ late`
で `gradeBool` が真なら、`H` に `positive` な validator がいる。手書き `q20_graded_has_honest_supporter` の数え上げ。 -/
theorem graded_has_honest_positive (e : ProtocolEnv) (hv : Sorted (validators e.electorate)) (gv : GradeView)
    (f : Block) (eta r : Nat) {early late : Int} (hel : early ≤ late) {H A : VSet} (hA : Sorted A)
    (hAH : ∀ x ∈ A.elems, x ∈ H.elems ∧ (interpretedInputs gv f eta r early x).elems ≠ [])
    (hmaj : weightOf e.electorate ((validators e.electorate).diff H) < weightOf e.electorate A) {b : Block}
    (hgrade : gradeBool e gv f eta r early late b = true) :
    ∃ v ∈ H.elems, positive gv f eta r early late v b = true := by
  by_contra hno
  push Not at hno
  have hnopos : ∀ v ∈ H.elems, positive gv f eta r early late v b = false := fun v hvH => by
    simpa using hno v hvH
  have hopp : weightOf e.electorate A ≤ weightOf e.electorate ((validators e.electorate).filter
      (fun v => opposing gv f eta r early late v b)) := by
    apply weightOf_le_of_sub_validators hA (hv.filter _)
    intro x hx hxv
    obtain ⟨hxH, hxne⟩ := hAH x hx
    show x ∈ (validators e.electorate).elems.filter _
    rw [List.mem_filter]
    refine ⟨hxv, ?_⟩
    rcases positive_or_opposing gv f eta r hel x b hxne with hp | ho
    · rw [hnopos x hxH] at hp
      exact absurd hp (by decide)
    · exact ho
  have hpos : weightOf e.electorate ((validators e.electorate).filter (fun v => positive gv f eta r early late v b)) ≤
      weightOf e.electorate ((validators e.electorate).diff H) := by
    apply Proofs.Consensus.JustificationCertificate.weightOf_le_of_sub (hv.filter _) (hv.filter _)
    intro x hx
    have hx' : x ∈ (validators e.electorate).elems.filter _ := hx
    rw [List.mem_filter] at hx'
    show x ∈ (validators e.electorate).elems.filter _
    rw [List.mem_filter]
    refine ⟨hx'.1, ?_⟩
    cases hc : H.contains x
    · rfl
    · have hxH := (contains_iff_mem vid_eq H x).mp hc
      rw [hnopos x hxH] at hx'
      exact absurd hx'.2 (by decide)
  unfold gradeBool at hgrade
  rw [decide_eq_true_iff] at hgrade
  omega

/-- **grade の通った block には honest な支持者がいる**(`graded_has_honest_positive` の `positive` を開いた形): honest な `v` の
早い cutoff の解釈済みの入力 `y` で、`y.confirmed = some k`、grade view の tree で `findRoot? k = some head`、`b ⪯ head` の
ものがある。手書き `q20_graded_has_honest_supporter` の結論(手書きは `head.root = k` と `find?`)。 -/
theorem graded_has_honest_supporter_head (e : ProtocolEnv) (hv : Sorted (validators e.electorate)) (gv : GradeView)
    (f : Block) (eta r : Nat) {early late : Int} (hel : early ≤ late) {H A : VSet} (hA : Sorted A)
    (hAH : ∀ x ∈ A.elems, x ∈ H.elems ∧ (interpretedInputs gv f eta r early x).elems ≠ [])
    (hmaj : weightOf e.electorate ((validators e.electorate).diff H) < weightOf e.electorate A) {b : Block}
    (hgrade : gradeBool e gv f eta r early late b = true) :
    ∃ v ∈ H.elems, ∃ y ∈ (interpretedInputs gv f eta r early v).elems, ∃ (k : BlockId) (head : Block),
      y.confirmed = some k ∧ findRoot? gv.tree k = some head ∧ preceq b head = true := by
  obtain ⟨v, hvH, hpos⟩ := graded_has_honest_positive e hv gv f eta r hel hA hAH hmaj hgrade
  unfold positive supports NaruStd.Set.any at hpos
  rw [List.any_eq_true] at hpos
  obtain ⟨x, hx, hsx⟩ := hpos
  simp only [Bool.and_eq_true] at hsx
  have hcov := hsx.1.1.2
  obtain ⟨y, hy, rfl⟩ := (mem_readyView_iff gv f eta r early v x).mp hx
  refine ⟨v, hvH, y, hy, ?_⟩
  unfold localCovers headCovers token at hcov
  simp only at hcov
  cases hconf : y.confirmed with
  | none => rw [hconf] at hcov; simp at hcov
  | some k =>
    rw [hconf] at hcov
    simp only at hcov
    cases hfind : findRoot? gv.tree k with
    | none => rw [hfind] at hcov; simp at hcov
    | some head =>
      rw [hfind] at hcov
      exact ⟨k, head, rfl, hfind, hcov⟩

/-- **phase の grade の通った block には honest な支持者がいる**(`0 ≤ Δ`): `graded_has_honest_supporter_head` の cutoff を
round `r` の phase `p` の early / late 時刻に置いた版。手書き `q20_graded_has_honest_supporter`(`phaseGrade` と
`WindowMajorityAt` の early cutoff)と同じ形。 -/
theorem phase_graded_has_honest_supporter (e : ProtocolEnv) (hc : HealConfig) (hδ : 0 ≤ e.delta)
    (hv : Sorted (validators e.electorate)) (gv : GradeView) (f : Block) (r : Nat) (p : GradePhase) {H A : VSet}
    (hA : Sorted A)
    (hAH : ∀ x ∈ A.elems, x ∈ H.elems ∧ (interpretedInputs gv f hc.etaSG r (earlyTime e hc r p) x).elems ≠ [])
    (hmaj : weightOf e.electorate ((validators e.electorate).diff H) < weightOf e.electorate A) {b : Block}
    (hgrade : gradeBool e gv f hc.etaSG r (earlyTime e hc r p) (lateTime e hc r p) b = true) :
    ∃ v ∈ H.elems, ∃ y ∈ (interpretedInputs gv f hc.etaSG r (earlyTime e hc r p) v).elems,
      ∃ (k : BlockId) (head : Block),
        y.confirmed = some k ∧ findRoot? gv.tree k = some head ∧ preceq b head = true :=
  graded_has_honest_supporter_head e hv gv f hc.etaSG r (earlyTime_le_lateTime e hc r p hδ) hA hAH hmaj hgrade

/-! ## grade の通った block 同士は互換 -/

/-- 同じ token の key が覆う 2 つの block は互換(どちらも tree の同じ head の祖先)。手書き `q10_covers_compatible`。 -/
theorem localCovers_compatible {gv : GradeView} {k : Option BlockId} {b b' : Block}
    (h : localCovers gv k b = true) (h' : localCovers gv k b' = true) : compatible b b' = true := by
  unfold localCovers headCovers at h h'
  cases k with
  | none => simp at h
  | some r =>
    simp only at h h'
    cases hf : findRoot? gv.tree r with
    | none => rw [hf] at h; simp at h
    | some hd =>
      rw [hf] at h h'
      exact Proofs.Consensus.Blocks.compatible_of_preceq_common h h'

/-- **支持は互換でない block への反対**(`early ≤ late`): `v` が `b` に `positive` なら、`b` と互換でない `b'` に `opposing`。
支持の根拠の早い token `x`(round が早い token の中で最大で `b` を覆う)は遅い cutoff でも解釈済みで(`readyView_mono`)、
`b'` を覆えば `b` と `b'` は互換になる。手書き `q10_opposing_of_positive`(`SGFromSupport.sg_opposing_of_positive`)。 -/
theorem opposing_of_positive (gv : GradeView) (f : Block) (eta r : Nat) {early late : Int} (hel : early ≤ late)
    (v : ValidatorId) {b b' : Block} (hne : compatible b b' = false)
    (hpos : positive gv f eta r early late v b = true) : opposing gv f eta r early late v b' = true := by
  unfold positive supports NaruStd.Set.any at hpos
  rw [List.any_eq_true] at hpos
  obtain ⟨x, hx, hsx⟩ := hpos
  simp only [Bool.and_eq_true] at hsx
  obtain ⟨⟨⟨hmax, hcov⟩, -⟩, -⟩ := hsx
  unfold opposing opposes NaruStd.Set.any
  rw [Bool.or_eq_true, List.any_eq_true]
  refine Or.inl ⟨x, readyView_mono hel v x hx, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨hmax, ?_⟩
  show (!localCovers gv x.key b') = true
  cases hc : localCovers gv x.key b'
  · rfl
  · rw [localCovers_compatible hcov hc] at hne
    exact absurd hne (by decide)

/-- **grade の通った 2 つの block は互換**(`early ≤ late`): 互換でなければ、一方の支持は他方の反対に含まれ
(`opposing_of_positive`)、重みが `支持(b) ≤ 反対(b') < 支持(b') ≤ 反対(b) < 支持(b)` と一周する。
手書き `q10_graded_compatible`(`SGFromSupport.sg_graded_compatible`)。 -/
theorem graded_compatible (e : ProtocolEnv) (hv : Sorted (validators e.electorate)) (gv : GradeView) (f : Block)
    (eta r : Nat) {early late : Int} (hel : early ≤ late) {b b' : Block}
    (hb : gradeBool e gv f eta r early late b = true) (hb' : gradeBool e gv f eta r early late b' = true) :
    compatible b b' = true := by
  by_contra hcon
  have hne : compatible b b' = false := by simpa using hcon
  have hne' : compatible b' b = false := by rw [Proofs.Consensus.Blocks.compatible_comm]; exact hne
  have hsub : ∀ {x y : Block}, compatible x y = false →
      weightOf e.electorate ((validators e.electorate).filter (fun v => positive gv f eta r early late v x)) ≤
        weightOf e.electorate ((validators e.electorate).filter (fun v => opposing gv f eta r early late v y)) := by
    intro x y hxy
    apply Proofs.Consensus.JustificationCertificate.weightOf_le_of_sub (hv.filter _) (hv.filter _)
    intro z hz
    have hz' : z ∈ (validators e.electorate).elems.filter _ := hz
    rw [List.mem_filter] at hz'
    show z ∈ (validators e.electorate).elems.filter _
    rw [List.mem_filter]
    exact ⟨hz'.1, opposing_of_positive gv f eta r hel z hxy hz'.2⟩
  have h1 := hsub hne
  have h2 := hsub hne'
  unfold gradeBool at hb hb'
  rw [decide_eq_true_iff] at hb hb'
  omega

end Proofs.Consensus.GradeSupporter
