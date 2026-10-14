import Proofs.Consensus.Votes
import Proofs.Consensus.Goldfish
import Proofs.Consensus.Weights
import Proofs.Consensus.Liveness
import Mathlib.Tactic

/-!
# 確認の門 `lateCount < 2 · score` と honest 過半(C71 の liveness 系 claim の足場)

`updateConfirmationWith`(`Model/Consensus/Protocol/Handlers.lean`)が確認の候補に選ぶ fork choice の head は、確認の門
`lateCount < 2 · score`(`Goldfish.lean` の `latestConfirmed_shape`)を通る。`score b` は支持の投票 `supportVotes`(`supportCutoff` までに
解決した slot `s` の投票のうち、遅い投票 `lateVotes` に同じ投票者の別の投票が無いもの `noSecondVoteIn`)の equivocator の数と `b` の支持者の数の和、
`lateCount` は遅い投票(`confirmationTime` までに受信した slot `s` の投票)の参加者の数(`Model/Consensus/Protocol/ForkChoice/Goldfish.lean`)。
このモジュールは、その門の honest 過半についての数え上げを生成 Model の定義に対して示す。手書き
`DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean` の `Numerator` / `HonestSupport` の筋。
- **支持の投票は投票者ごとに 1 つ**(`supportVotes_unique`): `noSecondVoteIn lateVotes` の絞り込みと「支持の投票は遅い投票」
  (`supportVotes_sub_lateVotes`: 解決の印 `storeTau` は受信の印 `timestampVote` 以上で、`supportCutoff ≤ confirmationTime`、`0 ≤ Δ`)から。
  したがって支持の投票に equivocator は無く(`supportVotes_no_equivocation`。`NaruStd.Set` の要素は整列して重複が無い `SortedLt`)、
  得点は支持者の数そのもの(`score_eq_supporters`)。手書き `Numerator.unique_in_late` / `no_equivocation` / `score_eq_supporters`。
- **参加者は committee の要素**(`participants_sub_committee`: pool の不変条件 `Votes.lean`)。手書き `voters_count_le_committee`。
  支持者は参加者(`Goldfish.lean` の `rawSupporters_sub_participants`、手書き `supporters_subset_participants`)。
- **数え上げの核** `exists_honest_of_majority`(`Finset` の上): equivocator `E` と支持者 `S` は遅い投票の参加者 `P` に含まれ互いに素、
  `P ⊆ C`(committee)、honest な committee の要素 `C ∩ H` はすべて参加者、`|C| < 2 |C ∩ H|`(`HonestCommittees`)、門 `|P| < 2 (|E| + |S|)`
  なら `E ∪ S` に honest な要素がある(無ければ `E ∪ S ⊆ P \ H` で `2 |P \ H| > |P| ≥ |P \ H| + |C ∩ H|`、一方 `|P \ H| ≤ |C \ H| < |C ∩ H|`)。
- **門を通るブロックには honest な支持者がいる**(`exists_honest_supporter`): 前提は `0 ≤ Δ`・pool の不変条件・committee の整列
  (`SetupWellFormed`)・`HonestCommittees` の slot `s` の不等式・honest な committee の要素がすべて遅い投票の参加者であること。
  fork choice の head が SG root から降りていれば head について(`exists_honest_supporter_of_head`)。
- **`HonestSupport`**(手書きの形から `vote` を弱めたもの: 手書きは投票が `B` にちょうど解決することを要求し、ここでは `B` 以下を指す
  `targetsUnder` でよい): committee は honest 過半で、honest な committee の要素はみな支持の投票に `B` 以下を指す slot `s` の投票を持つ。
  このとき honest な committee の要素はみな遅い投票の参加者で `B` の支持者(`participants` / `supporters`)、`B` とその祖先は門を通る
  (`eligible` / `eligible_of_preceq`: `2 · score B ≥ 2 |C ∩ H| > |C| ≥ lateCount`、得点は祖先ほど大きい。手書き `HonestSupport.eligible`)、
  門を通るどのブロック `C` も `B` と互換(`compatible_of_eligible`: `C` の honest な支持者の投票は投票者ごとに 1 つなので `B` 以下も指す。
  手書き `HonestSupport.not_eligible`(`B` と競合するブロックは門を通らない)より弱い形 — `vote` を弱めたので結論は互換まで)。
残るのは `SleepyRegime` の下で `HonestSupport` の `vote` を示すこと — honest な tick は `voteTime` に自分の fork choice の head への投票を発行し
(`goldfishVoteWith_some`)、その head が honest な提案 `B` を延ばして slot が `s` 以下であること(投票者の fork choice `getHeadInTreeWith` /
`voterView` が `B` を採る。手書きでは `B.slot = Σ.s` なので過半なしに適格)、`ExecutionValid` / `PartialSynchrony` で投票とブロック `B` が honest な
全ノードに `supportCutoff` までに届くこと(解決の印 `storeTau` は投票の受信の印と head のブロックの受信の印の大きい方) —、2 つの honest なノードの
読みの間の正準性(手書きの安全の核
`eligible_compatible`: 一方の支持の投票が他方の遅い投票に入る `CrossView` の下で、同じ slot に両ノードで門を通る 2 ブロックは互換 —
2 つの支持者の集合は `noSecondVoteIn` で互いに素でどちらも一方の参加者に収まるので `2(a + b) ≤ count_v + count_w < 2a + 2b`)、
そして確認の記録・stable の記録・grade の候補の分岐をそれで結ぶこと。生成 Model の得点と `HonestCommittees` は個数(`Set.size`)なので
重みではなく個数で数える(手書きも Goldfish の確認は個数)。
-/

namespace Proofs.Consensus.Majority

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Parameters
open Model.Consensus.Objects.Time
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Schedule
open Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.StoreBase Model.Consensus.Protocol.Grades
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Blocks Proofs.Consensus.Sets Proofs.Consensus.Trees Proofs.Consensus.Orders Proofs.Consensus.Votes
open Proofs.Consensus.Goldfish (earlyVotes lateVotes supportVotes lateCount sgRoot mem_votesBy_iff mem_voters_iff
  mem_rawSupporters_iff participates_of_mem eligible_iff head_cases targetsUnder_iff)

/-! ## 数え上げの核 -/

/-- **門を通る集合には honest な要素がある**(`Finset` の上の数え上げ)。`E`(equivocator)と `S`(支持者)は参加者 `P` に含まれ互いに素、
`P ⊆ C`(committee)、honest な committee の要素 `C ∩ H` はすべて参加者、committee は honest 過半 `|C| < 2 |C ∩ H|`、門
`|P| < 2 (|E| + |S|)` なら、`E ∪ S` に honest な要素がある。 -/
theorem exists_honest_of_majority {E S P C H : Finset ValidatorId}
    (hEP : E ⊆ P) (hSP : S ⊆ P) (hES : Disjoint E S) (hPC : P ⊆ C) (hCH : C ∩ H ⊆ P)
    (hHC : C.card < 2 * (C ∩ H).card) (hmaj : P.card < 2 * (E.card + S.card)) :
    ∃ v ∈ H, v ∈ E ∨ v ∈ S := by
  by_contra hno
  have hno' : ∀ v ∈ H, v ∉ E ∧ v ∉ S :=
    fun v hv => ⟨fun he => hno ⟨v, hv, Or.inl he⟩, fun hs => hno ⟨v, hv, Or.inr hs⟩⟩
  have hsub : E ∪ S ⊆ P \ H := by
    intro v hv
    rw [Finset.mem_union] at hv
    rw [Finset.mem_sdiff]
    refine ⟨?_, fun hvH => ?_⟩
    · rcases hv with hv | hv
      · exact hEP hv
      · exact hSP hv
    · rcases hv with hv | hv
      · exact (hno' v hvH).1 hv
      · exact (hno' v hvH).2 hv
  have h1 : E.card + S.card ≤ (P \ H).card := by
    rw [← Finset.card_union_of_disjoint hES]
    exact Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter P H
  have h3 : (C ∩ H).card ≤ (P ∩ H).card :=
    Finset.card_le_card (Finset.subset_inter hCH Finset.inter_subset_right)
  have h4 : (P \ H).card ≤ (C \ H).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff hPC (Finset.Subset.refl H))
  have h5 := Finset.card_sdiff_add_card_inter C H
  omega

/-! ## `NaruStd.Set` の整列(`compare` が狭義順序の型)

`Sets.lean` の `Sorted` は `ValidatorId` 専用。ここでは `compare` の `.lt` が推移的で `.gt` が逆向きの `.lt` である任意の型について、
stdlib の構築関数が狭義昇順 `SortedLt` を保つことを示し、重複が無い(`nodup`)ことに使う。 -/

/-- 狭義昇順(`compare a b = .lt`)。 -/
def SortedLt {α : Type} [Ord α] (s : NaruStd.Set α) : Prop := s.elems.Pairwise (fun a b => compare a b = .lt)

theorem SortedLt.empty {α : Type} [Ord α] : SortedLt (NaruStd.Set.empty : NaruStd.Set α) := List.Pairwise.nil

theorem SortedLt.filter {α : Type} [Ord α] {s : NaruStd.Set α} (h : SortedLt s) (p : α → Bool) : SortedLt (s.filter p) :=
  List.Pairwise.filter p h

/-- 狭義昇順で `compare a a ≠ .lt` なら重複が無い。 -/
theorem SortedLt.nodup {α : Type} [Ord α] (hirr : ∀ a : α, compare a a ≠ .lt) {s : NaruStd.Set α} (h : SortedLt s) :
    s.elems.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (List.Pairwise.imp (fun hab heq => by subst heq; exact hirr _ hab) h)

section SortedLt

variable {α : Type} [Ord α] (heq : ∀ a b : α, compare a b = .eq ↔ a = b)
  (hlt : ∀ a b c : α, compare a b = .lt → compare b c = .lt → compare a c = .lt)
  (hgt : ∀ a b : α, compare a b = .gt → compare b a = .lt)
include heq hlt hgt

/-- `insertSorted` は狭義昇順を保つ(`Sets.lean` の `sorted_insertSorted` の一般形)。 -/
theorem sortedLt_insertSorted (x : α) : ∀ l : List α,
    l.Pairwise (fun a b => compare a b = .lt) → (NaruStd.Set.insertSorted x l).Pairwise (fun a b => compare a b = .lt)
  | [], _ => by simp [NaruStd.Set.insertSorted]
  | y :: ys, hl => by
    rw [List.pairwise_cons] at hl
    obtain ⟨hy, hys⟩ := hl
    cases hc : compare x y with
    | lt =>
      simp only [NaruStd.Set.insertSorted, hc]
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr ⟨hy, hys⟩⟩
      intro b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hc
      · exact hlt x y b hc (hy b hb)
    | eq =>
      simp only [NaruStd.Set.insertSorted, hc]
      exact List.pairwise_cons.mpr ⟨hy, hys⟩
    | gt =>
      simp only [NaruStd.Set.insertSorted, hc]
      rw [List.pairwise_cons]
      refine ⟨?_, sortedLt_insertSorted x ys hys⟩
      intro b hb
      rw [mem_insertSorted heq x b ys] at hb
      rcases hb with rfl | hb
      · exact hgt _ _ hc
      · exact hy b hb

theorem SortedLt.insert {s : NaruStd.Set α} (h : SortedLt s) (x : α) : SortedLt (s.insert x) :=
  sortedLt_insertSorted heq hlt hgt x s.elems h

theorem SortedLt.foldl_insert : ∀ (l : List α) {s : NaruStd.Set α}, SortedLt s → SortedLt (l.foldl NaruStd.Set.insert s)
  | [], _, hs => hs
  | y :: ys, _, hs => by
    rw [List.foldl_cons]
    exact SortedLt.foldl_insert ys (SortedLt.insert heq hlt hgt hs y)

theorem SortedLt.of (l : List α) : SortedLt (NaruStd.Set.of l) :=
  SortedLt.foldl_insert heq hlt hgt l SortedLt.empty

theorem SortedLt.toSet (l : List α) : SortedLt (NaruStd.List.toSet l) := SortedLt.of heq hlt hgt l

end SortedLt

/-! ## `GoldfishVote` の順序(派生 `Ord`: 投票者・slot・head の辞書式) -/

theorem then_eq_lt_iff (o p : Ordering) : o.then p = .lt ↔ o = .lt ∨ (o = .eq ∧ p = .lt) := by
  cases o <;> cases p <;> decide

theorem then_eq_gt_iff (o p : Ordering) : o.then p = .gt ↔ o = .gt ∨ (o = .eq ∧ p = .gt) := by
  cases o <;> cases p <;> decide

theorem bid_compare (a b : BlockId) : compare a b = compare a.value b.value := by
  cases a with
  | mk x =>
    cases b with
    | mk y => exact then_eq _

/-- 派生 `Ord GoldfishVote` は (投票者の番号, slot, head の番号) の辞書式順序。 -/
theorem gv_compare (a b : GoldfishVote) :
    compare a b = (compare a.valIndex.value b.valIndex.value).then
      ((compare a.slot b.slot).then (compare a.head.value b.head.value)) := by
  cases a with
  | mk v1 s1 h1 =>
    cases b with
    | mk v2 s2 h2 =>
      show (compare v1 v2).then ((compare s1 s2).then ((compare h1 h2).then .eq)) = _
      rw [then_eq, vid_compare, bid_compare]

theorem gv_lt_iff (a b : GoldfishVote) : compare a b = .lt ↔
    a.valIndex.value < b.valIndex.value ∨ (a.valIndex.value = b.valIndex.value ∧
      (a.slot < b.slot ∨ (a.slot = b.slot ∧ a.head.value < b.head.value))) := by
  simp only [gv_compare, then_eq_lt_iff, Nat.compare_eq_lt, Nat.compare_eq_eq]

theorem gv_gt_iff (a b : GoldfishVote) : compare a b = .gt ↔
    b.valIndex.value < a.valIndex.value ∨ (a.valIndex.value = b.valIndex.value ∧
      (b.slot < a.slot ∨ (a.slot = b.slot ∧ b.head.value < a.head.value))) := by
  simp only [gv_compare, then_eq_gt_iff, Nat.compare_eq_gt, Nat.compare_eq_eq]

theorem gv_lt_trans (a b c : GoldfishVote) (h1 : compare a b = .lt) (h2 : compare b c = .lt) : compare a c = .lt := by
  rw [gv_lt_iff] at h1 h2 ⊢
  omega

theorem gv_gt_lt (a b : GoldfishVote) (h : compare a b = .gt) : compare b a = .lt := by
  rw [gv_gt_iff] at h
  rw [gv_lt_iff]
  omega

theorem gv_irrefl (a : GoldfishVote) : compare a a ≠ .lt := by
  intro h
  rw [gv_lt_iff] at h
  omega

/-- pool の投票の集合は整列(`List.toSet`)。 -/
theorem storePool_sortedLt (st : Store) (k : Nat) : SortedLt (storePool st k) := by
  unfold storePool
  exact SortedLt.toSet gv_compare_eq_iff gv_lt_trans gv_gt_lt _

theorem supportVotes_sortedLt (e : ProtocolEnv) (st : Store) (s : Nat) : SortedLt (supportVotes e st s) := by
  unfold supportVotes earlyVotes
  exact SortedLt.filter (SortedLt.filter (storePool_sortedLt st s) _) _

/-! ## `NaruStd.Set ValidatorId` と `Finset` の橋 -/

/-- 投票者の集合 `voters`(`Set.map`)は整列。 -/
theorem sorted_voters (votes : NaruStd.Set GoldfishVote) : Sorted (voters votes) := by
  unfold voters NaruStd.Set.map
  exact Sorted.of _

/-- 整列した集合の大きさは `toFinset` の濃度。 -/
theorem size_eq_card {s : VSet} (hs : Sorted s) : s.size = s.elems.toFinset.card :=
  (List.toFinset_card_of_nodup hs.nodup).symm

/-! ## equivocator・参加者・投票者 -/

theorem mem_rawEquivocators_iff (votes : NaruStd.Set GoldfishVote) (v : ValidatorId) :
    v ∈ (rawEquivocators votes).elems ↔ v ∈ (voters votes).elems ∧ equivocates votes v = true := by
  unfold rawEquivocators
  exact mem_filter_iff _ _ _

theorem mem_rawParticipants_iff (votes : NaruStd.Set GoldfishVote) (v : ValidatorId) :
    v ∈ (rawParticipants votes).elems ↔ v ∈ (voters votes).elems ∧ participates votes v = true := by
  unfold rawParticipants
  exact mem_filter_iff _ _ _

/-- 投票者は参加者。 -/
theorem mem_rawParticipants_of_voters {votes : NaruStd.Set GoldfishVote} {v : ValidatorId}
    (hv : v ∈ (voters votes).elems) : v ∈ (rawParticipants votes).elems := by
  rw [mem_rawParticipants_iff]
  obtain ⟨u, hu, hvi⟩ := (mem_voters_iff votes v).mp hv
  exact ⟨hv, participates_of_mem hu hvi⟩

/-- 投票の集合が大きくなれば投票者の集合も大きくなる。 -/
theorem voters_mono {a b : NaruStd.Set GoldfishVote} (hab : ∀ u ∈ a.elems, u ∈ b.elems) {v : ValidatorId}
    (hv : v ∈ (voters a).elems) : v ∈ (voters b).elems := by
  rw [mem_voters_iff] at hv ⊢
  obtain ⟨u, hu, hvi⟩ := hv
  exact ⟨u, hab u hu, hvi⟩

/-! ## 時刻の印: 支持の投票は遅い投票 -/

/-- 印 `x` が `γ` より前: `Bottom`(genesis)か、`γ` より小さい時刻。 -/
theorem stampBefore_iff (x : Stamp) (γ : Int) :
    stampBefore x γ = true ↔ x = Stamp.Bottom ∨ ∃ a, x = Stamp.At a ∧ a < γ := by
  cases x with
  | Bottom =>
    unfold stampBefore
    rw [show compare Stamp.Bottom (Stamp.At γ) = .lt from rfl]
    simp
  | At a =>
    unfold stampBefore
    rw [show compare (Stamp.At a) (Stamp.At γ) = compare a γ from then_eq _, beq_iff_eq, Int.compare_eq_lt]
    simp

/-- `occurrenceMax` の中身(2 つの印の大きい方)が `γ` より前なら、左の印は `γ' ≥ γ` より前。 -/
theorem stampBefore_of_max {a b : Stamp} {γ γ' : Int}
    (h : stampBefore (if compare a b == .lt then b else a) γ = true) (hγ : γ ≤ γ') :
    stampBefore a γ' = true := by
  rw [stampBefore_iff] at h ⊢
  split_ifs at h with hab
  · cases a with
    | Bottom => exact Or.inl rfl
    | At a' =>
      cases b with
      | Bottom =>
        rw [show compare (Stamp.At a') Stamp.Bottom = .gt from rfl] at hab
        exact absurd hab (by decide)
      | At b' =>
        rw [show compare (Stamp.At a') (Stamp.At b') = compare a' b' from then_eq _, beq_iff_eq,
          Int.compare_eq_lt] at hab
        rcases h with h | ⟨bb, hbb, hlt⟩
        · exact absurd h (by simp)
        · rw [Stamp.At.injEq] at hbb
          subst hbb
          exact Or.inr ⟨a', rfl, by omega⟩
  · rcases h with h | ⟨aa, haa, hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨aa, haa, by omega⟩

/-- 解決の印 `storeTau`(受信の印と head のブロックの受信の印の大きい方)が `γ` より前なら、投票の受信の印は `γ' ≥ γ` より前。 -/
theorem timestampVote_before_of_tau {st : Store} {u : GoldfishVote} {γ γ' : Int}
    (h : occurrenceBefore (storeTau st u) γ = true) (hγ : γ ≤ γ') :
    occurrenceBefore (NaruStd.Table.get? st.timestampVote u) γ' = true := by
  unfold storeTau resolutionTime at h
  cases hr : findRoot? st.tree u.head with
  | none =>
    rw [hr] at h
    exact absurd h (by simp [occurrenceBefore])
  | some hd =>
    rw [hr] at h
    dsimp only at h
    split_ifs at h with hs
    · unfold occurrenceMax at h
      cases hv : NaruStd.Table.get? st.timestampVote u with
      | none =>
        rw [hv] at h
        exact absurd h (by simp [occurrenceBefore])
      | some a =>
        rw [hv] at h
        cases hb : NaruStd.Table.get? st.timestampBlock hd with
        | none =>
          rw [hb] at h
          exact absurd h (by simp [occurrenceBefore])
        | some b =>
          rw [hb] at h
          dsimp only [occurrenceBefore] at h ⊢
          exact stampBefore_of_max h hγ
    · exact absurd h (by simp [occurrenceBefore])

theorem supportCutoff_le_confirmationTime (e : ProtocolEnv) (s : Nat) (hδ : 0 ≤ e.delta) :
    supportCutoff e s ≤ confirmationTime e s := by
  unfold supportCutoff confirmationTime
  linarith

/-- 支持の投票(`supportCutoff` までに解決した slot `s` の投票)は遅い投票(`confirmationTime` までに受信)。手書き `Numerator.subset_late`。 -/
theorem supportVotes_sub_lateVotes (e : ProtocolEnv) (st : Store) (s : Nat) (hδ : 0 ≤ e.delta) :
    ∀ u ∈ (supportVotes e st s).elems, u ∈ (lateVotes e st s).elems := by
  intro u hu
  unfold supportVotes at hu
  obtain ⟨hu, -⟩ := (mem_filter_iff _ _ _).mp hu
  unfold earlyVotes at hu
  obtain ⟨hpool, hτ⟩ := (mem_filter_iff _ _ _).mp hu
  unfold lateVotes
  rw [mem_filter_iff]
  exact ⟨hpool, timestampVote_before_of_tau hτ (supportCutoff_le_confirmationTime e s hδ)⟩

theorem lateVotes_sub_pool (e : ProtocolEnv) (st : Store) (s : Nat) :
    ∀ u ∈ (lateVotes e st s).elems, u ∈ (storePool st s).elems := by
  intro u hu
  unfold lateVotes at hu
  exact ((mem_filter_iff _ _ _).mp hu).1

/-- pool の不変条件の下で、支持の投票の投票者は slot `s` の committee の要素。 -/
theorem supportVotes_committee {c : Nat → NaruStd.Set ValidatorId} {st : Store} (hinv : PoolInv c st) {e : ProtocolEnv}
    {s : Nat} (hδ : 0 ≤ e.delta) {u : GoldfishVote} (hu : u ∈ (supportVotes e st s).elems) : u.valIndex ∈ (c s).elems :=
  (hinv.mem (lateVotes_sub_pool e st s u (supportVotes_sub_lateVotes e st s hδ u hu))).2

/-- pool の不変条件の下で、遅い投票の参加者は slot `s` の committee の要素。手書き `voters_count_le_committee` の所属の形。 -/
theorem participants_sub_committee {c : Nat → NaruStd.Set ValidatorId} {st : Store} (hinv : PoolInv c st)
    (e : ProtocolEnv) (s : Nat) : ∀ v ∈ (rawParticipants (lateVotes e st s)).elems, v ∈ (c s).elems := by
  intro v hv
  obtain ⟨hv, -⟩ := (mem_rawParticipants_iff _ _).mp hv
  obtain ⟨u, hu, hvi⟩ := (mem_voters_iff _ _).mp hv
  obtain ⟨-, hmem⟩ := hinv.mem (lateVotes_sub_pool e st s u hu)
  rw [← hvi]
  exact hmem

/-! ## 支持の投票は投票者ごとに 1 つ -/

/-- 支持の投票の中では同じ投票者の投票は 1 つ: `noSecondVoteIn lateVotes` の絞り込みと支持の投票が遅い投票であることから。
手書き `Numerator.unique_in_late`。 -/
theorem supportVotes_unique (e : ProtocolEnv) (st : Store) (s : Nat) (hδ : 0 ≤ e.delta) {u u' : GoldfishVote}
    (hu : u ∈ (supportVotes e st s).elems) (hu' : u' ∈ (supportVotes e st s).elems) (hv : u'.valIndex = u.valIndex) :
    u' = u := by
  have hlate := supportVotes_sub_lateVotes e st s hδ u' hu'
  unfold supportVotes at hu
  obtain ⟨-, hno⟩ := (mem_filter_iff _ _ _).mp hu
  unfold noSecondVoteIn NaruStd.Set.all at hno
  rw [List.all_eq_true] at hno
  have h := hno u' hlate
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
  rcases h with h | h
  · exact h
  · exact absurd hv h

/-- 重複が無く要素がすべて等しいリストの長さは 1 以下。 -/
theorem length_le_one_of_nodup {β : Type} {l : List β} (hnd : l.Nodup) (hall : ∀ a ∈ l, ∀ b ∈ l, a = b) :
    l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons a t =>
    cases t with
    | nil => simp
    | cons b t' =>
      exfalso
      rw [List.nodup_cons] at hnd
      have hab : a = b := hall a (List.mem_cons_self ..) b (List.mem_cons_of_mem a (List.mem_cons_self ..))
      subst hab
      exact hnd.1 (List.mem_cons_self ..)

/-- **支持の投票に equivocator は無い**(どの validator についても)。手書き `Numerator.no_equivocation`。 -/
theorem supportVotes_no_equivocation (e : ProtocolEnv) (st : Store) (s : Nat) (hδ : 0 ≤ e.delta) (v : ValidatorId) :
    equivocates (supportVotes e st s) v = false := by
  unfold equivocates
  rw [decide_eq_false_iff_not]
  intro h2
  have hnd : (votesBy (supportVotes e st s) v).elems.Nodup := by
    unfold votesBy
    exact SortedLt.nodup gv_irrefl (SortedLt.filter (supportVotes_sortedLt e st s) _)
  have hle : (votesBy (supportVotes e st s) v).elems.length ≤ 1 := by
    apply length_le_one_of_nodup hnd
    intro a ha b hb
    rw [mem_votesBy_iff] at ha hb
    exact supportVotes_unique e st s hδ hb.1 ha.1 (ha.2.trans hb.2.symm)
  unfold NaruStd.Set.size at h2
  omega

/-- 支持の投票の equivocator の集合は空。 -/
theorem rawEquivocators_supportVotes (e : ProtocolEnv) (st : Store) (s : Nat) (hδ : 0 ≤ e.delta) :
    (rawEquivocators (supportVotes e st s)).elems = [] := by
  unfold rawEquivocators NaruStd.Set.filter
  rw [List.filter_eq_nil_iff]
  intro v _ hv
  rw [supportVotes_no_equivocation e st s hδ v] at hv
  exact Bool.false_ne_true hv

/-- 確認の得点は支持者の数そのもの。手書き `Numerator.score_eq_supporters`。 -/
theorem score_eq_supporters (e : ProtocolEnv) (st : Store) (s : Nat) (b : Block) (hδ : 0 ≤ e.delta) :
    Proofs.Consensus.Goldfish.score e st s b =
      (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s b).size := by
  show (rawEquivocators (supportVotes e st s)).size +
    (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s b).size = _
  unfold NaruStd.Set.size
  rw [rawEquivocators_supportVotes e st s hδ]
  simp

/-! ## 門を通るブロックの honest な支持者 -/

/-- **門 `lateCount < 2 · score b` を通るブロックには honest な支持者がいる**: honest な支持者 `v` とその投票 `u`(slot `s`、`b` 以下を指す)。
前提: `0 ≤ Δ`、pool の不変条件、slot `s` の committee が整列(`SetupWellFormed` の `normalizedValidators`)、`HonestCommittees` の
slot `s` での不等式、honest な committee の要素がすべて遅い投票の参加者であること(`HonestSupport.participants`)。 -/
theorem exists_honest_supporter {c : Nat → NaruStd.Set ValidatorId} (e : ProtocolEnv) {st : Store} (s : Nat) (b : Block)
    (H : VSet) (hδ : 0 ≤ e.delta) (hinv : PoolInv c st) (hsorted : Sorted (c s))
    (hcom : (c s).size < 2 * ((c s).inter H).size)
    (hall : ∀ v ∈ (c s).elems, v ∈ H.elems → v ∈ (rawParticipants (lateVotes e st s)).elems)
    (hmaj : lateCount e st s < 2 * Proofs.Consensus.Goldfish.score e st s b) :
    ∃ v u, v ∈ H.elems ∧ u ∈ (supportVotes e st s).elems ∧ u.valIndex = v ∧ u.slot = s ∧
      targetsUnder st.tree b u = true := by
  have hE : Sorted (rawEquivocators (supportVotes e st s)) := by
    unfold rawEquivocators
    exact Sorted.filter (sorted_voters _) _
  have hS : Sorted (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s b) := by
    unfold rawSupporters
    exact Sorted.filter (sorted_voters _) _
  have hP : Sorted (rawParticipants (lateVotes e st s)) := by
    unfold rawParticipants
    exact Sorted.filter (sorted_voters _) _
  have hsub := supportVotes_sub_lateVotes e st s hδ
  have hEP : (rawEquivocators (supportVotes e st s)).elems.toFinset ⊆
      (rawParticipants (lateVotes e st s)).elems.toFinset := by
    intro v hv
    rw [List.mem_toFinset] at hv ⊢
    exact mem_rawParticipants_of_voters (voters_mono hsub ((mem_rawEquivocators_iff _ _).mp hv).1)
  have hSP : (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s b).elems.toFinset ⊆
      (rawParticipants (lateVotes e st s)).elems.toFinset := by
    intro v hv
    rw [List.mem_toFinset] at hv ⊢
    exact mem_rawParticipants_of_voters (voters_mono hsub ((mem_rawSupporters_iff _ _ _ _ _ _).mp hv).1)
  have hES : Disjoint (rawEquivocators (supportVotes e st s)).elems.toFinset
      (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s b).elems.toFinset := by
    rw [Finset.disjoint_left]
    intro v hvE hvS
    rw [List.mem_toFinset] at hvE hvS
    have h1 := ((mem_rawEquivocators_iff _ _).mp hvE).2
    have h2 := ((mem_rawSupporters_iff _ _ _ _ _ _).mp hvS).2.1
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hPC : (rawParticipants (lateVotes e st s)).elems.toFinset ⊆ (c s).elems.toFinset := by
    intro v hv
    rw [List.mem_toFinset] at hv ⊢
    exact participants_sub_committee hinv e s v hv
  have hCH : (c s).elems.toFinset ∩ H.elems.toFinset ⊆ (rawParticipants (lateVotes e st s)).elems.toFinset := by
    intro v hv
    rw [Finset.mem_inter, List.mem_toFinset, List.mem_toFinset] at hv
    rw [List.mem_toFinset]
    exact hall v hv.1 hv.2
  have hHC : (c s).elems.toFinset.card < 2 * ((c s).elems.toFinset ∩ H.elems.toFinset).card := by
    rw [← toFinset_inter, ← size_eq_card hsorted, ← size_eq_card (hsorted.inter H)]
    exact hcom
  have hmaj' : (rawParticipants (lateVotes e st s)).elems.toFinset.card <
      2 * ((rawEquivocators (supportVotes e st s)).elems.toFinset.card +
        (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s b).elems.toFinset.card) := by
    rw [← size_eq_card hP, ← size_eq_card hE, ← size_eq_card hS]
    exact hmaj
  obtain ⟨v, hvH, hv⟩ := exists_honest_of_majority hEP hSP hES hPC hCH hHC hmaj'
  rw [List.mem_toFinset] at hvH
  rcases hv with hv | hv
  · exfalso
    rw [List.mem_toFinset, rawEquivocators_supportVotes e st s hδ] at hv
    exact absurd hv List.not_mem_nil
  · rw [List.mem_toFinset] at hv
    obtain ⟨-, -, u, hu, hvi, hs, ht⟩ := (mem_rawSupporters_iff _ _ _ _ _ _).mp hv
    exact ⟨v, u, hvH, hu, hvi, hs, ht⟩

/-- `updateConfirmationWith` の適格の判定 `eligible`(`lateCount < 2 · score`)から。 -/
theorem exists_honest_supporter_of_eligible {c : Nat → NaruStd.Set ValidatorId} (e : ProtocolEnv) {st : Store} (s : Nat)
    (b : Block) (H : VSet) (hδ : 0 ≤ e.delta) (hinv : PoolInv c st) (hsorted : Sorted (c s))
    (hcom : (c s).size < 2 * ((c s).inter H).size)
    (hall : ∀ v ∈ (c s).elems, v ∈ H.elems → v ∈ (rawParticipants (lateVotes e st s)).elems)
    (hel : Proofs.Consensus.Goldfish.eligible e st s b = true) :
    ∃ v u, v ∈ H.elems ∧ u ∈ (supportVotes e st s).elems ∧ u.valIndex = v ∧ u.slot = s ∧
      targetsUnder st.tree b u = true :=
  exists_honest_supporter e s b H hδ hinv hsorted hcom hall ((eligible_iff e st s b).mp hel)

/-- fork choice の head が SG root から降りていれば(`head_cases`)、head には honest な支持者がいる。 -/
theorem exists_honest_supporter_of_head {c : Nat → NaruStd.Set ValidatorId} (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    {st : Store} (s : Nat) (H : VSet) (hδ : 0 ≤ e.delta) (hinv : PoolInv c st) (hsorted : Sorted (c s))
    (hcom : (c s).size < 2 * ((c s).inter H).size)
    (hall : ∀ v ∈ (c s).elems, v ∈ H.elems → v ∈ (rawParticipants (lateVotes e st s)).elems)
    (hne : Proofs.Consensus.Goldfish.head cache e hc st s ≠ sgRoot cache e hc st) :
    ∃ v u, v ∈ H.elems ∧ u ∈ (supportVotes e st s).elems ∧ u.valIndex = v ∧ u.slot = s ∧
      targetsUnder st.tree (Proofs.Consensus.Goldfish.head cache e hc st s) u = true := by
  rcases head_cases cache e hc st s with h | ⟨-, hmaj⟩
  · exact absurd h hne
  · exact exists_honest_supporter e s _ H hδ hinv hsorted hcom hall hmaj

/-! ## honest な支持 `HonestSupport`(手書き `Confirmation.lean` と同じ形) -/

/-- slot `s` の committee は honest 過半で、honest な committee の要素はみな支持の投票に `B` 以下を指す slot `s` の投票を持つ。
`majority` は `HonestCommittees` の slot `s` での不等式、`vote` は同期性の議論の結論(次の層で `SleepyRegime` から示す)。
手書き `Confirmation.lean` の `HonestSupport` は `vote` に「投票が `B` にちょうど解決する」(`find? T u.head = some B ∧ B.slot ≤ u.slot`)を
要求するが、ここでは `B` 以下を指す `targetsUnder` に弱めた(弱いぶん regime から出しやすい。結論は `compatible_of_eligible` の互換まで)。 -/
structure HonestSupport (c : Nat → NaruStd.Set ValidatorId) (e : ProtocolEnv) (st : Store) (s : Nat) (H : VSet)
    (B : Block) : Prop where
  majority : (c s).size < 2 * ((c s).inter H).size
  vote : ∀ v ∈ (c s).elems, v ∈ H.elems →
    ∃ u ∈ (supportVotes e st s).elems, u.valIndex = v ∧ u.slot = s ∧ targetsUnder st.tree B u = true

namespace HonestSupport

variable {c : Nat → NaruStd.Set ValidatorId} {e : ProtocolEnv} {st : Store} {s : Nat} {H : VSet} {B : Block}

/-- honest な committee の要素は遅い投票の参加者(`exists_honest_supporter` の前提 `hall`)。 -/
theorem participants (h : HonestSupport c e st s H B) (hδ : 0 ≤ e.delta) :
    ∀ v ∈ (c s).elems, v ∈ H.elems → v ∈ (rawParticipants (lateVotes e st s)).elems := by
  intro v hc hH
  obtain ⟨u, hu, hvi, -, -⟩ := h.vote v hc hH
  exact mem_rawParticipants_of_voters ((mem_voters_iff _ _).mpr ⟨u, supportVotes_sub_lateVotes e st s hδ u hu, hvi⟩)

/-- honest な committee の要素はみな `B` の支持者。手書き `HonestSupport.subset_supporters`。 -/
theorem supporters (h : HonestSupport c e st s H B) (hδ : 0 ≤ e.delta) :
    ∀ v ∈ (c s).elems, v ∈ H.elems →
      v ∈ (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s B).elems := by
  intro v hc hH
  obtain ⟨u, hu, hvi, hs, ht⟩ := h.vote v hc hH
  rw [mem_rawSupporters_iff]
  exact ⟨(mem_voters_iff _ _).mpr ⟨u, hu, hvi⟩, supportVotes_no_equivocation e st s hδ v, u, hu, hvi, hs, ht⟩

/-- **`B` は門を通る**(`lateCount < 2 · score B`): 参加者は committee の要素(`|P| ≤ |C|`)、honest な committee の要素はみな支持者
(`|C ∩ H| ≤ |S|`)、committee は honest 過半(`|C| < 2 |C ∩ H|`)。手書き `HonestSupport.eligible`。 -/
theorem eligible (h : HonestSupport c e st s H B) (hδ : 0 ≤ e.delta) (hinv : PoolInv c st) (hsorted : Sorted (c s)) :
    lateCount e st s < 2 * Proofs.Consensus.Goldfish.score e st s B := by
  have hP : Sorted (rawParticipants (lateVotes e st s)) := by
    unfold rawParticipants
    exact Sorted.filter (sorted_voters _) _
  have hS : Sorted (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s B) := by
    unfold rawSupporters
    exact Sorted.filter (sorted_voters _) _
  have h1 : (rawParticipants (lateVotes e st s)).size ≤ (c s).size := by
    rw [size_eq_card hP, size_eq_card hsorted]
    apply Finset.card_le_card
    intro v hv
    rw [List.mem_toFinset] at hv ⊢
    exact participants_sub_committee hinv e s v hv
  have h2 : ((c s).inter H).size ≤ (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s B).size := by
    rw [size_eq_card (hsorted.inter H), size_eq_card hS, toFinset_inter]
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_inter, List.mem_toFinset, List.mem_toFinset] at hv
    rw [List.mem_toFinset]
    exact h.supporters hδ v hv.1 hv.2
  have h3 := h.majority
  show (rawParticipants (lateVotes e st s)).size < 2 * ((rawEquivocators (supportVotes e st s)).size +
    (rawSupporters st.tree (supportVotes e st s) (supportVotes e st s) s B).size)
  omega

/-- `B` の祖先 `C` も門を通る(得点は祖先ほど大きい `goldfishScore_mono`)。手書き `HonestSupport.eligible` は `B` の祖先全体について述べる。 -/
theorem eligible_of_preceq (h : HonestSupport c e st s H B) (hδ : 0 ≤ e.delta) (hinv : PoolInv c st) (hsorted : Sorted (c s))
    {C : Block} (hCB : preceq C B = true) : lateCount e st s < 2 * Proofs.Consensus.Goldfish.score e st s C := by
  have h1 := h.eligible hδ hinv hsorted
  have h2 : Proofs.Consensus.Goldfish.score e st s B ≤ Proofs.Consensus.Goldfish.score e st s C :=
    Proofs.Consensus.Goldfish.goldfishScore_mono e hCB
  omega

/-- **門を通るどのブロックも `B` と互換**: `C` の honest な支持者 `v` の投票 `u` は、支持の投票が投票者ごとに 1 つなので `B` 以下も指し、
`C` と `B` はともに `u` の head の祖先。手書き `HonestSupport.not_eligible`(`B` と競合するブロックは門を通らない)より弱い形
(`vote` を `B` 以下を指す形に弱めたので、`B` の子孫も門を通りうる。結論は互換)。 -/
theorem compatible_of_eligible (h : HonestSupport c e st s H B) (hδ : 0 ≤ e.delta) (hinv : PoolInv c st)
    (hsorted : Sorted (c s)) {C : Block} (hC : lateCount e st s < 2 * Proofs.Consensus.Goldfish.score e st s C) :
    compatible C B = true := by
  obtain ⟨v, u, hvH, hu, hvi, -, htC⟩ :=
    exists_honest_supporter e s C H hδ hinv hsorted h.majority (h.participants hδ) hC
  have hvc : v ∈ (c s).elems := by
    rw [← hvi]
    exact supportVotes_committee hinv hδ hu
  obtain ⟨u', hu', hvi', -, htB⟩ := h.vote v hvc hvH
  have heq : u' = u := supportVotes_unique e st s hδ hu hu' (hvi'.trans hvi.symm)
  subst heq
  rw [targetsUnder_iff] at htC htB
  obtain ⟨x, hx, -, hCx⟩ := htC
  obtain ⟨y, hy, -, hBy⟩ := htB
  rw [hx, Option.some.injEq] at hy
  subst hy
  exact compatible_of_preceq_common hCx hBy

end HonestSupport

/-! ## regime の前提からの形 -/

/-- `SetupWellFormed` から各 slot の committee は整列(`normalizedValidators`)。 -/
theorem committee_sorted {c : Nat → NaruStd.Set ValidatorId} {p : Nat → ValidatorId}
    {s : Model.Consensus.Execution.Setup.Setup} (hwf : SetupWellFormed c p s) (k : Nat) : Sorted (c k) := by
  unfold SetupWellFormed at hwf
  obtain ⟨-, hk⟩ := hwf
  obtain ⟨⟨⟨-, hn⟩, -⟩, -⟩ := hk k
  exact Proofs.Consensus.Weights.sorted_of_normalized hn

/-- `HonestCommittees` の slot `k` での不等式。 -/
theorem honestCommittees_at {c : Nat → NaruStd.Set ValidatorId} {H : VSet} (h : HonestCommittees c H) (k : Nat) :
    (c k).size < 2 * ((c k).inter H).size := by
  unfold HonestCommittees at h
  exact h k

/-- `SetupWellFormed` と `HonestCommittees` の下で、run のどの読みの store でも: honest な committee の要素がすべて遅い投票の参加者なら、
門を通る `b` には honest な支持者がいる。tick の途中の store(`updateConfirmationWith` が実際に読む store)については
`Votes.lean` の `*_poolExt'` から同じ `PoolInv` が出る。 -/
theorem exists_honest_supporter_of_run {c : Nat → NaruStd.Set ValidatorId} {p : Nat → ValidatorId}
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) {setup : Model.Consensus.Execution.Setup.Setup}
    (hwf : SetupWellFormed c p setup) (rho : Model.Consensus.Execution.Run.NamedRun) (hhc : HonestCommittees c rho.honest)
    (v : ValidatorId) (t : Int) (s : Nat) (b : Block)
    (hall : ∀ w ∈ (c s).elems, w ∈ rho.honest.elems →
      w ∈ (rawParticipants (lateVotes setup.e (Model.Consensus.Execution.Run.storeAt c p a nr setup rho v t).core s)).elems)
    (hmaj : lateCount setup.e (Model.Consensus.Execution.Run.storeAt c p a nr setup rho v t).core s <
      2 * Proofs.Consensus.Goldfish.score setup.e (Model.Consensus.Execution.Run.storeAt c p a nr setup rho v t).core s b) :
    ∃ w u, w ∈ rho.honest.elems ∧
      u ∈ (supportVotes setup.e (Model.Consensus.Execution.Run.storeAt c p a nr setup rho v t).core s).elems ∧
      u.valIndex = w ∧ u.slot = s ∧
      targetsUnder (Model.Consensus.Execution.Run.storeAt c p a nr setup rho v t).core.tree b u = true :=
  exists_honest_supporter setup.e s b rho.honest (le_of_lt (Proofs.Consensus.Liveness.wf_facts hwf).1)
    (storeAt_pool c p a nr setup rho v t) (committee_sorted hwf s) (honestCommittees_at hhc s) hall hmaj

end Proofs.Consensus.Majority
