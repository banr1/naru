import Proofs.Consensus.BlockStamps
import Proofs.Consensus.GradeSupporter
import Mathlib.Tactic

/-!
# SG 票の行と受信の印は run に沿って残る(C77 の補題)

store の SG 票の表 `sgVotes`(round を鍵にした `CombinedAttestation` のリスト)と受信の印の表 `timestampSgVote`(`sgVote a` を鍵にする)を
書くのは `onSgVote`(`Model/Consensus/Protocol/Handlers.lean`)の受理の分岐だけで、attestation `a` を鍵 `a.round` の行の末尾に足し、
`sgVote a` の印を現在の時計にする。受理の守りは「同じ round・同じ送り手の行に同じ `confirmed` が既にある」なら store を変えないので、
行の要素の round が鍵と一致していれば(`SgInv`)、既にある票の印は書き換わらない。したがって
- **行の不変条件** `SgInv st`: 鍵 `k` の行の attestation は round が `k`。
- **行と印の保存** `SgKeep a b`: `a` の行の attestation は `b` の同じ行にも残り、その `sgVote` の印は変わらない。
どのハンドラも不変条件を運び、不変条件の下で保存を満たす(`Step`)。初期の store は表が空なので、run のどの添字の store でも
不変条件が成り立ち(`stateBefore_sgInv`)、添字について行と印が残る(`stateBefore_sgKeep`)。grade の読み(`gradeView` の
`sgVotes` は行の `sgVote` の集合)では、生の入力 `rawInputs` が後の store と遅い cutoff に持ち越せる(`rawInputs_of_keep`)。

手書きでは `strict_sg_row_carry`(`Protocol/Grades/Q10Frame.lean`。SG 票の行と印が strict read の間で残る)に当たる。運びは
`BlockStamps`(tree のブロックとその印)と同じ。
-/

namespace Proofs.Consensus.SgStamps

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Time Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.StoreBase
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Protocol.ForkChoice.Goldfish (SGVote)
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Orders Proofs.Consensus.Tables Proofs.Consensus.Sets Proofs.Consensus.Carrier

/-! ## SG 票を鍵にした表 -/

/-- `SGVote` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem sgv_compare_eq_iff (a b : SGVote) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk v r c =>
    cases b with
    | mk v' r' c' =>
      show (compare v v').then ((compare r r').then ((compare c c').then .eq)) = .eq ↔ _
      rw [then_eq_eq, then_eq_eq, then_eq, vid_compare_eq_iff, Nat.compare_eq_eq, opt_compare_eq_iff bid_compare_eq_iff,
        SGVote.mk.injEq]

theorem sgv_get?_insert_ne {ν : Type} (t : NaruStd.Table SGVote ν) (k : SGVote) (v : ν) (k' : SGVote)
    (hne : k ≠ k') : (t.insert k v).get? k' = t.get? k' := by
  have htr : ∀ a b c : SGVote, compare a b = .eq → compare b c = .eq → compare a c = .eq := fun a b c hab hbc => by
    rw [sgv_compare_eq_iff] at hab hbc ⊢
    exact hab.trans hbc
  rcases find?_insertSorted htr k v k' t.entries with ⟨hk, _⟩ | hf
  · exact absurd ((sgv_compare_eq_iff k k').mp hk) hne
  · simp [NaruStd.Table.get?, NaruStd.Table.insert, hf]

/-! ## 行の不変条件と、行と印の保存 -/

/-- 鍵 `k` の行(`sgVotes` の元のリスト)。 -/
def rows (st : Store) (k : Nat) : List CombinedAttestation := NaruStd.Table.getOr st.sgVotes k []

/-- 行の不変条件: 鍵 `k` の行の attestation は round が `k`。 -/
def SgInv (st : Store) : Prop := ∀ k x, x ∈ rows st k → x.round = k

/-- 行と印の保存: `a` の行の attestation は `b` の同じ行にも残り、その `sgVote` の受信の印は変わらない。 -/
def SgKeep (a b : Store) : Prop :=
  ∀ k x, x ∈ rows a k → x ∈ rows b k ∧ b.timestampSgVote.get? (sgVote x) = a.timestampSgVote.get? (sgVote x)

/-- ハンドラの 1 段: 不変条件を運び、不変条件の下で行と印を保存する。 -/
structure Step (a b : Store) : Prop where
  inv : SgInv a → SgInv b
  keep : SgInv a → SgKeep a b

theorem SgKeep.refl (a : Store) : SgKeep a a := fun _ _ h => ⟨h, rfl⟩

theorem SgKeep.trans {a b d : Store} (h1 : SgKeep a b) (h2 : SgKeep b d) : SgKeep a d := fun k x h => by
  obtain ⟨hb, hb'⟩ := h1 k x h
  obtain ⟨hd, hd'⟩ := h2 k x hb
  exact ⟨hd, hd'.trans hb'⟩

theorem Step.refl (a : Store) : Step a a := ⟨id, fun _ => SgKeep.refl a⟩

theorem Step.trans {a b d : Store} (h1 : Step a b) (h2 : Step b d) : Step a d :=
  ⟨fun h => h2.inv (h1.inv h), fun h => (h1.keep h).trans (h2.keep (h1.inv h))⟩

/-- SG 票の表と印の表が等しい store の間は 1 段(何も変わらない)。 -/
theorem Step.of_same {a b : Store} (hsv : b.sgVotes = a.sgVotes) (hts : b.timestampSgVote = a.timestampSgVote) :
    Step a b := by
  have hr : ∀ k, rows b k = rows a k := fun k => by unfold rows; rw [hsv]
  exact ⟨fun h k x hx => h k x (by rw [← hr]; exact hx), fun _ k x hx => ⟨by rw [hr]; exact hx, by rw [hts]⟩⟩

/-! ## `Store` のハンドラ -/

theorem onGoldfishVote_step (st : Store) (x : GoldfishVote) : Step st (onGoldfishVote st x) := by
  unfold onGoldfishVote
  split_ifs <;> exact Step.of_same rfl rfl

theorem onGoldfishVoteChecked_step (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    Step st (onGoldfishVoteChecked c st u) := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact Step.refl st
  · exact onGoldfishVote_step st u

theorem foldl_step {β : Type} (g : Store → β → Store) (hg : ∀ s x, Step s (g s x)) :
    ∀ (l : List β) (s : Store), Step s (List.foldl g s l)
  | [], _ => Step.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (hg s x).trans (foldl_step g hg l (g s x))

/-- 受理された attestation `a` の行は鍵 `a.round` の行の末尾に `a` を足したもの、他の行は変わらない。 -/
theorem rows_insert (st : Store) (a : CombinedAttestation) (k : Nat) :
    NaruStd.Table.getOr (st.sgVotes.insert a.round (NaruStd.Table.getOr st.sgVotes a.round [] ++ [a])) k [] =
      if a.round = k then rows st a.round ++ [a] else rows st k := by
  split_ifs with hk
  · subst hk
    exact getOr_insert_self Proofs.Consensus.Records.nat_compare_eq_iff _ _ _ _
  · exact getOr_insert_ne Proofs.Consensus.Records.nat_compare_eq_iff _ _ _ _ _ hk

/-- `onSgVote` は 1 段: 受理の守りが、同じ `sgVote` の票が既に行にあるときの印の書き換えを防ぐ。 -/
theorem onSgVote_step (hc : HealConfig) (st : Store) (a : CombinedAttestation) : Step st (onSgVote hc st a) := by
  unfold onSgVote
  dsimp only
  split_ifs with hg
  · exact Step.refl st
  · refine ⟨fun hinv k x hx => ?_, fun hinv k x hx => ⟨?_, ?_⟩⟩
    · change x ∈ NaruStd.Table.getOr (st.sgVotes.insert a.round _) k [] at hx
      rw [rows_insert] at hx
      split_ifs at hx with hk
      · subst hk
        rcases List.mem_append.mp hx with hx | hx
        · exact hinv _ x hx
        · rw [List.mem_singleton.mp hx]
      · exact hinv k x hx
    · change x ∈ NaruStd.Table.getOr (st.sgVotes.insert a.round _) k []
      rw [rows_insert]
      split_ifs with hk
      · subst hk
        exact List.mem_append_left _ hx
      · exact hx
    · change (NaruStd.Table.insert st.timestampSgVote (sgVote a) (Stamp.At st.t)).get? (sgVote x) = _
      refine sgv_get?_insert_ne _ _ _ _ (fun heq => hg ?_)
      have hv : x.valIndex = a.valIndex := (congrArg SGVote.valIndex heq).symm
      have hr : x.round = a.round := (congrArg SGVote.round heq).symm
      have hcf : x.confirmed = a.confirmed := (congrArg SGVote.confirmed heq).symm
      have hk : k = a.round := (hinv k x hx).symm.trans hr
      subst hk
      have hpool : x ∈ (sgPool st a.round).elems := by
        unfold sgPool
        exact (mem_toSet_iff ca_compare_eq_iff _ _).mpr hx
      have hmem : a.confirmed ∈ (roundVotes st a).elems := by
        unfold roundVotes
        refine (mem_of_iff (opt_compare_eq_iff bid_compare_eq_iff) _ _).mpr (List.mem_map.mpr ⟨x, ?_, hcf⟩)
        exact List.mem_filter.mpr ⟨hpool, beq_iff_eq.mpr hv⟩
      have hcont : (roundVotes st a).contains a.confirmed = true :=
        (contains_iff_mem (opt_compare_eq_iff bid_compare_eq_iff) _ _).mpr hmem
      simp [hcont]

theorem updateFinality_step (st : Store) (σ : ChainState) : Step st (updateFinality st σ) := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact Step.of_same rfl rfl

theorem updateConfirmationWith_step (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (k : Nat) :
    Step st (updateConfirmationWith cache e hc st k) :=
  Step.of_same rfl rfl

theorem goldfishVoteWith_step (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) (st : Store) : Step st (goldfishVoteWith c cache e hc nd st).1 := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_step c st _
  · exact Step.refl st

/-! ## ブロックの受理 -/

theorem storedOf_step (st : Store) (b : Block) (post : ChainState) : Step st (storedOf st b post) :=
  Step.of_same rfl rfl

theorem acceptBody_step (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    Step st (acceptBody c st b post) :=
  ((storedOf_step st b post).trans (foldl_step _ (fun s u => onGoldfishVoteChecked_step c s u) _ _)).trans
    (updateFinality_step _ _)

theorem onBlockUsing_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : Step st (onBlockUsing c p st b build) := by
  rcases onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h]; exact Step.refl st
  · rw [h]; exact acceptBody_step c st b _

theorem onBlockCheckedUsing_step (handle : Store → Store) (hh : ∀ s, Step s (handle s)) (hc : HealConfig) (st : Store)
    (b : Block) : Step st (onBlockCheckedUsing handle hc st b) := by
  rcases onBlockCheckedUsing_eq handle hc st b with h | h
  · rw [h]; exact hh st
  · rw [h]; exact Step.refl st

/-! ## `NamedStore` のハンドラ -/

theorem processBlockCore_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    Step st.core (processBlockCore c p e hc cfg st b).core := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · exact Step.refl _
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    exact onBlockCheckedUsing_step _ (fun cur => onBlockUsing_step c p cur _ _) hc st.core _

theorem admitRow_step (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) :
    Step st.core (admitRow hc st row).core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_step hc st.core _

theorem admitRows_step (hc : HealConfig) :
    ∀ (rows : List NamedAttestation) (st : NamedStore), Step st.core (admitRows hc st rows).core
  | [], _ => Step.refl _
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_step hc rows (admitRow hc st row)
    unfold admitRows at ih
    exact (admitRow_step hc st row).trans ih

theorem admitCarried_step (adm : CarriedAdmission) (hc : HealConfig) (before after : NamedStore) (b : NamedBlock) :
    Step after.core (admitCarried adm hc before after b).core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_step hc _ after
  · exact Step.refl _

theorem onBlockWith_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    Step st.core (onBlockWith c p adm e hc cfg st b).core := by
  unfold onBlockWith
  exact (processBlockCore_step c p e hc cfg st b).trans (admitCarried_step adm hc st _ b)

theorem receiptProcess_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (o : NamedObject) :
    Step st.core (receiptProcess c p s st o).core := by
  cases o with
  | Block b => exact onBlockWith_step c p _ _ _ _ st b
  | GfVote u =>
    show Step st.core (onGoldfishVoteChecked c st.core u)
    exact onGoldfishVoteChecked_step c st.core u
  | Attest a =>
    show Step st.core (admitRow s.hc st a).core
    exact admitRow_step s.hc st a

theorem nodeProcess_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : NamedObject) :
    Step n.st.core (nodeProcess c p s n o).st.core :=
  receiptProcess_step c p s n.st o

/-! ## Tick の務め -/

/-- `NamedStore` の間の 1 段(`core` の `Step`)。tick の 16 経路を入れ子の形で閉じるため。 -/
abbrev SStep (a b : NamedStore) : Prop := Step a.core b.core

theorem proposeBlockWith_step' (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Node) {s0 st : NamedStore} (h : SStep s0 st) : SStep s0 (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  refine Step.trans h ?_
  unfold proposeBlockWith
  split
  · exact Step.refl _
  · rename_i b _
    exact onBlockWith_step c p CarriedAdmission.AlsoCarried e hc cfg st b

theorem namedGoldfishVoteWith_step' (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) {s0 st : NamedStore} (h : SStep s0 st) : SStep s0 (namedGoldfishVoteWith c cache e hc nd st).1 := by
  refine Step.trans h ?_
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show Step st.core core
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  rw [h1]
  exact goldfishVoteWith_step c cache e hc nd st.core

theorem namedUpdateConfirmationWith_step' (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) {s0 st : NamedStore}
    (h : SStep s0 st) (k : Nat) : SStep s0 (namedUpdateConfirmationWith cache e hc st k) :=
  Step.trans h (updateConfirmationWith_step cache e hc st.core k)

theorem attestWith_step' (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (nd : Node) {s0 st : NamedStore}
    (h : SStep s0 st) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    SStep s0 (attestWith cache e hc nd st rec).1 := by
  refine Step.trans h ?_
  unfold attestWith
  split
  exact admitRow_step hc st _

/-- 1 tick の務め `tick` は 1 段(時計合わせは SG 票の表を変えない。`BlockStamps.tick_grow` と同じ 16 経路)。 -/
theorem tick_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Node) (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    Step st.core (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  have h0 : SStep st { st with core := { st.core with t := t, s := slotOf e t } } := Step.of_same rfl rfl
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)) _) rec
    | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd h0) _) rec
    | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc (proposeBlockWith_step' c p nr cache e hc cfg nd h0) _) rec
    | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc h0 _) rec
    | with_reducible exact attestWith_step' cache e hc nd (namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)) rec
    | with_reducible exact attestWith_step' cache e hc nd (namedGoldfishVoteWith_step' c cache e hc nd h0) rec
    | with_reducible exact attestWith_step' cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0) rec
    | with_reducible exact attestWith_step' cache e hc nd h0 rec
    | with_reducible exact namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)) _
    | with_reducible exact namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_step' cache e hc (proposeBlockWith_step' c p nr cache e hc cfg nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_step' cache e hc h0 _
    | with_reducible exact namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)
    | with_reducible exact namedGoldfishVoteWith_step' c cache e hc nd h0
    | with_reducible exact proposeBlockWith_step' c p nr cache e hc cfg nd h0
    | with_reducible exact h0

theorem nodeTick_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) : Step n.st.core (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_step c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## world と run -/

/-- 1 event の後、どのノードの store も 1 段。 -/
theorem worldStep_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (w : NamedWorld) (ev : NamedEvent)
    (v : ValidatorId) : Step (worldAt w v).st.core (worldAt (worldStep c p a nr s w ev) v).st.core := by
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeTick_step c p a nr s u (worldAt w u) t
    · rw [h]
      exact Step.refl _
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeProcess_step c p s (worldAt w u) o
    · rw [h]
      exact Step.refl _

theorem foldl_worldStep_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) (w : NamedWorld) (v : ValidatorId),
      Step (worldAt w v).st.core (worldAt (l.foldl (worldStep c p a nr s) w) v).st.core
  | [], _, _ => Step.refl _
  | ev :: l, w, v => by
    rw [List.foldl_cons]
    exact (worldStep_step c p a nr s w ev v).trans (foldl_worldStep_step c p a nr s l _ v)

/-- 初期の store は SG 票の表が空なので、行の不変条件を満たす。 -/
theorem initial_sgInv : SgInv initStore := fun k x hx => by
  have : rows initStore k = [] := rfl
  rw [this] at hx
  exact absurd hx List.not_mem_nil

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の前の world のどのノードの store も行の不変条件を満たす(run への前提なし)。 -/
theorem stateBefore_sgInv (i : Nat) (v : ValidatorId) : SgInv (worldAt (stateBefore c p a nr s rho i) v).st.core := by
  unfold stateBefore
  exact (foldl_worldStep_step c p a nr s _ _ v).inv initial_sgInv

/-- 添字について、同じノードの store は 1 段。 -/
theorem stateBefore_step {i j : Nat} (hij : i ≤ j) (v : ValidatorId) :
    Step (worldAt (stateBefore c p a nr s rho i) v).st.core (worldAt (stateBefore c p a nr s rho j) v).st.core := by
  induction j with
  | zero =>
    rw [Nat.le_zero.mp hij]
    exact Step.refl _
  | succ j ih =>
    rcases Nat.lt_or_ge j i with hlt | hle
    · have : i = j + 1 := by omega
      rw [this]
      exact Step.refl _
    · refine (ih hle).trans ?_
      rw [Proofs.Consensus.Signing.stateBefore_succ]
      cases rho.events[j]? with
      | none => exact Step.refl _
      | some ev => exact worldStep_step c p a nr s _ ev v

/-- **添字について、同じノードの store は SG 票の行と受信の印を保存する**(手書き `strict_sg_row_carry`)。 -/
theorem stateBefore_sgKeep {i j : Nat} (hij : i ≤ j) (v : ValidatorId) :
    SgKeep (worldAt (stateBefore c p a nr s rho i) v).st.core (worldAt (stateBefore c p a nr s rho j) v).st.core :=
  (stateBefore_step c p a nr s rho hij v).keep (stateBefore_sgInv c p a nr s rho i v)

end Run

/-! ## grade の読みの生の入力 -/

/-- grade の読みの鍵 `k` の SG 票は、store の鍵 `k` の行の attestation の `sgVote`。 -/
theorem mem_viewRow_iff (st : Store) (k : Nat) (y : SGVote) :
    y ∈ (NaruStd.Table.getOr (gradeView (storeToHealing st)).sgVotes k (NaruStd.Set.empty : NaruStd.Set SGVote)).elems ↔
      ∃ x ∈ rows st k, sgVote x = y := by
  have hget : NaruStd.Table.get? (gradeView (storeToHealing st)).sgVotes k =
      (NaruStd.Table.get? st.sgVotes k).map (fun rws => NaruStd.Set.map (NaruStd.List.toSet rws) sgVote) := by
    simp only [gradeView, storeToHealing, NaruStd.Table.get?, NaruStd.Table.mapValues, List.find?_map, Option.map_map]
    rfl
  unfold rows NaruStd.Table.getOr
  rw [hget]
  cases NaruStd.Table.get? st.sgVotes k with
  | none => simp [NaruStd.Set.empty]
  | some rws =>
    show y ∈ (NaruStd.Set.map (NaruStd.List.toSet rws) sgVote).elems ↔ ∃ x ∈ rws, sgVote x = y
    unfold NaruStd.Set.map
    rw [mem_of_iff sgv_compare_eq_iff, List.mem_map]
    simp only [mem_toSet_iff ca_compare_eq_iff]

/-- 行と印が残れば、生の入力は後の store と遅い cutoff に持ち越せる(手書き `q10_rawInputs_fwd` の抽象的な半分)。 -/
theorem rawInputs_of_keep {a b : Store} (hk : SgKeep a b) {eta r : Nat} {c c' : Int} (hc : c ≤ c') {v : ValidatorId}
    {y : SGVote} (hy : y ∈ (rawInputs (gradeView (storeToHealing a)) eta r c v).elems) :
    y ∈ (rawInputs (gradeView (storeToHealing b)) eta r c' v).elems := by
  rw [GradeSupporter.mem_rawInputs_iff] at hy ⊢
  obtain ⟨hw, hv, hs⟩ := hy
  obtain ⟨k, hkw, hyk⟩ := (mem_flatMap_iff sgv_compare_eq_iff _ _ _).mp hw
  obtain ⟨x, hx, rfl⟩ := (mem_viewRow_iff a k _).mp hyk
  obtain ⟨hxb, hst⟩ := hk k x hx
  refine ⟨(mem_flatMap_iff sgv_compare_eq_iff _ _ _).mpr ⟨k, hkw, (mem_viewRow_iff b k _).mpr ⟨x, hxb, rfl⟩⟩, hv, ?_⟩
  change occurrenceBefore (b.timestampSgVote.get? (sgVote x)) c' = true
  rw [hst]
  exact GradeSupporter.occurrenceBefore_mono hs hc

end Proofs.Consensus.SgStamps
