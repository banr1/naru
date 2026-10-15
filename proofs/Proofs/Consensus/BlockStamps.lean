import Proofs.Consensus.Stamps
import Proofs.Consensus.TreeInv
import Mathlib.Tactic

/-!
# tree のブロックの受信の印は固定され、時計以下(C71 の補題)

`Majority.HonestSupport.vote` の支持の投票(`supportVotes`)は、解決の印 `storeTau`(投票の受信の印 `timestampVote` と head の
ブロックの受信の印 `timestampBlock` の大きい方)が `supportCutoff` より前の投票。`Stamps` が投票の側を示したので、この節は
ブロックの側の印の運びと、2 つの印から `storeTau` の判定へ結ぶ向き(`storeTau_before`)を示す。

store の受信の印の表 `timestampBlock` を書くのは `onBlockUsing` の受理の分岐(`Carrier.storedOf`)だけで、まだ tree に無い
ブロック `b` を tree に入れるときに、`b` の印を現在の時計 `Stamp.At st.t` にする(`Carrier.onBlockUsing_eq` の `b ∉ tree`)。
初期の store は tree が `{Genesis}` で、genesis の印は `Stamp.Bottom`(`genesisStamp`)。したがって
- **印の保存** `Keep a b`: `a` の tree のブロックは `b` の tree にも残り、印は変わらない。
- **新しいブロックの印** `Fresh a b`: `b` の tree に増えたブロックの印は `b` の時計以下の時刻。
どのハンドラも時計を変えずにこの 2 つを満たし(`Step`)、tick は時計を合わせた後の store からの `Step`(`Grow`)。運びは
`Stamps` と同じで、run のどの添字の store でも tree のブロックの印は `Bottom` か時計以下の時刻(`StampInv`、
`stateBefore_stampInv`)、`stateBefore (j + 1)` の tree にあるブロックは以後ずっと tree にあり、印は添字 `j` の event の
時刻で抑えられる(`stamp_le_of_mem`、`tree_stamped`)。

手書きでは `DecoupledConsensusProofs/Objects/BlockVisibilityCore.lean` の `genesis_mem_and_stamp_storeBeforeTime` /
`admittedBefore_mem_and_stamp_at`(tree のブロックとその印を run に沿って運ぶ)に当たる。運びの形は投票の側の
`Protocol/Handlers/Pool.lean` の `PoolStamps` / `PoolCarry` との類比。
-/

namespace Proofs.Consensus.BlockStamps

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Time Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.StoreBase
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Tables Proofs.Consensus.Sets Proofs.Consensus.Carrier
open Proofs.Consensus.Clocks (SameClock)

/-! ## ブロックを鍵にした表 -/

theorem bl_get?_insert_self {ν : Type} (t : NaruStd.Table Block ν) (k : Block) (v : ν) :
    (t.insert k v).get? k = some v := by
  simp [NaruStd.Table.get?, NaruStd.Table.insert, find?_insertSorted_self block_compare_eq_iff k v t.entries]

theorem bl_get?_insert_ne {ν : Type} (t : NaruStd.Table Block ν) (k : Block) (v : ν) (k' : Block)
    (hne : k ≠ k') : (t.insert k v).get? k' = t.get? k' := by
  rcases find?_insertSorted block_compare_eq_trans k v k' t.entries with ⟨hk, _⟩ | hf
  · exact absurd ((block_compare_eq_iff k k').mp hk) hne
  · simp [NaruStd.Table.get?, NaruStd.Table.insert, hf]

/-! ## 印の保存と新しいブロックの印 -/

/-- 印の保存: `a` の tree のブロックは `b` の tree にも残り、受信の印は変わらない。 -/
def Keep (a b : Store) : Prop :=
  ∀ B, B ∈ a.tree.elems → B ∈ b.tree.elems ∧ b.timestampBlock.get? B = a.timestampBlock.get? B

/-- 新しいブロックの印: `b` の tree のブロックは `a` の tree にもあったか、受信の印が `b` の時計以下の時刻。 -/
def Fresh (a b : Store) : Prop :=
  ∀ B, B ∈ b.tree.elems → B ∈ a.tree.elems ∨ ∃ τ, b.timestampBlock.get? B = some (Stamp.At τ) ∧ τ ≤ b.t

/-- 時計を変えないハンドラの 1 段: 印の保存・新しいブロックの印・時計の一致。 -/
structure Step (a b : Store) : Prop where
  keep : Keep a b
  fresh : Fresh a b
  clock : SameClock b a

theorem Keep.refl (a : Store) : Keep a a := fun _ h => ⟨h, rfl⟩

theorem Keep.trans {a b d : Store} (h1 : Keep a b) (h2 : Keep b d) : Keep a d := fun B h => by
  obtain ⟨hb, hb'⟩ := h1 B h
  obtain ⟨hd, hd'⟩ := h2 B hb
  exact ⟨hd, hd'.trans hb'⟩

theorem Step.refl (a : Store) : Step a a := ⟨Keep.refl a, fun _ h => Or.inl h, SameClock.refl a⟩

theorem Step.trans {a b d : Store} (h1 : Step a b) (h2 : Step b d) : Step a d := by
  refine ⟨h1.keep.trans h2.keep, fun B hB => ?_, h2.clock.trans h1.clock⟩
  rcases h2.fresh B hB with hb | hd
  · rcases h1.fresh B hb with ha | ⟨τ, hτ, hle⟩
    · exact Or.inl ha
    · obtain ⟨-, heq⟩ := h2.keep B hb
      exact Or.inr ⟨τ, heq.trans hτ, by rw [h2.clock.t]; exact hle⟩
  · exact Or.inr hd

/-- tree・印の表・時計が等しい store の間は 1 段(何も増えない)。 -/
theorem Step.of_same {a b : Store} (htr : b.tree = a.tree) (htb : b.timestampBlock = a.timestampBlock)
    (hc : SameClock b a) : Step a b :=
  ⟨fun B hB => ⟨by rw [htr]; exact hB, by rw [htb]⟩, fun B hB => Or.inl (by rw [← htr]; exact hB), hc⟩

/-! ## tree と印の表を触らない `Store` のハンドラ -/

theorem onGoldfishVote_step (st : Store) (x : GoldfishVote) : Step st (onGoldfishVote st x) := by
  unfold onGoldfishVote
  split_ifs <;> exact Step.of_same rfl rfl ⟨rfl, rfl⟩

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

theorem onSgVote_step (hc : HealConfig) (st : Store) (a : CombinedAttestation) : Step st (onSgVote hc st a) := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact Step.of_same rfl rfl ⟨rfl, rfl⟩

theorem updateFinality_step (st : Store) (σ : ChainState) : Step st (updateFinality st σ) := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact Step.of_same rfl rfl ⟨rfl, rfl⟩

theorem updateConfirmationWith_step (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (k : Nat) :
    Step st (updateConfirmationWith cache e hc st k) :=
  Step.of_same rfl rfl ⟨rfl, rfl⟩

theorem goldfishVoteWith_step (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) (st : Store) : Step st (goldfishVoteWith c cache e hc nd st).1 := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_step c st _
  · exact Step.refl st

/-! ## ブロックの受理 -/

/-- まだ tree に無いブロック `b` を入れる `storedOf` は 1 段: 既存のブロックの印は残り、`b` の印は時計の時刻。 -/
theorem storedOf_step {st : Store} {b : Block} (hb : b ∉ st.tree.elems) (post : ChainState) :
    Step st (storedOf st b post) := by
  refine ⟨fun B hB => ⟨?_, ?_⟩, fun B hB => ?_, ⟨rfl, rfl⟩⟩
  · exact (mem_insert_iff block_compare_eq_iff st.tree b B).mpr (Or.inr hB)
  · refine bl_get?_insert_ne _ _ _ _ ?_
    rintro rfl
    exact hb hB
  · rcases (mem_insert_iff block_compare_eq_iff st.tree b B).mp hB with rfl | hB
    · exact Or.inr ⟨st.t, bl_get?_insert_self _ _ _, le_rfl⟩
    · exact Or.inl hB

theorem unpackedOf_step (c : Nat → NaruStd.Set ValidatorId) {st : Store} {b : Block} (hb : b ∉ st.tree.elems)
    (post : ChainState) : Step st (unpackedOf c st b post) :=
  (storedOf_step hb post).trans (foldl_step _ (fun s u => onGoldfishVoteChecked_step c s u) _ _)

theorem acceptBody_step (c : Nat → NaruStd.Set ValidatorId) {st : Store} {b : Block} (hb : b ∉ st.tree.elems)
    (post : ChainState) : Step st (acceptBody c st b post) :=
  (unpackedOf_step c hb post).trans (updateFinality_step _ _)

theorem onBlockUsing_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : Step st (onBlockUsing c p st b build) := by
  rcases onBlockUsing_eq c p st b build with h | ⟨hb, -, h⟩
  · rw [h]; exact Step.refl st
  · rw [h]; exact acceptBody_step c hb _

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

/-- 印の保存と新しいブロックの印(時計の一致は問わない)。 -/
def Grow (a b : Store) : Prop := Keep a b ∧ Fresh a b

theorem Step.grow {a b : Store} (h : Step a b) : Grow a b := ⟨h.keep, h.fresh⟩

theorem Grow.refl (a : Store) : Grow a a := (Step.refl a).grow

/-- 1 tick の務め `tick` は印を保存し、新しいブロックの印は tick の後の時計以下(時計合わせの後の store からの `Step`。
`Stamps.tick_grow` と同じ 16 経路)。 -/
theorem tick_grow (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Node) (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    Grow st.core (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  have h0 : SStep { st with core := { st.core with t := t, s := slotOf e t } }
      { st with core := { st.core with t := t, s := slotOf e t } } := Step.refl _
  have hfin : SStep { st with core := { st.core with t := t, s := slotOf e t } } (tick c p a nr cache e hc cfg nd st rec t).1 := by
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
  exact ⟨fun B hB => hfin.keep B hB, fun B hB => hfin.fresh B hB⟩

theorem nodeTick_grow (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) : Grow n.st.core (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_grow c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## world と run -/

/-- 1 event の後、どのノードの store も印を保存し、新しいブロックの印はその store の時計以下。 -/
theorem worldStep_grow (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (w : NamedWorld) (ev : NamedEvent)
    (v : ValidatorId) : Grow (worldAt w v).st.core (worldAt (worldStep c p a nr s w ev) v).st.core := by
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeTick_grow c p a nr s u (worldAt w u) t
    · rw [h]
      exact Grow.refl _
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, h⟩ | h
    · rw [h]
      exact (nodeProcess_step c p s (worldAt w u) o).grow
    · rw [h]
      exact Grow.refl _

/-- 印が時刻 `t` で抑えられる: genesis の印 `Bottom` か、`t` 以下の時刻。 -/
def Bounded (x : Option Stamp) (t : Int) : Prop :=
  x = some Stamp.Bottom ∨ ∃ τ, x = some (Stamp.At τ) ∧ τ ≤ t

theorem Bounded.mono {x : Option Stamp} {t t' : Int} (h : Bounded x t) (ht : t ≤ t') : Bounded x t' := by
  rcases h with h | ⟨τ, hτ, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨τ, hτ, le_trans hle ht⟩

/-- `t` で抑えられた印は、`t < γ` なら `γ` より前。 -/
theorem Bounded.before {x : Option Stamp} {t γ : Int} (h : Bounded x t) (hγ : t < γ) :
    occurrenceBefore x γ = true := by
  rcases h with rfl | ⟨τ, rfl, hle⟩
  · unfold occurrenceBefore
    exact (Proofs.Consensus.Majority.stampBefore_iff _ _).mpr (Or.inl rfl)
  · exact Proofs.Consensus.Stamps.occurrenceBefore_at (lt_of_le_of_lt hle hγ)

/-- 印の不変条件: tree のブロックの受信の印は、`Bottom` か store の時計以下の時刻。 -/
def StampInv (st : Store) : Prop :=
  ∀ B, B ∈ st.tree.elems → Bounded (st.timestampBlock.get? B) st.t

theorem StampInv.of_grow {a b : Store} (h : StampInv a) (hg : Grow a b) (ht : a.t ≤ b.t) : StampInv b := fun B hB => by
  rcases hg.2 B hB with ha | ⟨τ, hτ, hle⟩
  · obtain ⟨-, heq⟩ := hg.1 B ha
    rw [heq]
    exact (h B ha).mono ht
  · exact Or.inr ⟨τ, hτ, hle⟩

/-- 初期の store: tree は `{Genesis}` で、genesis の印は `Bottom`。 -/
theorem initial_stampInv : StampInv initStore := fun B hB => by
  have hB' : B ∈ (NaruStd.Set.singleton Block.Genesis).elems := hB
  rw [mem_singleton_iff] at hB'
  subst hB'
  exact Or.inl (bl_get?_insert_self _ _ _)

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字について、同じノードの store は tree のブロックとその印を保存する。 -/
theorem stateBefore_keep {i j : Nat} (hij : i ≤ j) (v : ValidatorId) :
    Keep (worldAt (stateBefore c p a nr s rho i) v).st.core (worldAt (stateBefore c p a nr s rho j) v).st.core := by
  induction j with
  | zero =>
    rw [Nat.le_zero.mp hij]
    exact Keep.refl _
  | succ j ih =>
    rcases Nat.lt_or_ge j i with hlt | hle
    · have : i = j + 1 := by omega
      rw [this]
      exact Keep.refl _
    · refine (ih hle).trans ?_
      rw [Proofs.Consensus.Signing.stateBefore_succ]
      cases rho.events[j]? with
      | none => exact Keep.refl _
      | some ev =>
        show Keep _ (worldAt (worldStep c p a nr s (stateBefore c p a nr s rho j) ev) v).st.core
        exact (worldStep_grow c p a nr s _ ev v).1

/-- **run のどの添字・どのノードでも印の不変条件**(event の整列と時刻の非負の下で。時計の単調性 `Window.clock_succ_ge`)。 -/
theorem stateBefore_stampInv (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev) :
    ∀ (i : Nat) (v : ValidatorId), StampInv (worldAt (stateBefore c p a nr s rho i) v).st.core
  | 0, _ => initial_stampInv
  | i + 1, v => by
    have ih := stateBefore_stampInv hs hnn i v
    have ht := Proofs.Consensus.Window.clock_succ_ge c p a nr s rho hs hnn i v
    refine ih.of_grow ?_ ht
    rw [Proofs.Consensus.Signing.stateBefore_succ]
    cases rho.events[i]? with
    | none => exact Grow.refl _
    | some ev =>
      show Grow _ (worldAt (worldStep c p a nr s (stateBefore c p a nr s rho i) ev) v).st.core
      exact worldStep_grow c p a nr s _ ev v

/-- **印は event の時刻で抑えられたまま固定される**: `stateBefore (j + 1)` の `w` の tree に `B` があれば、`j` より後の
どの添字でも `B` は `w` の tree にあり、受信の印は添字 `j` の event の時刻で抑えられる。 -/
theorem stamp_le_of_mem (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {j : Nat} {ev : NamedEvent} (hev : rho.events[j]? = some ev) {w : ValidatorId} {B : Block}
    (hB : B ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems) {i : Nat} (hji : j < i) :
    B ∈ (worldAt (stateBefore c p a nr s rho i) w).st.core.tree.elems ∧
      Bounded ((worldAt (stateBefore c p a nr s rho i) w).st.core.timestampBlock.get? B) (eventTime ev) := by
  have hb := stateBefore_stampInv c p a nr s rho hs hnn (j + 1) w B hB
  obtain ⟨hmem, heq⟩ := stateBefore_keep c p a nr s rho (i := j + 1) (j := i) hji w B hB
  refine ⟨hmem, ?_⟩
  rw [heq]
  exact hb.mono (Proofs.Consensus.Stamps.clock_succ_le_event c p a nr s rho hs hnn hev w)

/-- `stateBefore (j + 1)` の tree にあるブロックは、添字 `j` の event の時刻が `γ` より前なら、`j` より後のどの添字でも
tree にあり受信の印が `γ` より前。 -/
theorem tree_stamped (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {j : Nat} {ev : NamedEvent} (hev : rho.events[j]? = some ev) {γ : Int} (hγ : eventTime ev < γ) {w : ValidatorId}
    {B : Block} (hB : B ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems) {i : Nat} (hji : j < i) :
    B ∈ (worldAt (stateBefore c p a nr s rho i) w).st.core.tree.elems ∧
      occurrenceBefore ((worldAt (stateBefore c p a nr s rho i) w).st.core.timestampBlock.get? B) γ = true := by
  obtain ⟨hm, hb⟩ := stamp_le_of_mem c p a nr s rho hs hnn hev hB hji
  exact ⟨hm, hb.before hγ⟩

end Run

/-! ## 2 つの印から解決の印へ -/

/-- 2 つの印がどちらも `γ` より前なら、大きい方も `γ` より前(`Majority.stampBefore_of_max` の逆向き)。 -/
theorem stampBefore_max {x y : Stamp} {γ : Int} (hx : stampBefore x γ = true) (hy : stampBefore y γ = true) :
    stampBefore (if compare x y == .lt then y else x) γ = true := by
  split_ifs
  · exact hy
  · exact hx

/-- **解決の印が締切より前**: 投票の head の root を引いたブロック `hd`(slot が投票の slot 以下)の受信の印と、投票の受信の印が
どちらも `γ` より前なら、`storeTau st u` も `γ` より前。 -/
theorem storeTau_before {st : Store} {u : GoldfishVote} {hd : Block} {γ : Int} (hr : findRoot? st.tree u.head = some hd)
    (hsl : slot hd ≤ u.slot) (hv : occurrenceBefore (st.timestampVote.get? u) γ = true)
    (hb : occurrenceBefore (st.timestampBlock.get? hd) γ = true) : occurrenceBefore (storeTau st u) γ = true := by
  unfold storeTau resolutionTime
  rw [hr]
  dsimp only
  simp only [hsl, decide_true, ↓reduceIte]
  unfold occurrenceMax
  cases hvv : st.timestampVote.get? u with
  | none =>
    rw [hvv] at hv
    exact absurd hv (by simp [occurrenceBefore])
  | some x =>
    rw [hvv] at hv
    cases hbb : st.timestampBlock.get? hd with
    | none =>
      rw [hbb] at hb
      exact absurd hb (by simp [occurrenceBefore])
    | some y =>
      rw [hbb] at hb
      dsimp only [occurrenceBefore] at hv hb ⊢
      exact stampBefore_max hv hb

/-- `findRoot?` が引いたブロックは tree にあり、その root は引いた root。 -/
theorem findRoot?_mem {tree : NaruStd.Set Block} {r : BlockId} {hd : Block} (h : findRoot? tree r = some hd) :
    hd ∈ tree.elems ∧ root hd = r := by
  obtain ⟨hm, hp⟩ := Proofs.Consensus.Trees.findUnique?_mem h
  exact ⟨hm, beq_iff_eq.mp hp⟩

end Proofs.Consensus.BlockStamps
