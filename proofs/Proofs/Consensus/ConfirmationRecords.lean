import Model.Consensus.Execution.Node
import Proofs.Consensus.Blocks
import Proofs.Consensus.Stores
import Proofs.Consensus.Carrier
import Proofs.Consensus.TreeInv
import Mathlib.Tactic

/-!
# 確認の記録 `latestConfirmed` / `latestStable` を書くハンドラ(C71 の liveness 系 claim の足場)

生成 Model の store には利用者向けの 2 つの記録 `latestConfirmed`(確認)と `latestStable`(stable)がある
(`Model/Consensus/Protocol/Store.lean`)。これらを書くのは `updateConfirmationWith`(`Handlers.lean`)だけで、
書き方は `advanceConfirmed old cand`(`cand ⪯ old` なら `old`、でなければ `cand`)と
`floorOnStable stable cand old`(`stable ⪯ cand` なら `cand`、`stable ⪯ old` なら `old`、でなければ `stable`)の組み合わせ。
`advanceConfirmed` は「古い記録の接頭辞 `B` は、新しい記録と互換なら新しい記録の接頭辞のまま」(`Keeps`)を満たし、`floorOnStable` は
候補 `cand` の側がそれを満たす限り同じ性質を保つ(`floorOnStable_keeps` の前提 `harm`)ので、組み合わせも `Keeps` を満たす。
記録は一致(互換)の下では後退しない、というのが claim `available` の `SafeFrom`(`AgreeFrom ∧ MonotoneFrom`)の
単調性の側を一致の側に還元する鍵で、`RecordGrowth.lean` が run に沿ってこれを積み上げる。
`Keeps` は推移的でない(途中の記録との互換が要る)ので、1 tick = 高々 1 回の `updateConfirmationWith` という形
(`tick_rec_shape`)で使う。他のハンドラ(投票・attestation・ブロックの受理・finality の更新)は 2 つの記録を変えない(`SameRec`)。

手書き `DecoupledConsensusProofs/Protocol/Handlers/Monotone.lean`(`preceq_floor` / `update_confirmation_with_latest_preserves` /
`*_latest` / `tick_latest_preserves`)と `Protocol/Handlers/RetentionNamed.lean`(`node_process_latest`)の筋。手書きは `latest_confirmed` だけを扱うが、ここでは
`latestStable` も同じ形で扱う(`stable` は `advanceConfirmed st.latestStable g` か不変)。
-/

namespace Proofs.Consensus.ConfirmationRecords

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick Model.Consensus.Protocol.Grades
open Model.Consensus.Protocol.ChainState Model.Consensus.Execution.Node
open Proofs.Consensus.Blocks Proofs.Consensus.Carrier Proofs.Consensus.Trees

/-! ## 記録の接頭辞保存 -/

/-- 記録 `old` の接頭辞 `B` は、`new` と互換なら `new` の接頭辞。 -/
def Keeps (old new : Block) : Prop :=
  ∀ B, preceq B old = true → compatible B new = true → preceq B new = true

theorem Keeps.refl (b : Block) : Keeps b b := fun _ h _ => h

theorem Keeps.of_eq {old new : Block} (h : new = old) : Keeps old new := by
  subst h; exact Keeps.refl _

/-- `advanceConfirmed old cand` は接頭辞を保つ: 結果が `old` なら自明、`cand` なら `¬ cand ⪯ old` と互換から `B ⪯ cand`。 -/
theorem advanceConfirmed_keeps (old cand : Block) : Keeps old (advanceConfirmed old cand) := by
  intro B hold hc
  unfold advanceConfirmed at hc ⊢
  split_ifs at hc ⊢ with h
  · exact hold
  · unfold compatible at hc
    rw [Bool.or_eq_true] at hc
    rcases hc with hBc | hcB
    · exact hBc
    · exact absurd (preceq_trans hcB hold) h

/-- `floorOnStable stable cand old` は、`cand` が互換なら接頭辞を保つ限り、接頭辞を保つ。手書き `preceq_floor`。 -/
theorem floorOnStable_keeps {B stable cand old : Block} (hold : preceq B old = true)
    (harm : compatible B cand = true → preceq B cand = true)
    (hc : compatible B (floorOnStable stable cand old) = true) :
    preceq B (floorOnStable stable cand old) = true := by
  unfold floorOnStable at hc ⊢
  split_ifs at hc ⊢ with h1 h2
  · exact harm hc
  · exact hold
  · unfold compatible at hc
    rw [Bool.or_eq_true] at hc
    rcases hc with hBs | hsB
    · exact hBs
    · exact absurd (preceq_trans hsB hold) h2

/-- 確認の更新は stable の記録の接頭辞を保つ(`frameStableRoot` が返せば `advanceConfirmed st.latestStable g`、でなければ不変)。 -/
theorem updateConfirmationWith_stable_keeps (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (k : Nat) :
    Keeps st.latestStable (updateConfirmationWith cache e hc st k).latestStable := by
  unfold updateConfirmationWith
  dsimp only
  cases hfs : frameStableRoot cache e hc (storeToHealing st) (roundOf hc st.s) with
  | some g =>
    dsimp only
    exact advanceConfirmed_keeps _ _
  | none =>
    dsimp only
    exact Keeps.refl _

/-- 確認の更新は確認の記録の接頭辞を保つ(`floorOnStable` の `cand` は `advanceConfirmed st.latestConfirmed _` か不変)。
手書き `update_confirmation_with_latest_preserves`。 -/
theorem updateConfirmationWith_confirmed_keeps (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (k : Nat) :
    Keeps st.latestConfirmed (updateConfirmationWith cache e hc st k).latestConfirmed := by
  intro B hold hcompat
  unfold updateConfirmationWith at hcompat ⊢
  dsimp only at hcompat ⊢
  refine floorOnStable_keeps hold ?_ hcompat
  split_ifs
  · exact advanceConfirmed_keeps _ _ B hold
  · cases hcand : frameSgCandidate cache e hc (storeToHealing st) k with
    | some cand =>
      dsimp only
      exact advanceConfirmed_keeps _ _ B hold
    | none =>
      dsimp only
      exact fun _ => hold

/-! ## 2 つの記録を変えないハンドラ -/

/-- `latestConfirmed` と `latestStable` が等しい。 -/
structure SameRec (a b : Store) : Prop where
  confirmed : a.latestConfirmed = b.latestConfirmed
  stable : a.latestStable = b.latestStable

theorem SameRec.refl (a : Store) : SameRec a a := ⟨rfl, rfl⟩

theorem SameRec.trans {a b c : Store} (h1 : SameRec a b) (h2 : SameRec b c) : SameRec a c :=
  ⟨h1.confirmed.trans h2.confirmed, h1.stable.trans h2.stable⟩

theorem SameRec.of_eq {a b : Store} (h : a = b) : SameRec a b := by
  subst h; exact SameRec.refl _

theorem SameRec.of_out {a b : Store} (h : SameOut a b) : SameRec a b := ⟨h.confirmed, h.stable⟩

theorem onGoldfishVote_rec (st : Store) (u : GoldfishVote) : SameRec (onGoldfishVote st u) st :=
  SameRec.of_out (onGoldfishVote_out st u)

theorem onGoldfishVoteChecked_rec (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    SameRec (onGoldfishVoteChecked c st u) st :=
  SameRec.of_out (onGoldfishVoteChecked_out c st u)

theorem foldl_rec {β : Type} (g : Store → β → Store) (hg : ∀ s x, SameRec (g s x) s) :
    ∀ (l : List β) (st : Store), SameRec (List.foldl g st l) st
  | [], _ => SameRec.refl _
  | x :: l, st => by
    rw [List.foldl_cons]
    exact (foldl_rec g hg l (g st x)).trans (hg st x)

theorem onSgVote_rec (hc : HealConfig) (st : Store) (a : CombinedAttestation) : SameRec (onSgVote hc st a) st :=
  SameRec.of_out (onSgVote_out hc st a)

theorem goldfishVoteWith_rec (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : Store) :
    SameRec (goldfishVoteWith c cache e hc nd st).1 st :=
  SameRec.of_out (goldfishVoteWith_out c cache e hc nd st)

theorem updateFinality_rec (st : Store) (σ : ChainState) : SameRec (updateFinality st σ) st :=
  ⟨(updateFinality_out st σ).2.2.2.1, (updateFinality_out st σ).2.2.2.2⟩

theorem acceptBody_rec (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    SameRec (acceptBody c st b post) st :=
  ⟨(acceptBody_out c st b post).2.2.2.1, (acceptBody_out c st b post).2.2.2.2⟩

/-- ブロックの受理 `onBlockUsing` は記録を変えない(`onBlockUsing_eq`: store のままか `acceptBody`)。手書き `on_block_using_latest`。 -/
theorem onBlockUsing_rec (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : SameRec (onBlockUsing c p st b build) st := by
  rcases onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h]; exact SameRec.refl _
  · rw [h]; exact acceptBody_rec c st b _

theorem onBlockCheckedUsing_rec (handle : Store → Store) (hh : ∀ s, SameRec (handle s) s) (hc : HealConfig)
    (st : Store) (b : Block) : SameRec (onBlockCheckedUsing handle hc st b) st := by
  rcases onBlockCheckedUsing_eq handle hc st b with h | h
  · rw [h]; exact hh st
  · rw [h]; exact SameRec.refl _

/-! ## `NamedStore` のハンドラ -/

theorem processBlockCore_rec (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    SameRec (processBlockCore c p e hc cfg st b).core st.core := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · exact SameRec.refl _
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    exact onBlockCheckedUsing_rec _ (fun cur => onBlockUsing_rec c p cur _ _) hc st.core _

theorem admitRow_rec (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) :
    SameRec (admitRow hc st row).core st.core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_rec hc st.core _

theorem admitRows_rec (hc : HealConfig) :
    ∀ (rows : List NamedAttestation) (st : NamedStore), SameRec (admitRows hc st rows).core st.core
  | [], _ => SameRec.refl _
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_rec hc rows (admitRow hc st row)
    unfold admitRows at ih
    exact ih.trans (admitRow_rec hc st row)

theorem admitCarried_rec (adm : CarriedAdmission) (hc : HealConfig) (before after : NamedStore) (b : NamedBlock) :
    SameRec (admitCarried adm hc before after b).core after.core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_rec hc _ after
  · exact SameRec.refl _

theorem onBlockWith_rec (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    SameRec (onBlockWith c p adm e hc cfg st b).core st.core := by
  unfold onBlockWith
  exact (admitCarried_rec adm hc st _ b).trans (processBlockCore_rec c p e hc cfg st b)

/-- 受信した object の処理は記録を変えない。 -/
theorem receiptProcess_rec (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (o : Model.Consensus.Execution.Objects.NamedObject) :
    SameRec (receiptProcess c p s st o).core st.core := by
  cases o with
  | Block b => exact onBlockWith_rec c p _ _ _ _ st b
  | GfVote u =>
    show SameRec (onGoldfishVoteChecked c st.core u) st.core
    exact onGoldfishVoteChecked_rec c st.core u
  | Attest a =>
    show SameRec (admitRow s.hc st a).core st.core
    exact admitRow_rec s.hc st a

/-- Deliver の処理 `nodeProcess` は記録を変えない。手書き `node_process_latest`。 -/
theorem nodeProcess_rec (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : Model.Consensus.Execution.Objects.NamedObject) :
    SameRec (nodeProcess c p s n o).st.core n.st.core :=
  receiptProcess_rec c p s n.st o

/-! ## Tick の務め -/

theorem proposeBlockWith_rec (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) :
    SameRec (proposeBlockWith c p nr cache e hc cfg nd st).1.core st.core := by
  unfold proposeBlockWith
  split
  · exact SameRec.refl _
  · rename_i b _
    exact onBlockWith_rec c p CarriedAdmission.AlsoCarried e hc cfg st b

theorem namedGoldfishVoteWith_rec (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) :
    SameRec (namedGoldfishVoteWith c cache e hc nd st).1.core st.core := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out h
  show SameRec core st.core
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [h]
  rw [h1]
  exact goldfishVoteWith_rec c cache e hc nd st.core

theorem namedUpdateConfirmationWith_core (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : NamedStore) (k : Nat) :
    (namedUpdateConfirmationWith cache e hc st k).core = updateConfirmationWith cache e hc st.core k := rfl

theorem attestWith_rec (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    SameRec (attestWith cache e hc nd st rec).1.core st.core := by
  unfold attestWith
  split
  exact admitRow_rec hc st _

/-- 1 tick の結果の記録の形: 記録を変えない務め(時計合わせ・提案・投票)で得た `st2` に、確認の更新 `updateConfirmationWith`
(slot `slotOf e t - 1`)が高々 1 回掛かり、その後の attestation は記録を変えない。`Carrier.tick_inv` と同じ 16 経路。 -/
theorem tick_rec_shape (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    ∃ st2 : NamedStore, SameRec st2.core st.core ∧
      (SameRec (tick c p a nr cache e hc cfg nd st rec t).1.core st2.core ∨
        SameRec (tick c p a nr cache e hc cfg nd st rec t).1.core
          (updateConfirmationWith cache e hc st2.core (slotOf e t - 1))) := by
  have h0 : SameRec ({ st with core := { st.core with t := t, s := slotOf e t } } : NamedStore).core st.core := ⟨rfl, rfl⟩
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0), Or.inr ((attestWith_rec cache e hc nd _ rec).trans (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _)))⟩
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans h0, Or.inr ((attestWith_rec cache e hc nd _ rec).trans (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _)))⟩
    | with_reducible exact ⟨_, (proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0, Or.inr ((attestWith_rec cache e hc nd _ rec).trans (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _)))⟩
    | with_reducible exact ⟨_, h0, Or.inr ((attestWith_rec cache e hc nd _ rec).trans (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _)))⟩
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0), Or.inl (attestWith_rec cache e hc nd _ rec)⟩
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans h0, Or.inl (attestWith_rec cache e hc nd _ rec)⟩
    | with_reducible exact ⟨_, (proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0, Or.inl (attestWith_rec cache e hc nd _ rec)⟩
    | with_reducible exact ⟨_, h0, Or.inl (attestWith_rec cache e hc nd _ rec)⟩
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0), Or.inr (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _))⟩
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans h0, Or.inr (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _))⟩
    | with_reducible exact ⟨_, (proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0, Or.inr (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _))⟩
    | with_reducible exact ⟨_, h0, Or.inr (SameRec.of_eq (namedUpdateConfirmationWith_core cache e hc _ _))⟩
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0), Or.inl (SameRec.refl _)⟩
    | with_reducible exact ⟨_, (namedGoldfishVoteWith_rec c cache e hc nd _).trans h0, Or.inl (SameRec.refl _)⟩
    | with_reducible exact ⟨_, (proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0, Or.inl (SameRec.refl _)⟩
    | with_reducible exact ⟨_, h0, Or.inl (SameRec.refl _)⟩

/-- 1 tick の務め `tick` は、確認の記録の接頭辞を保つ(時計合わせ・提案・投票・attestation は記録不変、確認の更新は `Keeps`)。
手書き `tick_latest_preserves`。 -/
theorem tick_confirmed_keeps (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    Keeps st.core.latestConfirmed (tick c p a nr cache e hc cfg nd st rec t).1.core.latestConfirmed := by
  obtain ⟨st2, h2, h3 | h3⟩ := tick_rec_shape c p a nr cache e hc cfg nd st rec t
  · rw [h3.confirmed, h2.confirmed]
    exact Keeps.refl _
  · rw [h3.confirmed, ← h2.confirmed]
    exact updateConfirmationWith_confirmed_keeps cache e hc st2.core _

/-- 1 tick の務め `tick` は、stable の記録の接頭辞を保つ。 -/
theorem tick_stable_keeps (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    Keeps st.core.latestStable (tick c p a nr cache e hc cfg nd st rec t).1.core.latestStable := by
  obtain ⟨st2, h2, h3 | h3⟩ := tick_rec_shape c p a nr cache e hc cfg nd st rec t
  · rw [h3.stable, h2.stable]
    exact Keeps.refl _
  · rw [h3.stable, ← h2.stable]
    exact updateConfirmationWith_stable_keeps cache e hc st2.core _

/-- Tick の処理 `nodeTick` は確認の記録の接頭辞を保つ。 -/
theorem nodeTick_confirmed_keeps (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) :
    Keeps n.st.core.latestConfirmed (nodeTick c p a nr s v n t).1.st.core.latestConfirmed := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_confirmed_keeps c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-- Tick の処理 `nodeTick` は stable の記録の接頭辞を保つ。 -/
theorem nodeTick_stable_keeps (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) :
    Keeps n.st.core.latestStable (nodeTick c p a nr s v n t).1.st.core.latestStable := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_stable_keeps c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

end Proofs.Consensus.ConfirmationRecords
