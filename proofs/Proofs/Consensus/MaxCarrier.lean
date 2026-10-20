import Proofs.Consensus.JustifiedCarrier
import Mathlib.Tactic

/-!
# store の最大の高さの carrier(C77 の補題)

`AvailableHoles` の段の 2 つの穴に残る「band に届かない枝」(手書き `coreFrontierConfirmationWitness`、
`DecoupledConsensusProofs/Protocol/Schedule/WeakGoldfishCone.lean`)の最初の層。手書きは frontier の証人を
`Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime`(store の `h_max` は bodies のどれかの `W` の導出の高さ)から作る。

- store の `hMax` を書くのは `updateFinality` だけで、書く値は `max hMax σ.h`(`σ` は受理したばかりのブロック `B` の chain 状態
  `post`)。`Carrier.StoreInv` の `sigma` から `post = deriveNamed e cfg B` なので、`hMax` は常に bodies のどれかの `D` の導出の
  高さに等しい(`MCarrier`)。他のハンドラは `hMax` を変えず(`SameM`)、bodies は増えるだけ。初期 store は `hMax = 1` で、
  genesis の導出(`initialChainState`)の高さも 1。
- `JustifiedCarrier.lean` と同じ順に `Store` → `NamedStore` → tick / 配送 → world → run の読みに積む
  (`stateBefore_mcarrier` / `readAt_mcarrier` / `stateBeforeTime_mcarrier`。前提なし)。
-/

namespace Proofs.Consensus.MaxCarrier

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Tables Proofs.Consensus.NamedBlocks
open Proofs.Consensus.Runs Proofs.Consensus.Carrier

/-! ## 不変条件 -/

/-- `hMax` の欄が等しい。 -/
structure SameM (a b : Store) : Prop where
  hMax : a.hMax = b.hMax

theorem SameM.refl (a : Store) : SameM a a := ⟨rfl⟩

theorem SameM.trans {a b c : Store} (h1 : SameM a b) (h2 : SameM b c) : SameM a c :=
  ⟨h1.hMax.trans h2.hMax⟩

/-- 最大の高さの carrier: store の `hMax` は bodies のどれかの `D` の導出の高さ。 -/
def MCarrier (e : ProtocolEnv) (cfg : HeightConfig) (st : NamedStore) : Prop :=
  ∃ D, D ∈ st.bodies.elems ∧ (deriveNamed e cfg D).h = st.core.hMax

/-- bodies が等しく `hMax` が等しい別の store へ移す。 -/
theorem MCarrier.congr {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : MCarrier e cfg st)
    {st' : NamedStore} (hb : st'.bodies = st.bodies) (hc : SameM st'.core st.core) : MCarrier e cfg st' := by
  obtain ⟨D, hD, hh⟩ := h
  exact ⟨D, by rw [hb]; exact hD, hh.trans hc.hMax.symm⟩

/-- bodies に 1 つ足しても carrier は残る。 -/
theorem MCarrier.insert {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : MCarrier e cfg st)
    {st' : NamedStore} (hb : st'.bodies = st.bodies.insert B) (hc : SameM st'.core st.core) : MCarrier e cfg st' := by
  obtain ⟨D, hD, hh⟩ := h
  refine ⟨D, ?_, hh.trans hc.hMax.symm⟩
  rw [hb, mem_insert_iff nb_compare_eq_iff]
  exact Or.inr hD

/-- 初期 store は carrier を持つ(genesis。高さはどちらも 1)。 -/
theorem initial_mcarrier (e : ProtocolEnv) (cfg : HeightConfig) : MCarrier e cfg initialNamedStore :=
  ⟨NamedBlock.Genesis, (mem_singleton_iff _ _).mpr rfl, rfl⟩

/-! ## `Store` のハンドラ -/

theorem onGoldfishVote_sameM (st : Store) (u : GoldfishVote) : SameM (onGoldfishVote st u) st := by
  unfold onGoldfishVote
  split_ifs <;> exact ⟨rfl⟩

theorem onGoldfishVoteChecked_sameM (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    SameM (onGoldfishVoteChecked c st u) st := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact SameM.refl _
  · exact onGoldfishVote_sameM st u

theorem foldl_sameM {β : Type} (g : Store → β → Store) (hg : ∀ s x, SameM (g s x) s) :
    ∀ (l : List β) (s : Store), SameM (List.foldl g s l) s
  | [], _ => SameM.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (foldl_sameM g hg l _).trans (hg s x)

theorem onSgVote_sameM (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (a : CombinedAttestation) :
    SameM (onSgVote hc st a) st := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact ⟨rfl⟩

theorem updateConfirmationWith_sameM (c : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (s : Nat) :
    SameM (updateConfirmationWith c e hc st s) st := ⟨rfl⟩

theorem goldfishVoteWith_sameM (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : Store) : SameM (goldfishVoteWith c cache e hc nd st).1 st := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_sameM c st _
  · exact SameM.refl _

/-- `updateFinality` の `hMax` は `max hMax σ.h`(`j` / `f` の更新は `hMax` を変えない)。 -/
theorem updateFinality_hMax (st : Store) (σ : ChainState) :
    (updateFinality st σ).hMax = max st.hMax σ.h := by
  unfold updateFinality
  dsimp only
  split_ifs <;> rfl

/-- 受理の分岐の `hMax` は `max hMax post.h`。 -/
theorem acceptBody_hMax (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    (acceptBody c st b post).hMax = max st.hMax post.h := by
  have hu : SameM (unpackedOf c st b post) st :=
    (foldl_sameM (fun acc u => onGoldfishVoteChecked c acc u) (fun s u => onGoldfishVoteChecked_sameM c s u)
      (gfVotes b) (storedOf st b post)).trans ⟨rfl⟩
  show (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).hMax =
    max st.hMax post.h
  rw [updateFinality_hMax, JustifiedCarrier.unpackedOf_chainState, hu.hMax]

/-! ## `NamedStore` のハンドラ -/

/-- `processBlockCore` は carrier を保つ(本体。`JustifiedCarrier.processBlockCore_jcarrier` と同じ経路)。 -/
theorem processBlockCore_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (hc : Model.Consensus.Protocol.Grades.HealConfig) {st : NamedStore}
    (h : StoreInv e cfg st) (hm : MCarrier e cfg st) (B : NamedBlock) :
    MCarrier e cfg (processBlockCore c p e hc cfg st B) := by
  unfold processBlockCore
  split_ifs with hpar
  · exact hm
  · have hparent : namedParent B ∈ st.bodies.elems := by
      rw [← contains_iff_mem nb_compare_eq_iff]
      cases hcp : st.bodies.contains (namedParent B) with
      | true => rfl
      | false => exact absurd (by simp [hcp]) hpar
    dsimp only
    rcases onBlockCheckedUsing_eq (fun cur => onBlockUsing c p cur (eraseBlock B)
        (fun ps => namedTransition e cfg ps B)) hc st.core (eraseBlock B) with hafter | hafter
    · rw [hafter]
      rcases onBlockUsing_eq c p st.core (eraseBlock B) (fun ps => namedTransition e cfg ps B)
          with hb | ⟨hnb, _, hb⟩
      · rw [hb, commitBlock_self]
        exact hm
      · rw [hb]
        have hpost : namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B =
            deriveNamed e cfg B := by
          rw [parent_eraseBlock, h.sigma _ hparent]
          cases B with
          | Genesis => exact absurd (h.tree _ hparent) hnb
          | Node p s r v sup rows i => rfl
        show MCarrier e cfg (commitBlock st (acceptBody c st.core (eraseBlock B)
          (namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B)) B)
        rw [hpost]
        have hnotin : st.core.tree.contains (eraseBlock B) = false := by
          cases hx : st.core.tree.contains (eraseBlock B) with
          | false => rfl
          | true => exact absurd ((contains_iff_mem block_compare_eq_iff _ _).mp hx) hnb
        have hin : (acceptBody c st.core (eraseBlock B) (deriveNamed e cfg B)).tree.contains (eraseBlock B) = true := by
          rw [contains_iff_mem block_compare_eq_iff, acceptBody_tree, mem_insert_iff block_compare_eq_iff]
          exact Or.inl rfl
        rw [commitBlock_accept hnotin hin]
        have hmax := acceptBody_hMax c st.core (eraseBlock B) (deriveNamed e cfg B)
        rcases le_total (deriveNamed e cfg B).h st.core.hMax with hle | hle
        · exact hm.insert rfl ⟨hmax.trans (max_eq_left hle)⟩
        · refine ⟨B, (mem_insert_iff nb_compare_eq_iff _ _ _).mpr (Or.inl rfl), ?_⟩
          show (deriveNamed e cfg B).h = (acceptBody c st.core (eraseBlock B) (deriveNamed e cfg B)).hMax
          rw [hmax, max_eq_right hle]
    · rw [hafter, commitBlock_self]
      exact hm

theorem admitRow_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : MCarrier e cfg st) (row : NamedAttestation) : MCarrier e cfg (admitRow hc st row) := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact h.congr rfl (onSgVote_sameM hc st.core _)

theorem admitRows_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    ∀ (rows : List NamedAttestation) {st : NamedStore}, MCarrier e cfg st → MCarrier e cfg (admitRows hc st rows)
  | [], _, h => h
  | row :: rows, st, h => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_mcarrier hc rows (admitRow_mcarrier hc h row)
    unfold admitRows at ih
    exact ih

theorem admitCarried_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (adm : CarriedAdmission)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (before : NamedStore) {after : NamedStore}
    (h : MCarrier e cfg after) (b : NamedBlock) : MCarrier e cfg (admitCarried adm hc before after b) := by
  unfold admitCarried
  split_ifs
  · exact admitRows_mcarrier hc _ h
  · exact h

theorem onBlockWith_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (adm : CarriedAdmission) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : StoreInv e cfg st) (hm : MCarrier e cfg st) (b : NamedBlock) :
    MCarrier e cfg (onBlockWith c p adm e hc cfg st b) := by
  unfold onBlockWith
  exact admitCarried_mcarrier adm hc st (processBlockCore_mcarrier c p hc h hm b) b

theorem receiptProcess_mcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} (h : StoreInv s.e s.cfg st)
    (hm : MCarrier s.e s.cfg st) (o : Model.Consensus.Execution.Objects.NamedObject) :
    MCarrier s.e s.cfg (receiptProcess c p s st o) := by
  cases o with
  | Block b => exact onBlockWith_mcarrier c p _ _ h hm b
  | GfVote u =>
    show MCarrier s.e s.cfg { st with core := onGoldfishVoteChecked c st.core u }
    exact hm.congr rfl (onGoldfishVoteChecked_sameM c st.core u)
  | Attest a =>
    show MCarrier s.e s.cfg (admitRow s.hc st a)
    exact admitRow_mcarrier s.hc hm a

theorem nodeProcess_mcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (h : StoreInv s.e s.cfg n.st)
    (hm : MCarrier s.e s.cfg n.st) (o : Model.Consensus.Execution.Objects.NamedObject) :
    MCarrier s.e s.cfg (nodeProcess c p s n o).st :=
  receiptProcess_mcarrier c p s h hm o

/-! ## Tick の務め -/

theorem proposeBlockWith_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : StoreInv e cfg st) (hm : MCarrier e cfg st) :
    MCarrier e cfg (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  unfold proposeBlockWith
  split
  · exact hm
  · rename_i b _
    exact onBlockWith_mcarrier c p CarriedAdmission.AlsoCarried hc h hm b

theorem namedGoldfishVoteWith_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : MCarrier e cfg st) :
    MCarrier e cfg (namedGoldfishVoteWith c cache e hc nd st).1 := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show MCarrier e cfg { st with core := core }
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  refine h.congr rfl ?_
  rw [h1]
  exact goldfishVoteWith_sameM c cache e hc nd st.core

theorem namedUpdateConfirmationWith_mcarrier {e : ProtocolEnv} {cfg : HeightConfig}
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : MCarrier e cfg st) (k : Nat) :
    MCarrier e cfg (namedUpdateConfirmationWith cache e hc st k) :=
  h.congr rfl (updateConfirmationWith_sameM cache e hc st.core k)

theorem attestWith_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : MCarrier e cfg st) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    MCarrier e cfg (attestWith cache e hc nd st rec).1 := by
  unfold attestWith
  split
  exact admitRow_mcarrier hc h _

/-- 1 tick の務め `tick` は carrier を保つ(`Carrier.tick_inv` と同じ 16 経路。提案だけが `StoreInv` を要する)。 -/
theorem tick_mcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : StoreInv e cfg st) (hm : MCarrier e cfg st)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    MCarrier e cfg (tick c p a nr cache e hc cfg nd st rec t).1 := by
  have h0 : StoreInv e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    h.congr rfl ⟨rfl, rfl, rfl⟩
  have hm0 : MCarrier e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    hm.congr rfl ⟨rfl⟩
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact attestWith_mcarrier cache hc nd (namedUpdateConfirmationWith_mcarrier cache hc (namedGoldfishVoteWith_mcarrier c cache hc nd (proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0)) _) _
    | with_reducible exact attestWith_mcarrier cache hc nd (namedUpdateConfirmationWith_mcarrier cache hc (namedGoldfishVoteWith_mcarrier c cache hc nd hm0) _) _
    | with_reducible exact attestWith_mcarrier cache hc nd (namedUpdateConfirmationWith_mcarrier cache hc (proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0) _) _
    | with_reducible exact attestWith_mcarrier cache hc nd (namedUpdateConfirmationWith_mcarrier cache hc hm0 _) _
    | with_reducible exact attestWith_mcarrier cache hc nd (namedGoldfishVoteWith_mcarrier c cache hc nd (proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0)) _
    | with_reducible exact attestWith_mcarrier cache hc nd (namedGoldfishVoteWith_mcarrier c cache hc nd hm0) _
    | with_reducible exact attestWith_mcarrier cache hc nd (proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0) _
    | with_reducible exact attestWith_mcarrier cache hc nd hm0 _
    | with_reducible exact namedUpdateConfirmationWith_mcarrier cache hc (namedGoldfishVoteWith_mcarrier c cache hc nd (proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0)) _
    | with_reducible exact namedUpdateConfirmationWith_mcarrier cache hc (namedGoldfishVoteWith_mcarrier c cache hc nd hm0) _
    | with_reducible exact namedUpdateConfirmationWith_mcarrier cache hc (proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0) _
    | with_reducible exact namedUpdateConfirmationWith_mcarrier cache hc hm0 _
    | with_reducible exact namedGoldfishVoteWith_mcarrier c cache hc nd (proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0)
    | with_reducible exact namedGoldfishVoteWith_mcarrier c cache hc nd hm0
    | with_reducible exact proposeBlockWith_mcarrier c p nr cache hc nd h0 hm0
    | with_reducible exact hm0

theorem nodeTick_mcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    {n : NamedNodeState} (h : StoreInv s.e s.cfg n.st) (hm : MCarrier s.e s.cfg n.st) (t : Int) :
    MCarrier s.e s.cfg (nodeTick c p a nr s v n t).1.st := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_mcarrier c p a nr _ s.hc _ h hm n.signing t

/-! ## world と run の読み -/

/-- world のどのノードの store も carrier を持つ。 -/
def WorldM (e : ProtocolEnv) (cfg : HeightConfig) (w : NamedWorld) : Prop :=
  ∀ v, MCarrier e cfg (worldAt w v).st

theorem worldInit_mcarrier (e : ProtocolEnv) (cfg : HeightConfig) : WorldM e cfg worldInit := fun _ =>
  initial_mcarrier e cfg

theorem worldStep_mcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) {w : NamedWorld}
    (h : WorldInv s.e s.cfg w) (hm : WorldM s.e s.cfg w) (ev : NamedEvent) :
    WorldM s.e s.cfg (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_mcarrier c p a nr s u (h u) (hm u) t
    · rw [hw]
      exact hm v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_mcarrier c p s (h u) (hm u) o
    · rw [hw]
      exact hm v

theorem foldl_worldStep_mcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, WorldInv s.e s.cfg w → WorldM s.e s.cfg w →
      WorldM s.e s.cfg (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, _, hm => hm
  | ev :: l, _, h, hm => by
    rw [List.foldl_cons]
    exact foldl_worldStep_mcarrier c p a nr s l (worldStep_inv c p a nr s h ev) (worldStep_mcarrier c p a nr s h hm ev)

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の直前の world は carrier を持つ。 -/
theorem stateBefore_mcarrier (i : Nat) : WorldM s.e s.cfg (stateBefore c p a nr s rho i) := by
  unfold stateBefore
  exact foldl_worldStep_mcarrier c p a nr s _ (worldInit_inv s.e s.cfg) (worldInit_mcarrier s.e s.cfg)

/-- 時刻 `t` の読み `readAt` の world は carrier を持つ。 -/
theorem readAt_mcarrier (t : Int) : WorldM s.e s.cfg (readAt c p a nr s rho t) := by
  unfold readAt
  exact foldl_worldStep_mcarrier c p a nr s _ (worldInit_inv s.e s.cfg) (worldInit_mcarrier s.e s.cfg)

/-- 時刻 `< t` の読み `stateBeforeTime` の world は carrier を持つ(手書き
`Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime`)。 -/
theorem stateBeforeTime_mcarrier (t : Int) : WorldM s.e s.cfg (stateBeforeTime c p a nr s rho t) := by
  unfold stateBeforeTime
  exact foldl_worldStep_mcarrier c p a nr s _ (worldInit_inv s.e s.cfg) (worldInit_mcarrier s.e s.cfg)

/-- **読みの最大の高さの carrier**: 時刻 `< t` の読みの `v` の store には、bodies の名前付きブロック `W` で、消去が tree にあり、
`sigma` のその鍵の値が `W` の導出で、その高さが `hMax` に等しいものがある(手書き `maximum_carrier_stateBeforeTime` の
`W ∈ bodies` と `derive_named W).h = h_max`。`StoreInv` の `tree` / `sigma` を合わせた形)。 -/
theorem stateBeforeTime_maxCarrier (t : Int) (v : ValidatorId) :
    ∃ W, W ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.bodies.elems ∧
      eraseBlock W ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.core.tree.elems ∧
      chainStateOf (worldAt (stateBeforeTime c p a nr s rho t) v).st.core.sigma (eraseBlock W) =
        deriveNamed s.e s.cfg W ∧
      (deriveNamed s.e s.cfg W).h = (worldAt (stateBeforeTime c p a nr s rho t) v).st.core.hMax := by
  obtain ⟨W, hW, hh⟩ := stateBeforeTime_mcarrier c p a nr s rho t v
  have hinv := JustifiedCarrier.stateBeforeTime_inv c p a nr s rho t v
  exact ⟨W, hW, hinv.tree W hW, hinv.sigma W hW, hh⟩

end Run

end Proofs.Consensus.MaxCarrier
