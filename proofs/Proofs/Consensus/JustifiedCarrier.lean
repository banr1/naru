import Proofs.Consensus.Carrier
import Proofs.Consensus.Derivation
import Mathlib.Tactic

/-!
# store の justified carrier と FG root の由来(C71 の補題)

`ProposerRoot` に残る「honest な読みの FG root を共通の上界で抑える」ことの最初の層。手書きでは
`HealingSurface.fgRoot_justificationSource_at_read`(`Protocol/ChainState/FGRootWitness.lean`。FG root はどちらの分岐でも
store のどれかのブロックの導出の `J`)が `fgRoot_confirmationWitness_at_read`(同じファイル。FG root は genesis か honest な
checkpoint の witness)の出発点になっている。

- **justified carrier**: store の `j` / `hJ` を書くのは `updateFinality` だけで、そこで書く値は受理したばかりのブロック `B` の
  chain 状態 `post` の `j` / `hJ`。`Carrier.StoreInv` の `sigma` から `post = deriveNamed e cfg B` なので、`(j, hJ)` は常に bodies の
  どれかの `D` の導出の `(j, hJ)` に等しい(`JCarrier`)。他のハンドラは `j` / `hJ` を変えず(`SameJ`)、bodies は増えるだけ。
  初期 store は `bodies = {Genesis}` で、genesis の導出の `(j, hJ)` は初期 store のもの。`Carrier.lean` と同じ順に
  `Store` → `NamedStore` → tick / 配送 → world → run の読みに積む(`stateBefore_jcarrier` / `readAt_jcarrier` /
  `stateBeforeTime_jcarrier`。前提なし)。
- **FG root の由来**: `getFgRoot` は `j` か `f` を返す(`fgRoot_eq`)ので、FG root は bodies のどれかの `D` の導出の `j` か `f`
  (`fgRoot_source`)。導出の `j` / `f` は `D` の消去の祖先(`Derivation.deriveNamed_inv`)なので、FG root は bodies のどれかの
  消去の祖先で、その消去は tree にある(`fgRoot_preceq_body`)。run のどの読み(`stateBefore` / `storeAt` / `stateBeforeTime`)でも
  前提なしに成り立つ(`stateBefore_fgRoot_source` / `storeAt_fgRoot_source` / `stateBeforeTime_fgRoot_source` と `_preceq_body`)。

手書きの対応: `Proofs.Bridges.storeJustificationOnChain_stateBeforeTime` / `storeFinalizationOnChain_stateBeforeTime`
(`Protocol/Evidence/ProvenanceBridge.lean`。`HealingSurface.fgRoot_justificationSource_at_read` の 2 つの分岐)。手書きは finalized の
分岐をさらに導出の justified な祖先の `J` に言い換える(`FGRootWitness.lean` の private な `named_finalized_justificationAncestor`)。
ここではその言い換えはせず、`f` の分岐はそのまま返す(手書きより弱い)。
-/

namespace Proofs.Consensus.JustifiedCarrier

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Tables Proofs.Consensus.NamedBlocks
open Proofs.Consensus.Runs Proofs.Consensus.Carrier

/-! ## 不変条件 -/

/-- `j` / `hJ` の欄が等しい。 -/
structure SameJ (a b : Store) : Prop where
  j : a.j = b.j
  hJ : a.hJ = b.hJ

theorem SameJ.refl (a : Store) : SameJ a a := ⟨rfl, rfl⟩

theorem SameJ.trans {a b c : Store} (h1 : SameJ a b) (h2 : SameJ b c) : SameJ a c :=
  ⟨h1.j.trans h2.j, h1.hJ.trans h2.hJ⟩

/-- justified carrier: store の `(j, hJ)` は bodies のどれかの `D` の導出の `(j, hJ)`。 -/
def JCarrier (e : ProtocolEnv) (cfg : HeightConfig) (st : NamedStore) : Prop :=
  ∃ D, D ∈ st.bodies.elems ∧ (deriveNamed e cfg D).j = st.core.j ∧ (deriveNamed e cfg D).hJ = st.core.hJ

/-- bodies が等しく `j` / `hJ` が等しい別の store へ移す。 -/
theorem JCarrier.congr {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : JCarrier e cfg st)
    {st' : NamedStore} (hb : st'.bodies = st.bodies) (hc : SameJ st'.core st.core) : JCarrier e cfg st' := by
  obtain ⟨D, hD, hj, hh⟩ := h
  exact ⟨D, by rw [hb]; exact hD, hj.trans hc.j.symm, hh.trans hc.hJ.symm⟩

/-- bodies に 1 つ足しても carrier は残る。 -/
theorem JCarrier.insert {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : JCarrier e cfg st)
    {st' : NamedStore} (hb : st'.bodies = st.bodies.insert B) (hc : SameJ st'.core st.core) : JCarrier e cfg st' := by
  obtain ⟨D, hD, hj, hh⟩ := h
  refine ⟨D, ?_, hj.trans hc.j.symm, hh.trans hc.hJ.symm⟩
  rw [hb, mem_insert_iff nb_compare_eq_iff]
  exact Or.inr hD

/-- 初期 store は carrier を持つ(genesis)。 -/
theorem initial_jcarrier (e : ProtocolEnv) (cfg : HeightConfig) : JCarrier e cfg initialNamedStore :=
  ⟨NamedBlock.Genesis, (mem_singleton_iff _ _).mpr rfl, rfl, rfl⟩

/-! ## `Store` のハンドラ -/

theorem onGoldfishVote_sameJ (st : Store) (u : GoldfishVote) : SameJ (onGoldfishVote st u) st := by
  unfold onGoldfishVote
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem onGoldfishVoteChecked_sameJ (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    SameJ (onGoldfishVoteChecked c st u) st := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact SameJ.refl _
  · exact onGoldfishVote_sameJ st u

theorem foldl_sameJ {β : Type} (g : Store → β → Store) (hg : ∀ s x, SameJ (g s x) s) :
    ∀ (l : List β) (s : Store), SameJ (List.foldl g s l) s
  | [], _ => SameJ.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (foldl_sameJ g hg l _).trans (hg s x)

theorem onSgVote_sameJ (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (a : CombinedAttestation) :
    SameJ (onSgVote hc st a) st := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem updateConfirmationWith_sameJ (c : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (s : Nat) :
    SameJ (updateConfirmationWith c e hc st s) st := ⟨rfl, rfl⟩

theorem goldfishVoteWith_sameJ (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : Store) : SameJ (goldfishVoteWith c cache e hc nd st).1 st := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_sameJ c st _
  · exact SameJ.refl _

/-- `updateFinality` の `(j, hJ)` は元のままか `σ` のもの。 -/
theorem updateFinality_j (st : Store) (σ : ChainState) :
    SameJ (updateFinality st σ) st ∨ ((updateFinality st σ).j = σ.j ∧ (updateFinality st σ).hJ = σ.hJ) := by
  unfold updateFinality
  dsimp only
  split_ifs
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- 受理の分岐の store が読む受理したブロックの chain 状態は `post`。 -/
theorem unpackedOf_chainState (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    chainStateOf (unpackedOf c st b post).sigma b = post := by
  rw [(unpackedOf_same c st b post).sigma]
  show NaruStd.Table.getOr (st.sigma.insert b post) b initialChainState = post
  rw [getOr_insert_self block_compare_eq_iff]

/-- 受理の分岐の `(j, hJ)` は元のままか `post` のもの。 -/
theorem acceptBody_j (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    SameJ (acceptBody c st b post) st ∨ ((acceptBody c st b post).j = post.j ∧ (acceptBody c st b post).hJ = post.hJ) := by
  have hu : SameJ (unpackedOf c st b post) st :=
    (foldl_sameJ (fun acc u => onGoldfishVoteChecked c acc u) (fun s u => onGoldfishVoteChecked_sameJ c s u)
      (gfVotes b) (storedOf st b post)).trans ⟨rfl, rfl⟩
  rcases updateFinality_j (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b) with h | h
  · exact Or.inl (h.trans hu)
  · right
    show (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).j = post.j ∧
      (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).hJ = post.hJ
    rw [unpackedOf_chainState] at h ⊢
    exact h

/-! ## `NamedStore` のハンドラ -/

/-- `processBlockCore` は carrier を保つ(本体。`Carrier.processBlockCore_inv` と同じ経路)。 -/
theorem processBlockCore_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (hc : Model.Consensus.Protocol.Grades.HealConfig) {st : NamedStore}
    (h : StoreInv e cfg st) (hj : JCarrier e cfg st) (B : NamedBlock) :
    JCarrier e cfg (processBlockCore c p e hc cfg st B) := by
  unfold processBlockCore
  split_ifs with hpar
  · exact hj
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
        exact hj
      · rw [hb]
        have hpost : namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B =
            deriveNamed e cfg B := by
          rw [parent_eraseBlock, h.sigma _ hparent]
          cases B with
          | Genesis => exact absurd (h.tree _ hparent) hnb
          | Node p s r v sup rows i => rfl
        show JCarrier e cfg (commitBlock st (acceptBody c st.core (eraseBlock B)
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
        rcases acceptBody_j c st.core (eraseBlock B) (deriveNamed e cfg B) with hs | ⟨hj1, hj2⟩
        · exact hj.insert rfl hs
        · exact ⟨B, (mem_insert_iff nb_compare_eq_iff _ _ _).mpr (Or.inl rfl), hj1.symm, hj2.symm⟩
    · rw [hafter, commitBlock_self]
      exact hj

theorem admitRow_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : JCarrier e cfg st) (row : NamedAttestation) : JCarrier e cfg (admitRow hc st row) := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact h.congr rfl (onSgVote_sameJ hc st.core _)

theorem admitRows_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    ∀ (rows : List NamedAttestation) {st : NamedStore}, JCarrier e cfg st → JCarrier e cfg (admitRows hc st rows)
  | [], _, h => h
  | row :: rows, st, h => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_jcarrier hc rows (admitRow_jcarrier hc h row)
    unfold admitRows at ih
    exact ih

theorem admitCarried_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (adm : CarriedAdmission)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (before : NamedStore) {after : NamedStore}
    (h : JCarrier e cfg after) (b : NamedBlock) : JCarrier e cfg (admitCarried adm hc before after b) := by
  unfold admitCarried
  split_ifs
  · exact admitRows_jcarrier hc _ h
  · exact h

theorem onBlockWith_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (adm : CarriedAdmission) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : StoreInv e cfg st) (hj : JCarrier e cfg st) (b : NamedBlock) :
    JCarrier e cfg (onBlockWith c p adm e hc cfg st b) := by
  unfold onBlockWith
  exact admitCarried_jcarrier adm hc st (processBlockCore_jcarrier c p hc h hj b) b

theorem receiptProcess_jcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} (h : StoreInv s.e s.cfg st)
    (hj : JCarrier s.e s.cfg st) (o : Model.Consensus.Execution.Objects.NamedObject) :
    JCarrier s.e s.cfg (receiptProcess c p s st o) := by
  cases o with
  | Block b => exact onBlockWith_jcarrier c p _ _ h hj b
  | GfVote u =>
    show JCarrier s.e s.cfg { st with core := onGoldfishVoteChecked c st.core u }
    exact hj.congr rfl (onGoldfishVoteChecked_sameJ c st.core u)
  | Attest a =>
    show JCarrier s.e s.cfg (admitRow s.hc st a)
    exact admitRow_jcarrier s.hc hj a

theorem nodeProcess_jcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (h : StoreInv s.e s.cfg n.st)
    (hj : JCarrier s.e s.cfg n.st) (o : Model.Consensus.Execution.Objects.NamedObject) :
    JCarrier s.e s.cfg (nodeProcess c p s n o).st :=
  receiptProcess_jcarrier c p s h hj o

/-! ## Tick の務め -/

theorem proposeBlockWith_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : StoreInv e cfg st) (hj : JCarrier e cfg st) :
    JCarrier e cfg (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  unfold proposeBlockWith
  split
  · exact hj
  · rename_i b _
    exact onBlockWith_jcarrier c p CarriedAdmission.AlsoCarried hc h hj b

theorem namedGoldfishVoteWith_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : JCarrier e cfg st) :
    JCarrier e cfg (namedGoldfishVoteWith c cache e hc nd st).1 := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show JCarrier e cfg { st with core := core }
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  refine h.congr rfl ?_
  rw [h1]
  exact goldfishVoteWith_sameJ c cache e hc nd st.core

theorem namedUpdateConfirmationWith_jcarrier {e : ProtocolEnv} {cfg : HeightConfig}
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : JCarrier e cfg st) (k : Nat) :
    JCarrier e cfg (namedUpdateConfirmationWith cache e hc st k) :=
  h.congr rfl (updateConfirmationWith_sameJ cache e hc st.core k)

theorem attestWith_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : JCarrier e cfg st) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    JCarrier e cfg (attestWith cache e hc nd st rec).1 := by
  unfold attestWith
  split
  exact admitRow_jcarrier hc h _

/-- 1 tick の務め `tick` は carrier を保つ(`Carrier.tick_inv` と同じ 16 経路。提案だけが `StoreInv` を要する)。 -/
theorem tick_jcarrier {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : StoreInv e cfg st) (hj : JCarrier e cfg st)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    JCarrier e cfg (tick c p a nr cache e hc cfg nd st rec t).1 := by
  have h0 : StoreInv e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    h.congr rfl ⟨rfl, rfl, rfl⟩
  have hj0 : JCarrier e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    hj.congr rfl ⟨rfl, rfl⟩
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact attestWith_jcarrier cache hc nd (namedUpdateConfirmationWith_jcarrier cache hc (namedGoldfishVoteWith_jcarrier c cache hc nd (proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0)) _) _
    | with_reducible exact attestWith_jcarrier cache hc nd (namedUpdateConfirmationWith_jcarrier cache hc (namedGoldfishVoteWith_jcarrier c cache hc nd hj0) _) _
    | with_reducible exact attestWith_jcarrier cache hc nd (namedUpdateConfirmationWith_jcarrier cache hc (proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0) _) _
    | with_reducible exact attestWith_jcarrier cache hc nd (namedUpdateConfirmationWith_jcarrier cache hc hj0 _) _
    | with_reducible exact attestWith_jcarrier cache hc nd (namedGoldfishVoteWith_jcarrier c cache hc nd (proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0)) _
    | with_reducible exact attestWith_jcarrier cache hc nd (namedGoldfishVoteWith_jcarrier c cache hc nd hj0) _
    | with_reducible exact attestWith_jcarrier cache hc nd (proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0) _
    | with_reducible exact attestWith_jcarrier cache hc nd hj0 _
    | with_reducible exact namedUpdateConfirmationWith_jcarrier cache hc (namedGoldfishVoteWith_jcarrier c cache hc nd (proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0)) _
    | with_reducible exact namedUpdateConfirmationWith_jcarrier cache hc (namedGoldfishVoteWith_jcarrier c cache hc nd hj0) _
    | with_reducible exact namedUpdateConfirmationWith_jcarrier cache hc (proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0) _
    | with_reducible exact namedUpdateConfirmationWith_jcarrier cache hc hj0 _
    | with_reducible exact namedGoldfishVoteWith_jcarrier c cache hc nd (proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0)
    | with_reducible exact namedGoldfishVoteWith_jcarrier c cache hc nd hj0
    | with_reducible exact proposeBlockWith_jcarrier c p nr cache hc nd h0 hj0
    | with_reducible exact hj0

theorem nodeTick_jcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    {n : NamedNodeState} (h : StoreInv s.e s.cfg n.st) (hj : JCarrier s.e s.cfg n.st) (t : Int) :
    JCarrier s.e s.cfg (nodeTick c p a nr s v n t).1.st := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_jcarrier c p a nr _ s.hc _ h hj n.signing t

/-! ## world と run の読み -/

/-- world のどのノードの store も carrier を持つ。 -/
def WorldJ (e : ProtocolEnv) (cfg : HeightConfig) (w : NamedWorld) : Prop :=
  ∀ v, JCarrier e cfg (worldAt w v).st

theorem worldInit_jcarrier (e : ProtocolEnv) (cfg : HeightConfig) : WorldJ e cfg worldInit := fun _ =>
  initial_jcarrier e cfg

theorem worldStep_jcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) {w : NamedWorld}
    (h : WorldInv s.e s.cfg w) (hj : WorldJ s.e s.cfg w) (ev : NamedEvent) :
    WorldJ s.e s.cfg (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_jcarrier c p a nr s u (h u) (hj u) t
    · rw [hw]
      exact hj v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_jcarrier c p s (h u) (hj u) o
    · rw [hw]
      exact hj v

theorem foldl_worldStep_jcarrier (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, WorldInv s.e s.cfg w → WorldJ s.e s.cfg w →
      WorldJ s.e s.cfg (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, _, hj => hj
  | ev :: l, _, h, hj => by
    rw [List.foldl_cons]
    exact foldl_worldStep_jcarrier c p a nr s l (worldStep_inv c p a nr s h ev) (worldStep_jcarrier c p a nr s h hj ev)

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の直前の world は carrier を持つ。 -/
theorem stateBefore_jcarrier (i : Nat) : WorldJ s.e s.cfg (stateBefore c p a nr s rho i) := by
  unfold stateBefore
  exact foldl_worldStep_jcarrier c p a nr s _ (worldInit_inv s.e s.cfg) (worldInit_jcarrier s.e s.cfg)

/-- 時刻 `t` の読み `readAt` の world は carrier を持つ。 -/
theorem readAt_jcarrier (t : Int) : WorldJ s.e s.cfg (readAt c p a nr s rho t) := by
  unfold readAt
  exact foldl_worldStep_jcarrier c p a nr s _ (worldInit_inv s.e s.cfg) (worldInit_jcarrier s.e s.cfg)

/-- 時刻 `< t` の読み `stateBeforeTime` の world は carrier を持つ。 -/
theorem stateBeforeTime_jcarrier (t : Int) : WorldJ s.e s.cfg (stateBeforeTime c p a nr s rho t) := by
  unfold stateBeforeTime
  exact foldl_worldStep_jcarrier c p a nr s _ (worldInit_inv s.e s.cfg) (worldInit_jcarrier s.e s.cfg)

/-- 時刻 `< t` の読み `stateBeforeTime` の world は `StoreInv` を満たす(`Carrier.readAt_inv` の `<` の版)。 -/
theorem stateBeforeTime_inv (t : Int) : WorldInv s.e s.cfg (stateBeforeTime c p a nr s rho t) := by
  unfold stateBeforeTime
  exact foldl_worldStep_inv c p a nr s _ (worldInit_inv s.e s.cfg)

end Run

/-! ## FG root の由来 -/

/-- FG root は `j` か `f`。 -/
theorem fgRoot_eq (st : Store) :
    getFgRoot (storeToHealing st) = st.j ∨ getFgRoot (storeToHealing st) = st.f := by
  unfold getFgRoot
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- FG root は bodies のどれかの導出の `j` か `f`。 -/
theorem fgRoot_source {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st)
    (hj : JCarrier e cfg st) :
    ∃ D, D ∈ st.bodies.elems ∧
      (getFgRoot (storeToHealing st.core) = (deriveNamed e cfg D).j ∨
        getFgRoot (storeToHealing st.core) = (deriveNamed e cfg D).f) := by
  rcases fgRoot_eq st.core with hr | hr
  · obtain ⟨D, hD, hDj, -⟩ := hj
    exact ⟨D, hD, Or.inl (hr.trans hDj.symm)⟩
  · obtain ⟨D, hD, hDf⟩ := h.carrier
    exact ⟨D, hD, Or.inr (hr.trans hDf.symm)⟩

/-- FG root は bodies のどれかの消去の祖先で、その消去は tree にある。 -/
theorem fgRoot_preceq_body {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st)
    (hj : JCarrier e cfg st) :
    ∃ D, D ∈ st.bodies.elems ∧ eraseBlock D ∈ st.core.tree.elems ∧
      preceq (getFgRoot (storeToHealing st.core)) (eraseBlock D) = true := by
  obtain ⟨D, hD, hr⟩ := fgRoot_source h hj
  refine ⟨D, hD, h.tree D hD, ?_⟩
  have hinv := Proofs.Consensus.Derivation.deriveNamed_inv e cfg D
  rcases hr with hr | hr
  · rw [hr]; exact hinv.j_preceq
  · rw [hr]; exact hinv.f_preceq

section RunRoot

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の直前のノード `v` の FG root は、その bodies のどれかの導出の `j` か `f`(前提なし)。 -/
theorem stateBefore_fgRoot_source (i : Nat) (v : ValidatorId) :
    ∃ D, D ∈ (worldAt (stateBefore c p a nr s rho i) v).st.bodies.elems ∧
      (getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) = (deriveNamed s.e s.cfg D).j ∨
        getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) = (deriveNamed s.e s.cfg D).f) :=
  fgRoot_source (stateBefore_inv c p a nr s rho i v) (stateBefore_jcarrier c p a nr s rho i v)

/-- 時刻 `t` の読みの FG root は、その bodies のどれかの導出の `j` か `f`(前提なし)。 -/
theorem storeAt_fgRoot_source (v : ValidatorId) (t : Int) :
    ∃ D, D ∈ (storeAt c p a nr s rho v t).bodies.elems ∧
      (getFgRoot (storeToHealing (storeAt c p a nr s rho v t).core) = (deriveNamed s.e s.cfg D).j ∨
        getFgRoot (storeToHealing (storeAt c p a nr s rho v t).core) = (deriveNamed s.e s.cfg D).f) :=
  fgRoot_source (readAt_inv c p a nr s rho t v) (readAt_jcarrier c p a nr s rho t v)

/-- 時刻 `< t` の読みの FG root は、その bodies のどれかの導出の `j` か `f`(前提なし)。 -/
theorem stateBeforeTime_fgRoot_source (v : ValidatorId) (t : Int) :
    ∃ D, D ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.bodies.elems ∧
      (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) v).st.core) = (deriveNamed s.e s.cfg D).j ∨
        getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) v).st.core) = (deriveNamed s.e s.cfg D).f) :=
  fgRoot_source (stateBeforeTime_inv c p a nr s rho t v) (stateBeforeTime_jcarrier c p a nr s rho t v)

/-- 添字 `i` の直前のノード `v` の FG root は、その tree にある bodies の消去の祖先(前提なし)。 -/
theorem stateBefore_fgRoot_preceq_body (i : Nat) (v : ValidatorId) :
    ∃ D, D ∈ (worldAt (stateBefore c p a nr s rho i) v).st.bodies.elems ∧
      eraseBlock D ∈ (worldAt (stateBefore c p a nr s rho i) v).st.core.tree.elems ∧
      preceq (getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core)) (eraseBlock D) = true :=
  fgRoot_preceq_body (stateBefore_inv c p a nr s rho i v) (stateBefore_jcarrier c p a nr s rho i v)

/-- 時刻 `t` の読みの FG root は、その tree にある bodies の消去の祖先(前提なし)。 -/
theorem storeAt_fgRoot_preceq_body (v : ValidatorId) (t : Int) :
    ∃ D, D ∈ (storeAt c p a nr s rho v t).bodies.elems ∧
      eraseBlock D ∈ (storeAt c p a nr s rho v t).core.tree.elems ∧
      preceq (getFgRoot (storeToHealing (storeAt c p a nr s rho v t).core)) (eraseBlock D) = true :=
  fgRoot_preceq_body (readAt_inv c p a nr s rho t v) (readAt_jcarrier c p a nr s rho t v)

/-- 時刻 `< t` の読みの FG root は、その tree にある bodies の消去の祖先(前提なし)。 -/
theorem stateBeforeTime_fgRoot_preceq_body (v : ValidatorId) (t : Int) :
    ∃ D, D ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.bodies.elems ∧
      eraseBlock D ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.core.tree.elems ∧
      preceq (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) v).st.core)) (eraseBlock D) = true :=
  fgRoot_preceq_body (stateBeforeTime_inv c p a nr s rho t v) (stateBeforeTime_jcarrier c p a nr s rho t v)

end RunRoot

end Proofs.Consensus.JustifiedCarrier
