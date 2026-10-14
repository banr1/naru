import Model.Consensus.Execution.Run
import Model.Consensus.Protocol.Evidence
import Proofs.Consensus.Orders
import Proofs.Consensus.Sets
import Proofs.Consensus.Tables
import Proofs.Consensus.NamedBlocks
import Proofs.Consensus.Runs
import Mathlib.Tactic

/-!
# store の finality carrier(C71 の補題)

生成 Model の `NamedStore`(`Model/Consensus/Protocol/Handlers.lean`)について、run のどの時点の honest なノードの store も
次の不変条件 `StoreInv` を満たすことを示す:
- `bodies` の各名前付きブロック `D` は、消去 `eraseBlock D` が `core.tree` にあり、chain 状態の表 `core.sigma` のその鍵の値
  (`chainStateOf core.sigma (eraseBlock D)`)が名前付き導出 `deriveNamed e cfg D` に等しい、
- finalized `core.f` は `bodies` のどれかの `D` の導出の `f` に等しい(finality carrier)。

`f` を書くのは `updateFinality` だけで、そこで書く値は受理したばかりのブロック `B` の chain 状態 `post` の `f`。`post` は
`onBlockUsing` が親の chain 状態 `chainStateOf sigma (parent (eraseBlock B))` から `namedTransition e cfg … B` で作るので、
親 `namedParent B ∈ bodies`(`processBlockCore` の最初の検査)の不変条件から `post = deriveNamed e cfg B` になる。
tree / sigma / bodies を書くのも同じ受理の経路だけで、他のハンドラ(vote / attestation / 確認の更新 / 時計合わせ)はこれらの欄を
変えない(`SameCore`)。初期状態は `bodies = {Genesis}`、`tree = {Block.Genesis}`、`sigma = ∅`、`f = Genesis` で成立する。
`Store` → `NamedStore` → `NamedNodeState`(`nodeTick` / `nodeProcess`)→ world(`worldStep` の畳み込み)の順に積み上げ、
`readAt` / `stateBefore` の world で `WorldInv` を得る。
手書き `FinalityCarrier.finality_carrier_stateBefore`(`DecoupledConsensusProofs/Protocol/Handlers/FinalityCarrier.lean`、
`CoreFinality`: `∃ D ∈ st.T, (st.σ D).F = st.F`)と `NamedRuntime.stateBefore_invariants`(`T = bodies.image erase`、
`σ (erase D) = derive_named D`)に当たる。
-/

namespace Proofs.Consensus.Carrier

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Tables Proofs.Consensus.NamedBlocks
open Proofs.Consensus.Runs

/-! ## 不変条件 -/

/-- 不変条件に関わる `Store` の欄(tree / sigma / f)が等しい。 -/
structure SameCore (a b : Store) : Prop where
  tree : a.tree = b.tree
  sigma : a.sigma = b.sigma
  f : a.f = b.f

theorem SameCore.refl (a : Store) : SameCore a a := ⟨rfl, rfl, rfl⟩

theorem SameCore.trans {a b c : Store} (h1 : SameCore a b) (h2 : SameCore b c) : SameCore a c :=
  ⟨h1.tree.trans h2.tree, h1.sigma.trans h2.sigma, h1.f.trans h2.f⟩

/-- store の不変条件(finality carrier)。`named` / `closed`(周回 126): tree の各ブロックは bodies のどれかの消去で、
bodies は名前付きの親について閉じている(手書き `T = bodies.image erase` と `NamedParentClosed`)。 -/
structure StoreInv (e : ProtocolEnv) (cfg : HeightConfig) (st : NamedStore) : Prop where
  tree : ∀ D, D ∈ st.bodies.elems → eraseBlock D ∈ st.core.tree.elems
  sigma : ∀ D, D ∈ st.bodies.elems → chainStateOf st.core.sigma (eraseBlock D) = deriveNamed e cfg D
  carrier : ∃ D, D ∈ st.bodies.elems ∧ (deriveNamed e cfg D).f = st.core.f
  named : ∀ B, B ∈ st.core.tree.elems → ∃ D, D ∈ st.bodies.elems ∧ eraseBlock D = B
  closed : ∀ D, D ∈ st.bodies.elems → namedParent D ∈ st.bodies.elems

/-- bodies と tree / sigma / f が等しい別の store へ移す。 -/
theorem StoreInv.congr {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st)
    {st' : NamedStore} (hb : st'.bodies = st.bodies) (hc : SameCore st'.core st.core) : StoreInv e cfg st' where
  tree := by rw [hb, hc.tree]; exact h.tree
  sigma := by rw [hb, hc.sigma]; exact h.sigma
  carrier := by rw [hb, hc.f]; exact h.carrier
  named := by rw [hb, hc.tree]; exact h.named
  closed := by rw [hb]; exact h.closed

/-- 初期 store は不変条件を満たす。 -/
theorem initial_inv (e : ProtocolEnv) (cfg : HeightConfig) : StoreInv e cfg initialNamedStore where
  tree := fun D hD => by
    have hD' : D ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD
    rw [mem_singleton_iff] at hD'
    subst hD'
    show eraseBlock NamedBlock.Genesis ∈ (NaruStd.Set.singleton Block.Genesis).elems
    exact (mem_singleton_iff _ _).mpr rfl
  sigma := fun D hD => by
    have hD' : D ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD
    rw [mem_singleton_iff] at hD'
    subst hD'
    rfl
  carrier := ⟨NamedBlock.Genesis, (mem_singleton_iff _ _).mpr rfl, rfl⟩
  named := fun B hB => by
    have hB' : B ∈ (NaruStd.Set.singleton Block.Genesis).elems := hB
    rw [mem_singleton_iff] at hB'
    subst hB'
    exact ⟨NamedBlock.Genesis, (mem_singleton_iff _ _).mpr rfl, rfl⟩
  closed := fun D hD => by
    have hD' : D ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD
    rw [mem_singleton_iff] at hD'
    subst hD'
    exact (mem_singleton_iff _ _).mpr rfl

/-! ## `Store` のハンドラ -/

theorem onGoldfishVote_same (st : Store) (u : GoldfishVote) : SameCore (onGoldfishVote st u) st := by
  unfold onGoldfishVote
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem onGoldfishVoteChecked_same (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    SameCore (onGoldfishVoteChecked c st u) st := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact SameCore.refl _
  · exact onGoldfishVote_same st u

theorem foldl_same {β : Type} (g : Store → β → Store) (hg : ∀ s x, SameCore (g s x) s) :
    ∀ (l : List β) (s : Store), SameCore (List.foldl g s l) s
  | [], _ => SameCore.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (foldl_same g hg l _).trans (hg s x)

theorem onSgVote_same (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (a : CombinedAttestation) :
    SameCore (onSgVote hc st a) st := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem updateConfirmationWith_same (c : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (s : Nat) :
    SameCore (updateConfirmationWith c e hc st s) st := ⟨rfl, rfl, rfl⟩

theorem goldfishVoteWith_same (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : Store) : SameCore (goldfishVoteWith c cache e hc nd st).1 st := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_same c st _
  · exact SameCore.refl _

/-- `updateFinality` は tree / sigma を変えず、`f` は元のままか `σ.f`。 -/
theorem updateFinality_fields (st : Store) (σ : ChainState) :
    (updateFinality st σ).tree = st.tree ∧ (updateFinality st σ).sigma = st.sigma ∧
      ((updateFinality st σ).f = st.f ∨ (updateFinality st σ).f = σ.f) := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, by first | exact Or.inl rfl | exact Or.inr rfl⟩

/-- `onBlockUsing` の受理の分岐: 受理したブロック `b` を tree / timestampBlock / sigma(値 `post`)に入れた store。 -/
def storedOf (st : Store) (b : Block) (post : ChainState) : Store :=
  { st with tree := st.tree.insert b,
            timestampBlock := st.timestampBlock.insert b (Model.Consensus.Objects.Time.Stamp.At st.t),
            sigma := st.sigma.insert b post }

/-- 受理の分岐: `storedOf` に `b` の goldfish vote を `onGoldfishVoteChecked` で入れた store。 -/
def unpackedOf (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) : Store :=
  List.foldl (fun acc u => onGoldfishVoteChecked c acc u) (storedOf st b post) (gfVotes b)

/-- 受理の分岐の結果(`onBlockUsing` の本体と定義的に等しい)。 -/
def acceptBody (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) : Store :=
  updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)

theorem unpackedOf_same (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    SameCore (unpackedOf c st b post) (storedOf st b post) :=
  foldl_same _ (fun s u => onGoldfishVoteChecked_same c s u) _ _

theorem acceptBody_tree (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    (acceptBody c st b post).tree = st.tree.insert b :=
  (updateFinality_fields _ _).1.trans (unpackedOf_same c st b post).tree

theorem acceptBody_sigma (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    (acceptBody c st b post).sigma = st.sigma.insert b post :=
  (updateFinality_fields _ _).2.1.trans (unpackedOf_same c st b post).sigma

theorem acceptBody_f (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    (acceptBody c st b post).f = st.f ∨ (acceptBody c st b post).f = post.f := by
  rcases (updateFinality_fields (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).2.2
    with hf | hf
  · exact Or.inl (hf.trans (unpackedOf_same c st b post).f)
  · right
    show (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).f = post.f
    rw [hf, (unpackedOf_same c st b post).sigma]
    show (NaruStd.Table.getOr (st.sigma.insert b post) b initialChainState).f = post.f
    rw [getOr_insert_self block_compare_eq_iff]

/-- `onBlockUsing` は store をそのまま返すか、`b ∉ tree` かつ `parent b ∈ tree` のとき受理の分岐(`acceptBody`)。 -/
theorem onBlockUsing_eq (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) :
    onBlockUsing c p st b build = st ∨
      (b ∉ st.tree.elems ∧ parent b ∈ st.tree.elems ∧
        onBlockUsing c p st b build = acceptBody c st b (build (chainStateOf st.sigma (parent b)))) := by
  unfold onBlockUsing
  split_ifs with h1
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    have hnb : st.tree.contains b = false := by
      cases hcb : st.tree.contains b with
      | false => rfl
      | true => exact absurd (by simp [hcb]) h1
    have hpb : st.tree.contains (parent b) = true := by
      cases hcp : st.tree.contains (parent b) with
      | true => rfl
      | false => exact absurd (by simp [hcp]) h1
    refine ⟨?_, (contains_iff_mem block_compare_eq_iff _ _).mp hpb, rfl⟩
    intro hm
    have := (contains_iff_mem block_compare_eq_iff st.tree b).mpr hm
    rw [this] at hnb
    exact Bool.noConfusion hnb

theorem onBlockCheckedUsing_eq (handle : Store → Store) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (st : Store) (b : Block) :
    onBlockCheckedUsing handle hc st b = handle st ∨ onBlockCheckedUsing handle hc st b = st := by
  unfold onBlockCheckedUsing
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## `NamedStore` のハンドラ -/

/-- core を変えない `commitBlock` は何もしない。 -/
theorem commitBlock_self (st : NamedStore) (B : NamedBlock) : commitBlock st st.core B = st := by
  unfold commitBlock
  dsimp only
  split_ifs with hc
  · exfalso
    cases hx : st.core.tree.contains (eraseBlock B) <;> simp [hx] at hc
  · rfl

/-- 受理したブロックの `commitBlock`: core を `after` に、bodies に `B` を入れる。 -/
theorem commitBlock_accept {before : NamedStore} {after : Store} {B : NamedBlock}
    (hnot : before.core.tree.contains (eraseBlock B) = false) (hin : after.tree.contains (eraseBlock B) = true) :
    commitBlock before after B = { before with core := after, bodies := before.bodies.insert B } := by
  unfold commitBlock
  dsimp only
  simp [hnot, hin]

/-- `processBlockCore` は不変条件を保つ(本体)。 -/
theorem processBlockCore_inv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (hc : Model.Consensus.Protocol.Grades.HealConfig) {st : NamedStore}
    (h : StoreInv e cfg st) (B : NamedBlock) : StoreInv e cfg (processBlockCore c p e hc cfg st B) := by
  unfold processBlockCore
  split_ifs with hpar
  · exact h
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
        exact h
      · rw [hb]
        have hpost : namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B =
            deriveNamed e cfg B := by
          rw [parent_eraseBlock, h.sigma _ hparent]
          cases B with
          | Genesis => exact absurd (h.tree _ hparent) hnb
          | Node p s r v sup rows i => rfl
        show StoreInv e cfg (commitBlock st (acceptBody c st.core (eraseBlock B)
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
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro D hD
          have hD' : D ∈ (st.bodies.insert B).elems := hD
          rw [mem_insert_iff nb_compare_eq_iff] at hD'
          show eraseBlock D ∈ (acceptBody c st.core (eraseBlock B) (deriveNamed e cfg B)).tree.elems
          rw [acceptBody_tree, mem_insert_iff block_compare_eq_iff]
          rcases hD' with rfl | hD'
          · exact Or.inl rfl
          · exact Or.inr (h.tree D hD')
        · intro D hD
          have hD' : D ∈ (st.bodies.insert B).elems := hD
          rw [mem_insert_iff nb_compare_eq_iff] at hD'
          show chainStateOf (acceptBody c st.core (eraseBlock B) (deriveNamed e cfg B)).sigma (eraseBlock D) =
            deriveNamed e cfg D
          unfold chainStateOf
          rw [acceptBody_sigma]
          rcases hD' with rfl | hD'
          · exact getOr_insert_self block_compare_eq_iff _ _ _ _
          · have hne : eraseBlock B ≠ eraseBlock D := fun heq => hnb (by rw [heq]; exact h.tree D hD')
            rw [getOr_insert_ne block_compare_eq_iff _ _ _ _ _ hne]
            exact h.sigma D hD'
        · rcases acceptBody_f c st.core (eraseBlock B) (deriveNamed e cfg B) with hf | hf
          · obtain ⟨D, hD, hDf⟩ := h.carrier
            refine ⟨D, (mem_insert_iff nb_compare_eq_iff _ _ _).mpr (Or.inr hD), ?_⟩
            show (deriveNamed e cfg D).f = (acceptBody c st.core (eraseBlock B) (deriveNamed e cfg B)).f
            rw [hf]
            exact hDf
          · exact ⟨B, (mem_insert_iff nb_compare_eq_iff _ _ _).mpr (Or.inl rfl), hf.symm⟩
        · intro X hX
          have hX' : X ∈ (acceptBody c st.core (eraseBlock B) (deriveNamed e cfg B)).tree.elems := hX
          rw [acceptBody_tree, mem_insert_iff block_compare_eq_iff] at hX'
          rcases hX' with rfl | hX'
          · exact ⟨B, (mem_insert_iff nb_compare_eq_iff _ _ _).mpr (Or.inl rfl), rfl⟩
          · obtain ⟨D, hD, hDX⟩ := h.named X hX'
            exact ⟨D, (mem_insert_iff nb_compare_eq_iff _ _ _).mpr (Or.inr hD), hDX⟩
        · intro D hD
          have hD' : D ∈ (st.bodies.insert B).elems := hD
          rw [mem_insert_iff nb_compare_eq_iff] at hD'
          show namedParent D ∈ (st.bodies.insert B).elems
          rw [mem_insert_iff nb_compare_eq_iff]
          rcases hD' with rfl | hD'
          · exact Or.inr hparent
          · exact Or.inr (h.closed D hD')
    · rw [hafter, commitBlock_self]
      exact h

theorem admitRow_inv {e : ProtocolEnv} {cfg : HeightConfig} (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : StoreInv e cfg st) (row : NamedAttestation) : StoreInv e cfg (admitRow hc st row) := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact h.congr rfl (onSgVote_same hc st.core _)

theorem admitRows_inv {e : ProtocolEnv} {cfg : HeightConfig} (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    ∀ (rows : List NamedAttestation) {st : NamedStore}, StoreInv e cfg st → StoreInv e cfg (admitRows hc st rows)
  | [], _, h => h
  | row :: rows, st, h => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_inv hc rows (admitRow_inv hc h row)
    unfold admitRows at ih
    exact ih

theorem admitCarried_inv {e : ProtocolEnv} {cfg : HeightConfig} (adm : CarriedAdmission)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (before : NamedStore) {after : NamedStore}
    (h : StoreInv e cfg after) (b : NamedBlock) : StoreInv e cfg (admitCarried adm hc before after b) := by
  unfold admitCarried
  split_ifs
  · exact admitRows_inv hc _ h
  · exact h

theorem onBlockWith_inv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (adm : CarriedAdmission) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : StoreInv e cfg st) (b : NamedBlock) : StoreInv e cfg (onBlockWith c p adm e hc cfg st b) := by
  unfold onBlockWith
  exact admitCarried_inv adm hc st (processBlockCore_inv c p hc h b) b

theorem receiptProcess_inv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} (h : StoreInv s.e s.cfg st)
    (o : Model.Consensus.Execution.Objects.NamedObject) : StoreInv s.e s.cfg (receiptProcess c p s st o) := by
  cases o with
  | Block b => exact onBlockWith_inv c p _ _ h b
  | GfVote u =>
    show StoreInv s.e s.cfg { st with core := onGoldfishVoteChecked c st.core u }
    exact h.congr rfl (onGoldfishVoteChecked_same c st.core u)
  | Attest a =>
    show StoreInv s.e s.cfg (admitRow s.hc st a)
    exact admitRow_inv s.hc h a

theorem nodeProcess_inv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (h : StoreInv s.e s.cfg n.st)
    (o : Model.Consensus.Execution.Objects.NamedObject) : StoreInv s.e s.cfg (nodeProcess c p s n o).st :=
  receiptProcess_inv c p s h o

/-! ## Tick の務め -/

theorem proposeBlockWith_inv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : StoreInv e cfg st) : StoreInv e cfg (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  unfold proposeBlockWith
  split
  · exact h
  · rename_i b _
    exact onBlockWith_inv c p CarriedAdmission.AlsoCarried hc h b

theorem namedGoldfishVoteWith_inv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : StoreInv e cfg st) :
    StoreInv e cfg (namedGoldfishVoteWith c cache e hc nd st).1 := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show StoreInv e cfg { st with core := core }
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  refine h.congr rfl ?_
  rw [h1]
  exact goldfishVoteWith_same c cache e hc nd st.core

theorem namedUpdateConfirmationWith_inv {e : ProtocolEnv} {cfg : HeightConfig}
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : NamedStore} (h : StoreInv e cfg st) (k : Nat) :
    StoreInv e cfg (namedUpdateConfirmationWith cache e hc st k) :=
  h.congr rfl (updateConfirmationWith_same cache e hc st.core k)

theorem attestWith_inv {e : ProtocolEnv} {cfg : HeightConfig} (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : StoreInv e cfg st) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    StoreInv e cfg (attestWith cache e hc nd st rec).1 := by
  unfold attestWith
  split
  exact admitRow_inv hc h _

/-- 1 tick の務め `tick` は不変条件を保つ(時計合わせは `congr`、提案は `proposeBlockWith_inv`、投票・確認・attestation は各補題。
`split_ifs` が 4 つの `if` で 16 の経路を割る)。 -/
theorem tick_inv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : StoreInv e cfg st) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    StoreInv e cfg (tick c p a nr cache e hc cfg nd st rec t).1 := by
  have h0 : StoreInv e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    h.congr rfl ⟨rfl, rfl, rfl⟩
  unfold tick
  dsimp only
  split_ifs
  -- 16 の経路を `with_reducible exact` で閉じる(失敗する候補が生成 Model の定義を展開して heartbeat を使い切らないよう、
  -- 候補の照合は reducible な展開だけで行う。各経路の項は補題の型と構文的に一致する)
  all_goals first
    | with_reducible exact attestWith_inv cache hc nd (namedUpdateConfirmationWith_inv cache hc (namedGoldfishVoteWith_inv c cache hc nd (proposeBlockWith_inv c p nr cache hc nd h0)) _) _
    | with_reducible exact attestWith_inv cache hc nd (namedUpdateConfirmationWith_inv cache hc (namedGoldfishVoteWith_inv c cache hc nd h0) _) _
    | with_reducible exact attestWith_inv cache hc nd (namedUpdateConfirmationWith_inv cache hc (proposeBlockWith_inv c p nr cache hc nd h0) _) _
    | with_reducible exact attestWith_inv cache hc nd (namedUpdateConfirmationWith_inv cache hc h0 _) _
    | with_reducible exact attestWith_inv cache hc nd (namedGoldfishVoteWith_inv c cache hc nd (proposeBlockWith_inv c p nr cache hc nd h0)) _
    | with_reducible exact attestWith_inv cache hc nd (namedGoldfishVoteWith_inv c cache hc nd h0) _
    | with_reducible exact attestWith_inv cache hc nd (proposeBlockWith_inv c p nr cache hc nd h0) _
    | with_reducible exact attestWith_inv cache hc nd h0 _
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc (namedGoldfishVoteWith_inv c cache hc nd (proposeBlockWith_inv c p nr cache hc nd h0)) _
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc (namedGoldfishVoteWith_inv c cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc (proposeBlockWith_inv c p nr cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc h0 _
    | with_reducible exact namedGoldfishVoteWith_inv c cache hc nd (proposeBlockWith_inv c p nr cache hc nd h0)
    | with_reducible exact namedGoldfishVoteWith_inv c cache hc nd h0
    | with_reducible exact proposeBlockWith_inv c p nr cache hc nd h0
    | with_reducible exact h0

theorem nodeTick_inv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    {n : NamedNodeState} (h : StoreInv s.e s.cfg n.st) (t : Int) :
    StoreInv s.e s.cfg (nodeTick c p a nr s v n t).1.st := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_inv c p a nr _ s.hc _ h n.signing t

/-! ## world -/

/-- world のどのノードの store も不変条件を満たす。 -/
def WorldInv (e : ProtocolEnv) (cfg : HeightConfig) (w : NamedWorld) : Prop :=
  ∀ v, StoreInv e cfg (worldAt w v).st

theorem worldInit_inv (e : ProtocolEnv) (cfg : HeightConfig) : WorldInv e cfg worldInit := fun _ =>
  initial_inv e cfg

theorem worldStep_inv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) {w : NamedWorld}
    (h : WorldInv s.e s.cfg w) (ev : NamedEvent) : WorldInv s.e s.cfg (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_inv c p a nr s u (h u) t
    · rw [hw]
      exact h v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_inv c p s (h u) o
    · rw [hw]
      exact h v

theorem foldl_worldStep_inv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, WorldInv s.e s.cfg w →
      WorldInv s.e s.cfg (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, h => h
  | ev :: l, _, h => by
    rw [List.foldl_cons]
    exact foldl_worldStep_inv c p a nr s l (worldStep_inv c p a nr s h ev)

/-- 時刻 `t` の読み `readAt` の world は不変条件を満たす。 -/
theorem readAt_inv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t : Int) :
    WorldInv s.e s.cfg (readAt c p a nr s rho t) := by
  unfold readAt
  exact foldl_worldStep_inv c p a nr s _ (worldInit_inv s.e s.cfg)

/-- 添字 `i` の前の world `stateBefore` も不変条件を満たす。 -/
theorem stateBefore_inv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (i : Nat) :
    WorldInv s.e s.cfg (stateBefore c p a nr s rho i) := by
  unfold stateBefore
  exact foldl_worldStep_inv c p a nr s _ (worldInit_inv s.e s.cfg)

end Proofs.Consensus.Carrier
