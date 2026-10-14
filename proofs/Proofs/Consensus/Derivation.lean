import Model.Consensus.Protocol.ChainState
import Proofs.Consensus.Blocks
import Proofs.Consensus.NamedBlocks
import Proofs.Consensus.Sets
import Mathlib.Tactic

/-!
# 名前付き導出 `deriveNamed` の不変条件(C71 の補題)

生成 Model の `deriveNamed e cfg B`(`Protocol/ChainState.lean`: genesis は `initialChainState`、子は親の状態に
`namedTransition` = `processHeightEvents (foldRows st (eraseBlock B) rows)` を当てる)の chain 状態 `st` について、
`B` の祖先の行で裏付けられた不変条件 `Inv e B st` を帰納法で示す:
- 高さの順序 `hF ≤ hJ < h`、`f` / `j` / `tH` が `eraseBlock B` の接頭辞、`hF = 0 → f = Genesis`;
- 3 つの署名者集合(`finalize` / `targetParticipation` / `progress`)が `Sorted` で、各署名者に `B` の chain 上の行
  (`OnChain B row`)があり、`finalize` の行は `finalityPair = some ⟨hJ, root j⟩`、`targetParticipation` / `progress` の行は
  `matchesEntry heightPair h (root tH)`;
- finality の証明書 `cert`: `hF ≠ 0` なら、重み `q` 以上の署名者集合の各署名者が `finalityPair = some ⟨hF, root f⟩` の行を持つ;
- 高さの横断 `crossing`: `1 ≤ h₀ < h` なら、`eraseBlock B` の祖先 `X` と、重み `q` 以上の署名者集合の各署名者が
  `matchesEntry heightPair h₀ (root X)` の行を持つ(高さ `h₀` を通過したときの定足数)。
手書き `NamedFinalityCertificates`(`finalized_zero_is_genesis` / `finality_certificate` / `height_crossing`)、
`NamedMatchingProgress` / `NamedEntryHeight`、`NamedDerivationGeometry.chainOrder_derive_named` / `derive_named_anchors_preceq`
(`DecoupledConsensusProofs/Protocol/ChainState/`)に当たる。手書きは不変条件を別々の補題に分けるが、
ここでは 1 つの構造体 `Inv` にまとめて 1 回の帰納法で示す。
-/

namespace Proofs.Consensus.Derivation

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Weights Model.Consensus.Protocol.ChainState
open Proofs.Consensus.Blocks Proofs.Consensus.NamedBlocks Proofs.Consensus.Sets

/-- 行 `row` が `B` かその名前付き祖先のどれかに載っている。手書き `OnNamedChain`。 -/
def OnChain (B : NamedBlock) (row : NamedAttestation) : Prop :=
  ∃ c : NamedBlock, namedPreceq c B = true ∧ row ∈ namedAttestations c

theorem OnChain.node {B : NamedBlock} {row : NamedAttestation} (h : OnChain B row) (s : Nat) (r : BlockId)
    (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId) :
    OnChain (NamedBlock.Node B s r v sup rows i) row := by
  obtain ⟨c, hc, hrow⟩ := h
  exact ⟨c, namedPreceq_node hc s r v sup rows i, hrow⟩

theorem OnChain.self {B : NamedBlock} {row : NamedAttestation} (h : row ∈ namedAttestations B) : OnChain B row :=
  ⟨B, namedPreceq_self B, h⟩

/-- 署名者の集合 `Q` の各署名者に、`B` の chain 上の行で性質 `P` を満たすものがある。 -/
def Rows (B : NamedBlock) (Q : VSet) (P : NamedAttestation → Prop) : Prop :=
  ∀ i ∈ Q.elems, ∃ row : NamedAttestation, OnChain B row ∧ row.valIndex = i ∧ P row

theorem Rows.node {B : NamedBlock} {Q : VSet} {P : NamedAttestation → Prop} (h : Rows B Q P) (s : Nat)
    (r : BlockId) (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId) :
    Rows (NamedBlock.Node B s r v sup rows i) Q P := by
  intro j hj
  obtain ⟨row, hrow, hv, hp⟩ := h j hj
  exact ⟨row, hrow.node s r v sup rows i, hv, hp⟩

theorem Rows.empty (B : NamedBlock) (P : NamedAttestation → Prop) : Rows B NaruStd.Set.empty P := by
  intro i hi
  simp [NaruStd.Set.empty] at hi

theorem Rows.insert {B : NamedBlock} {Q : VSet} {P : NamedAttestation → Prop} (h : Rows B Q P)
    {row : NamedAttestation} (hrow : OnChain B row) (hp : P row) : Rows B (Q.insert row.valIndex) P := by
  intro i hi
  rw [mem_insert_iff vid_eq] at hi
  rcases hi with rfl | hi
  · exact ⟨row, hrow, rfl, hp⟩
  · exact h i hi

/-- 定足数(重み `q` 以上)の署名者集合で、各署名者に性質 `P` の行がある。 -/
def Quorum (e : ProtocolEnv) (B : NamedBlock) (P : NamedAttestation → Prop) : Prop :=
  ∃ Q : VSet, Sorted Q ∧ quorumCheck e.electorate Q = true ∧ Rows B Q P

theorem Quorum.node {e : ProtocolEnv} {B : NamedBlock} {P : NamedAttestation → Prop} (h : Quorum e B P)
    (s : Nat) (r : BlockId) (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId) :
    Quorum e (NamedBlock.Node B s r v sup rows i) P := by
  obtain ⟨Q, hs, hq, hr⟩ := h
  exact ⟨Q, hs, hq, hr.node s r v sup rows i⟩

/-- `deriveNamed` の不変条件。 -/
structure Inv (e : ProtocolEnv) (B : NamedBlock) (st : ChainState) : Prop where
  hF_le_hJ : st.hF ≤ st.hJ
  hJ_lt_h : st.hJ < st.h
  f_preceq : preceq st.f (eraseBlock B) = true
  j_preceq : preceq st.j (eraseBlock B) = true
  tH_preceq : preceq st.tH (eraseBlock B) = true
  hF_zero : st.hF = 0 → st.f = Block.Genesis
  fin_sorted : Sorted st.finalize
  tp_sorted : Sorted st.targetParticipation
  pr_sorted : Sorted st.progress
  fin_rows : Rows B st.finalize (fun row => row.finalityPair = some ⟨st.hJ, root st.j⟩)
  tp_rows : Rows B st.targetParticipation (fun row => matchesEntry row.heightPair st.h (root st.tH) = true)
  pr_rows : Rows B st.progress (fun row => matchesEntry row.heightPair st.h (root st.tH) = true)
  cert : st.hF ≠ 0 → Quorum e B (fun row => row.finalityPair = some ⟨st.hF, root st.f⟩)
  crossing : ∀ h : Nat, 1 ≤ h → h < st.h → ∃ X : Block, preceq X (eraseBlock B) = true ∧
    Quorum e B (fun row => matchesEntry row.heightPair h (root X) = true)

/-! ## 持ち上げと合同 -/

/-- 親についての不変条件は、状態を変えずに子についての不変条件になる。 -/
theorem Inv.node {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st) (s : Nat) (r : BlockId)
    (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId) :
    Inv e (NamedBlock.Node B s r v sup rows i) st where
  hF_le_hJ := h.hF_le_hJ
  hJ_lt_h := h.hJ_lt_h
  f_preceq := preceq_trans h.f_preceq (eraseBlock_node_preceq B s r v sup rows i)
  j_preceq := preceq_trans h.j_preceq (eraseBlock_node_preceq B s r v sup rows i)
  tH_preceq := preceq_trans h.tH_preceq (eraseBlock_node_preceq B s r v sup rows i)
  hF_zero := h.hF_zero
  fin_sorted := h.fin_sorted
  tp_sorted := h.tp_sorted
  pr_sorted := h.pr_sorted
  fin_rows := h.fin_rows.node s r v sup rows i
  tp_rows := h.tp_rows.node s r v sup rows i
  pr_rows := h.pr_rows.node s r v sup rows i
  cert := fun hz => (h.cert hz).node s r v sup rows i
  crossing := fun h0 h1 h2 => by
    obtain ⟨X, hX, hQ⟩ := h.crossing h0 h1 h2
    exact ⟨X, preceq_trans hX (eraseBlock_node_preceq B s r v sup rows i), hQ.node s r v sup rows i⟩

/-- 不変条件に関わる欄が等しい状態へ移す。 -/
theorem Inv.congr {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st) {st' : ChainState}
    (hh : st'.h = st.h) (htH : st'.tH = st.tH) (hj : st'.j = st.j) (hhJ : st'.hJ = st.hJ)
    (hf : st'.f = st.f) (hhF : st'.hF = st.hF) (hfin : st'.finalize = st.finalize)
    (htp : st'.targetParticipation = st.targetParticipation) (hpr : st'.progress = st.progress) :
    Inv e B st' where
  hF_le_hJ := by rw [hhF, hhJ]; exact h.hF_le_hJ
  hJ_lt_h := by rw [hhJ, hh]; exact h.hJ_lt_h
  f_preceq := by rw [hf]; exact h.f_preceq
  j_preceq := by rw [hj]; exact h.j_preceq
  tH_preceq := by rw [htH]; exact h.tH_preceq
  hF_zero := by rw [hhF, hf]; exact h.hF_zero
  fin_sorted := by rw [hfin]; exact h.fin_sorted
  tp_sorted := by rw [htp]; exact h.tp_sorted
  pr_sorted := by rw [hpr]; exact h.pr_sorted
  fin_rows := by rw [hfin, hhJ, hj]; exact h.fin_rows
  tp_rows := by rw [htp, hh, htH]; exact h.tp_rows
  pr_rows := by rw [hpr, hh, htH]; exact h.pr_rows
  cert := by rw [hhF, hf]; exact h.cert
  crossing := by rw [hh]; exact h.crossing

/-! ## 初期状態 -/

theorem inv_initial (e : ProtocolEnv) : Inv e NamedBlock.Genesis initialChainState where
  hF_le_hJ := Nat.le_refl 0
  hJ_lt_h := Nat.zero_lt_one
  f_preceq := preceq_self _
  j_preceq := preceq_self _
  tH_preceq := preceq_self _
  hF_zero := fun _ => rfl
  fin_sorted := Sorted.empty
  tp_sorted := Sorted.empty
  pr_sorted := Sorted.empty
  fin_rows := Rows.empty _ _
  tp_rows := Rows.empty _ _
  pr_rows := Rows.empty _ _
  cert := fun hz => absurd rfl hz
  crossing := fun h0 h1 h2 => by
    have h2' : h0 < 1 := h2
    omega

/-! ## `processAttestation` -/

theorem pa_fields (st : ChainState) (a : CombinedAttestation) :
    (processAttestation st a).h = st.h ∧ (processAttestation st a).tH = st.tH ∧
    (processAttestation st a).j = st.j ∧ (processAttestation st a).hJ = st.hJ ∧
    (processAttestation st a).f = st.f ∧ (processAttestation st a).hF = st.hF := by
  unfold processAttestation
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pa_finalize (st : ChainState) (a : CombinedAttestation) :
    (processAttestation st a).finalize = st.finalize ∨
    (st.hF < st.hJ ∧ a.finalityPair = some ⟨st.hJ, root st.j⟩ ∧
      (processAttestation st a).finalize = st.finalize.insert a.valIndex) := by
  unfold processAttestation
  dsimp only
  split_ifs with h1 h2 h3 <;> simp_all

theorem pa_tp (st : ChainState) (a : CombinedAttestation) :
    (processAttestation st a).targetParticipation = st.targetParticipation ∨
    (a.heightPair = HeightPair.Target st.h (root st.tH) ∧
      (processAttestation st a).targetParticipation = st.targetParticipation.insert a.valIndex) := by
  unfold processAttestation
  dsimp only
  split_ifs with h1 h2 h3 <;> simp_all

theorem pa_pr (st : ChainState) (a : CombinedAttestation) :
    (processAttestation st a).progress = st.progress ∨
    ((a.heightPair = HeightPair.Target st.h (root st.tH) ∨ a.heightPair = HeightPair.Timeout st.h) ∧
      (processAttestation st a).progress = st.progress.insert a.valIndex) := by
  unfold processAttestation
  dsimp only
  split_ifs with h1 h2 h3 <;> simp_all

theorem matchesEntry_of_targetedView_target {st : ChainState} {row : NamedAttestation}
    (h : (targetedView st row).heightPair = HeightPair.Target st.h (root st.tH)) :
    matchesEntry row.heightPair st.h (root st.tH) = true := by
  change targetedHeightPair st row = _ at h
  unfold targetedHeightPair at h
  split_ifs at h with hm
  exact hm

theorem matchesEntry_of_targetedView_timeout {st : ChainState} {row : NamedAttestation}
    (h : (targetedView st row).heightPair = HeightPair.Timeout st.h) :
    matchesEntry row.heightPair st.h (root st.tH) = true := by
  change targetedHeightPair st row = _ at h
  unfold targetedHeightPair at h
  split_ifs at h with hm
  exact hm

/-- `B` の chain 上の行を 1 つ処理しても不変条件は保たれる。 -/
theorem Inv.attest {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st)
    {row : NamedAttestation} (hrow : OnChain B row) : Inv e B (processAttestationWith st row) := by
  unfold processAttestationWith
  obtain ⟨hh, htH, hj, hhJ, hf, hhF⟩ := pa_fields st (targetedView st row)
  have hfin := pa_finalize st (targetedView st row)
  have htp := pa_tp st (targetedView st row)
  have hpr := pa_pr st (targetedView st row)
  exact {
    hF_le_hJ := by rw [hhF, hhJ]; exact h.hF_le_hJ
    hJ_lt_h := by rw [hhJ, hh]; exact h.hJ_lt_h
    f_preceq := by rw [hf]; exact h.f_preceq
    j_preceq := by rw [hj]; exact h.j_preceq
    tH_preceq := by rw [htH]; exact h.tH_preceq
    hF_zero := by rw [hhF, hf]; exact h.hF_zero
    fin_sorted := by
      rcases hfin with hfin | ⟨_, _, hfin⟩ <;> rw [hfin]
      · exact h.fin_sorted
      · exact h.fin_sorted.insert _
    tp_sorted := by
      rcases htp with htp | ⟨_, htp⟩ <;> rw [htp]
      · exact h.tp_sorted
      · exact h.tp_sorted.insert _
    pr_sorted := by
      rcases hpr with hpr | ⟨_, hpr⟩ <;> rw [hpr]
      · exact h.pr_sorted
      · exact h.pr_sorted.insert _
    fin_rows := by
      rw [hhJ, hj]
      rcases hfin with hfin | ⟨_, hpair, hfin⟩ <;> rw [hfin]
      · exact h.fin_rows
      · exact h.fin_rows.insert hrow hpair
    tp_rows := by
      rw [hh, htH]
      rcases htp with htp | ⟨hpair, htp⟩ <;> rw [htp]
      · exact h.tp_rows
      · exact h.tp_rows.insert hrow (matchesEntry_of_targetedView_target hpair)
    pr_rows := by
      rw [hh, htH]
      rcases hpr with hpr | ⟨hpair, hpr⟩ <;> rw [hpr]
      · exact h.pr_rows
      · refine h.pr_rows.insert hrow ?_
        rcases hpair with hpair | hpair
        · exact matchesEntry_of_targetedView_target hpair
        · exact matchesEntry_of_targetedView_timeout hpair
    cert := by rw [hhF, hf]; exact h.cert
    crossing := by rw [hh]; exact h.crossing }

/-- `B` の chain 上の行の列を畳み込んでも不変条件は保たれる。 -/
theorem Inv.foldAttest {e : ProtocolEnv} {B : NamedBlock} : ∀ (rows : List NamedAttestation) {st : ChainState},
    Inv e B st → (∀ row ∈ rows, OnChain B row) → Inv e B (rows.foldl processAttestationWith st)
  | [], _, h, _ => h
  | row :: rows, st, h, hrows => by
    rw [List.foldl_cons]
    exact Inv.foldAttest rows (h.attest (hrows row (List.mem_cons_self ..)))
      (fun r hr => hrows r (List.mem_cons_of_mem _ hr))

/-- `foldRows` は不変条件を保つ(`s` と `l` の更新は不変条件に関わらない)。 -/
theorem Inv.fold {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st) (geom : Block)
    (rows : List NamedAttestation) (hrows : ∀ row ∈ rows, OnChain B row) :
    Inv e B (foldRows st geom rows) := by
  unfold foldRows
  dsimp only
  have h1 : Inv e B { st with s := slot geom } := h.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h2 := Inv.foldAttest rows h1 hrows
  exact h2.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem foldRows_l (st : ChainState) (geom : Block) (rows : List NamedAttestation) :
    (foldRows st geom rows).l = geom := rfl

/-! ## `processHeightEvents` -/

theorem finalityReady_iff {e : ProtocolEnv} {st : ChainState} :
    finalityReady e st = true ↔ st.hF < st.hJ ∧ quorumCheck e.electorate st.finalize = true := by
  unfold finalityReady finalityQuorum qFinality
  rw [Bool.and_eq_true, decide_eq_true_iff]

theorem targetReady_quorum {e : ProtocolEnv} {st : ChainState} (h : targetReady e st = true) :
    quorumCheck e.electorate st.targetParticipation = true := by
  unfold targetReady targetQuorum qTarget at h
  exact (Bool.and_eq_true _ _ |>.mp h).2

theorem progReady_quorum {e : ProtocolEnv} {cfg : HeightConfig} {st : ChainState} (h : progReady e cfg st = true) :
    quorumCheck e.electorate st.targetParticipation = true ∨ quorumCheck e.electorate st.progress = true := by
  unfold progReady targetQuorum progQuorum qTarget qProg at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Bool.and_eq_true _ _ |>.mp h).2

theorem processHeightEvents_l (e : ProtocolEnv) (cfg : HeightConfig) (st : ChainState) :
    (processHeightEvents e cfg st).l = st.l := by
  unfold processHeightEvents
  dsimp only
  split_ifs <;> rfl

/-- finality が成立したとき(`hF < hJ` と `finalize` の定足数)、`f := j`、`hF := hJ` にしても不変条件は保たれ、
証明書は `finalize` の行から作れる。 -/
theorem Inv.finalizeStep {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st) (hlt : st.hF < st.hJ)
    (hq : quorumCheck e.electorate st.finalize = true) : Inv e B { st with f := st.j, hF := st.hJ } where
  hF_le_hJ := Nat.le_refl _
  hJ_lt_h := h.hJ_lt_h
  f_preceq := h.j_preceq
  j_preceq := h.j_preceq
  tH_preceq := h.tH_preceq
  hF_zero := fun hz => by
    have hz' : st.hJ = 0 := hz
    omega
  fin_sorted := h.fin_sorted
  tp_sorted := h.tp_sorted
  pr_sorted := h.pr_sorted
  fin_rows := h.fin_rows
  tp_rows := h.tp_rows
  pr_rows := h.pr_rows
  cert := fun _ => ⟨st.finalize, h.fin_sorted, hq, h.fin_rows⟩
  crossing := h.crossing

/-- target の定足数で高さを進める(`finalize := empty`、`j := tH`、`hJ := h` の後の `advanceHeight`)。
高さ `h` の横断の定足数は `targetParticipation`。 -/
theorem Inv.advanceTarget {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st)
    (hl : preceq st.l (eraseBlock B) = true) (hq : quorumCheck e.electorate st.targetParticipation = true)
    (cfg : HeightConfig) :
    Inv e B (advanceHeight cfg { st with finalize := NaruStd.Set.empty, j := st.tH, hJ := st.h }) := by
  unfold advanceHeight
  dsimp only
  exact {
    hF_le_hJ := Nat.le_trans h.hF_le_hJ (Nat.le_of_lt h.hJ_lt_h)
    hJ_lt_h := Nat.lt_succ_self _
    f_preceq := h.f_preceq
    j_preceq := h.tH_preceq
    tH_preceq := hl
    hF_zero := h.hF_zero
    fin_sorted := Sorted.empty
    tp_sorted := Sorted.empty
    pr_sorted := Sorted.empty
    fin_rows := Rows.empty _ _
    tp_rows := Rows.empty _ _
    pr_rows := Rows.empty _ _
    cert := h.cert
    crossing := fun h0 h1 h2 => by
      have h2' : h0 < st.h + 1 := h2
      rcases Nat.lt_or_ge h0 st.h with hlt | hge
      · exact h.crossing h0 h1 hlt
      · have heq : h0 = st.h := by omega
        subst heq
        exact ⟨st.tH, h.tH_preceq, st.targetParticipation, h.tp_sorted, hq, h.tp_rows⟩ }

/-- progress の定足数(target か timeout)で高さを進める(`advanceHeight` だけ)。 -/
theorem Inv.advanceProg {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st)
    (hl : preceq st.l (eraseBlock B) = true)
    (hq : quorumCheck e.electorate st.targetParticipation = true ∨ quorumCheck e.electorate st.progress = true)
    (cfg : HeightConfig) : Inv e B (advanceHeight cfg st) := by
  unfold advanceHeight
  dsimp only
  exact {
    hF_le_hJ := h.hF_le_hJ
    hJ_lt_h := Nat.lt_trans h.hJ_lt_h (Nat.lt_succ_self _)
    f_preceq := h.f_preceq
    j_preceq := h.j_preceq
    tH_preceq := hl
    hF_zero := h.hF_zero
    fin_sorted := h.fin_sorted
    tp_sorted := Sorted.empty
    pr_sorted := Sorted.empty
    fin_rows := h.fin_rows
    tp_rows := Rows.empty _ _
    pr_rows := Rows.empty _ _
    cert := h.cert
    crossing := fun h0 h1 h2 => by
      have h2' : h0 < st.h + 1 := h2
      rcases Nat.lt_or_ge h0 st.h with hlt | hge
      · exact h.crossing h0 h1 hlt
      · have heq : h0 = st.h := by omega
        subst heq
        rcases hq with hq | hq
        · exact ⟨st.tH, h.tH_preceq, st.targetParticipation, h.tp_sorted, hq, h.tp_rows⟩
        · exact ⟨st.tH, h.tH_preceq, st.progress, h.pr_sorted, hq, h.pr_rows⟩ }

/-- `processHeightEvents` は不変条件を保つ(`l` が `eraseBlock B` の接頭辞なら)。 -/
theorem Inv.heightEvents {e : ProtocolEnv} {B : NamedBlock} {st : ChainState} (h : Inv e B st)
    (hl : preceq st.l (eraseBlock B) = true) (cfg : HeightConfig) :
    Inv e B (processHeightEvents e cfg st) := by
  unfold processHeightEvents
  dsimp only
  split_ifs with hfin htgt hprog htgt' hprog'
  · obtain ⟨hlt, hq⟩ := finalityReady_iff.mp hfin
    exact (h.finalizeStep hlt hq).advanceTarget hl (targetReady_quorum htgt) cfg
  · obtain ⟨hlt, hq⟩ := finalityReady_iff.mp hfin
    exact (h.finalizeStep hlt hq).advanceProg hl (progReady_quorum hprog) cfg
  · obtain ⟨hlt, hq⟩ := finalityReady_iff.mp hfin
    exact h.finalizeStep hlt hq
  · exact h.advanceTarget hl (targetReady_quorum htgt') cfg
  · exact h.advanceProg hl (progReady_quorum hprog') cfg
  · exact h

/-! ## `deriveNamed` -/

theorem deriveNamed_l (e : ProtocolEnv) (cfg : HeightConfig) : ∀ B : NamedBlock, (deriveNamed e cfg B).l = eraseBlock B
  | NamedBlock.Genesis => rfl
  | NamedBlock.Node p s r v sup rows i => by
    simp only [deriveNamed]
    unfold namedTransition transitionRows
    rw [processHeightEvents_l, foldRows_l]

/-- 名前付き導出の不変条件(`B` の構造帰納法)。 -/
theorem deriveNamed_inv (e : ProtocolEnv) (cfg : HeightConfig) : ∀ B : NamedBlock, Inv e B (deriveNamed e cfg B)
  | NamedBlock.Genesis => inv_initial e
  | NamedBlock.Node p s r v sup rows i => by
    have ih := deriveNamed_inv e cfg p
    simp only [deriveNamed]
    unfold namedTransition transitionRows
    have h1 : Inv e (NamedBlock.Node p s r v sup rows i) (deriveNamed e cfg p) := ih.node s r v sup rows i
    have h2 := h1.fold (eraseBlock (NamedBlock.Node p s r v sup rows i))
      (namedAttestations (NamedBlock.Node p s r v sup rows i)) (fun _ hrow => OnChain.self hrow)
    exact h2.heightEvents (by rw [foldRows_l]; exact preceq_self _) cfg

end Proofs.Consensus.Derivation
