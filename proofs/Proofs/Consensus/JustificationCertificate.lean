import Proofs.Consensus.FinalizedSource
import Proofs.Consensus.ReceiverFinality
import Proofs.Consensus.Weights
import Mathlib.Tactic

/-!
# justification の証明書と honest な署名者(C71 の補題)

`FinalizedSource.fgRoot_justified` は FG root を bodies のどれかの `D` の導出の `j` として返す。ここではその `j` の
justification の証明書を取り出し、faulty の重みが総重みの 1/3 未満なら、証明書の定足数に honest な署名者がいて、その行が
`D` の chain に載っていることを示す。手書き `NamedJustificationCertificates.justified_zero_is_genesis` /
`justification_certificate` と、`HealingSurface.processedJustification_confirmationWitness`(`Protocol/ChainState/FGRootWitness.lean`)の
前半(定足数の honest な署名者を取り、その行を運んだブロックを処理した event から署名者の発行を取るところまで)に当たる。
違いは 3 つ:
- 手書きの証明書は行の flag を `false`(`.vote h J.root false`)に固定するが、ここの行は `matchesEntry heightPair hJ (root j)`
  (flag を見ない。`Derivation.Inv.tp_rows` と同じ)。
- 手書きは honest な署名者を `HonestWeightMajority`(faulty の重み < honest の重み)から取る。ここでは前提を
  「どの定足数にも `H` の署名者がいる」`QuorumHonest` にして、`BelowOneThird` から出す版を系にする
  (`quorumHonest_of_belowOneThird`。`HonestWeightMajority` に当たる重みの形から出す版は残り)。
- 手書きの発行の時刻 `ta < time` は、処理の event の添字を `bodies_processed_before` で追い、添字 `idxLt time` より前の event の
  時刻は `time` より前(`time_lt_of_lt_idxLt`)なので、処理の時刻 `t < time` と発行の時刻 `t2 ≤ t` から出す
  (`stateBeforeTime_fgRoot_honestEmission_lt`。周回 161 で足した)。

- **証明書**: `Derivation.Inv` の欄 `hJ_zero` / `jcert`(周回 160 で足した)。`(j, hJ)` を書くのは `processHeightEvents` の
  target の分岐の `j := tH`、`hJ := h` だけで、そのとき `targetParticipation` が定足数で、各署名者に `matchesEntry heightPair h
  (root tH)` の行がある。`hJ = 0` は初期状態のままなので `j = Genesis`。
- **honest な署名者**: 定足数は重み `⌊(2W + 2) / 3⌋` 以上。署名者がどれも `H` に無ければ、重みが 0 でない署名者は
  `validators \ H`(= `faulty`)にあるので、定足数の重みは faulty の重み以下で、`3 · faulty < W`(`BelowOneThird`)と矛盾する
  (`exists_honest_of_quorum` / `quorumHonest_of_belowOneThird`)。
- **store と run**: bodies は祖先について閉じるので、行を運ぶブロックも bodies にある(`fgRoot_honestRow`)。run の読みでは、
  そのブロックは読みの主がある時刻に処理した(`Processes`)ブロックで(`Attribution.bodies_processed`)、
  `UnforgeableSignatures` の carried の半分(`Attribution.attributed` の `hcar` と同じ形)から、honest な署名者が実際に出した行(`Emits`)になる
  (`stateBefore_fgRoot_honestEmission` / `stateBeforeTime_fgRoot_honestEmission`。処理と発行の時刻が読みの時刻より前な版は
  `stateBeforeTime_fgRoot_honestEmission_lt`)。
-/

namespace Proofs.Consensus.JustificationCertificate

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Weights Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.NamedBlocks Proofs.Consensus.Sets Proofs.Consensus.Weights Proofs.Consensus.Derivation
open Proofs.Consensus.Carrier Proofs.Consensus.JustifiedCarrier Proofs.Consensus.FinalizedSource

/-! ## 証明書 -/

/-- 導出の `hJ = 0` なら `j = Genesis`。手書き `justified_zero_is_genesis`。 -/
theorem justified_zero_is_genesis (e : ProtocolEnv) (cfg : HeightConfig) (C : NamedBlock)
    (hz : (deriveNamed e cfg C).hJ = 0) : (deriveNamed e cfg C).j = Block.Genesis :=
  (deriveNamed_inv e cfg C).hJ_zero hz

/-- 導出の `hJ ≠ 0` なら、重み `q` 以上の署名者集合の各署名者に、`C` の chain 上の行で `matchesEntry heightPair hJ (root j)` の
ものがある。手書き `justification_certificate`(手書きは flag を `false` に固定する)。 -/
theorem justification_certificate (e : ProtocolEnv) (cfg : HeightConfig) (C : NamedBlock)
    (hz : (deriveNamed e cfg C).hJ ≠ 0) :
    Quorum e C (fun row => matchesEntry row.heightPair (deriveNamed e cfg C).hJ (root (deriveNamed e cfg C).j) = true) :=
  (deriveNamed_inv e cfg C).jcert hz

/-! ## 定足数の honest な署名者 -/

/-- 署名者がどれも `H` に無い集合の重みは、`validators \ H` の重み以下。 -/
theorem weightOf_le_diff {e : Electorate} (hv : Sorted (validators e)) {Q H : VSet} (hQ : Sorted Q)
    (hno : ∀ i ∈ Q.elems, i ∉ H.elems) : weightOf e Q ≤ weightOf e ((validators e).diff H) := by
  have hd : Sorted ((validators e).diff H) := hv.filter _
  rw [weightOf_eq hQ, weightOf_eq hd]
  apply Finset.sum_le_sum_of_ne_zero
  intro v hvQ hne
  rw [List.mem_toFinset] at hvQ ⊢
  show v ∈ (validators e).elems.filter (fun x => !H.contains x)
  rw [List.mem_filter]
  refine ⟨mem_validators_of_weight_ne_zero e v hne, ?_⟩
  have hc : H.contains v = false := by
    cases hc : H.contains v
    · rfl
    · exact absurd ((contains_iff_mem vid_eq H v).mp hc) (hno v hvQ)
  simp [hc]

/-- 定足数(重み `⌊(2W + 2) / 3⌋` 以上)には、`validators \ H` の重み `w` が `3 · w < W` なら `H` の署名者がいる。
手書き `HonestWeightMajority.exists_honest_member_of_quorum` に当たる(手書きの前提は faulty の重み < honest の重み)。 -/
theorem exists_honest_of_quorum {e : Electorate} (hv : Sorted (validators e)) {Q H : VSet} (hQ : Sorted Q)
    (hq : quorumCheck e Q = true) (hb : 3 * weightOf e ((validators e).diff H) < totalWeight e) :
    ∃ i ∈ Q.elems, i ∈ H.elems := by
  by_contra hno
  have hle := weightOf_le_diff hv hQ (fun i hi hH => hno ⟨i, hi, hH⟩)
  unfold quorumCheck finalityThreshold at hq
  rw [decide_eq_true_iff] at hq
  omega

/-- `BelowOneThird s H` は `exists_honest_of_quorum` の重みの前提。 -/
theorem belowOneThird_weight {s : Model.Consensus.Execution.Setup.Setup} {H : VSet} (hb : BelowOneThird s H) :
    3 * weightOf s.e.electorate ((validators s.e.electorate).diff H) < totalWeight s.e.electorate := by
  unfold BelowOneThird Model.Consensus.Spec.Conditions.faulty at hb
  exact hb

/-- どの定足数にも `H` の署名者がいる。store と run の版の前提。 -/
def QuorumHonest (e : ProtocolEnv) (H : VSet) : Prop :=
  ∀ Q : VSet, Sorted Q → quorumCheck e.electorate Q = true → ∃ i ∈ Q.elems, i ∈ H.elems

/-- `validators` が整列していて `BelowOneThird s H` なら `QuorumHonest s.e H`。 -/
theorem quorumHonest_of_belowOneThird {s : Model.Consensus.Execution.Setup.Setup} {H : VSet}
    (hv : Sorted (validators s.e.electorate)) (hb : BelowOneThird s H) : QuorumHonest s.e H :=
  fun _ hQ hq => exists_honest_of_quorum hv hQ hq (belowOneThird_weight hb)

/-- `SetupWellFormed` の下で `validators` は整列している。 -/
theorem sorted_validators {committee' : Nat → NaruStd.Set ValidatorId} {proposer' : Nat → ValidatorId}
    {s : Model.Consensus.Execution.Setup.Setup} (hwf : SetupWellFormed committee' proposer' s) :
    Sorted (validators s.e.electorate) := by
  unfold SetupWellFormed at hwf
  obtain ⟨⟨⟨_, hnorm⟩, _⟩, _⟩ := hwf
  exact sorted_of_normalized hnorm

/-- 導出の `j` は genesis(`hJ = 0`)か、`C` の名前付き祖先 `X` の行で、`H` の署名者の `matchesEntry heightPair hJ (root j)` の
ものがある。 -/
theorem justification_honestRow (e : ProtocolEnv) (cfg : HeightConfig) {H : VSet} (hqh : QuorumHonest e H)
    (C : NamedBlock) :
    ((deriveNamed e cfg C).hJ = 0 ∧ (deriveNamed e cfg C).j = Block.Genesis) ∨
      ∃ X row, namedPreceq X C = true ∧ row ∈ namedAttestations X ∧ row.valIndex ∈ H.elems ∧
        matchesEntry row.heightPair (deriveNamed e cfg C).hJ (root (deriveNamed e cfg C).j) = true := by
  by_cases hz : (deriveNamed e cfg C).hJ = 0
  · exact Or.inl ⟨hz, justified_zero_is_genesis e cfg C hz⟩
  · obtain ⟨Q, hQs, hQq, hrows⟩ := justification_certificate e cfg C hz
    obtain ⟨i, hiQ, hiH⟩ := hqh Q hQs hQq
    obtain ⟨row, ⟨X, hX, hrow⟩, hvi, hm⟩ := hrows i hiQ
    exact Or.inr ⟨X, row, hX, hrow, hvi ▸ hiH, hm⟩

/-! ## FG root -/

/-- store の FG root は genesis か、bodies のどれかの `D` の導出の `j` で、bodies にある `D` の祖先 `X` の行に、`H` の署名者の
`matchesEntry heightPair hJ (root FG root)` のものがある。 -/
theorem fgRoot_honestRow {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st)
    (hj : JCarrier e cfg st) {H : VSet} (hqh : QuorumHonest e H) :
    getFgRoot (storeToHealing st.core) = Block.Genesis ∨
      ∃ D X row, D ∈ st.bodies.elems ∧ (deriveNamed e cfg D).j = getFgRoot (storeToHealing st.core) ∧
        X ∈ st.bodies.elems ∧ namedPreceq X D = true ∧ row ∈ namedAttestations X ∧ row.valIndex ∈ H.elems ∧
        matchesEntry row.heightPair (deriveNamed e cfg D).hJ (root (getFgRoot (storeToHealing st.core))) = true := by
  obtain ⟨D, hD, hDj⟩ := fgRoot_justified h hj
  rcases justification_honestRow e cfg hqh D with ⟨-, hg⟩ | ⟨X, row, hX, hrow, hH, hm⟩
  · left
    rw [← hDj, hg]
  · right
    refine ⟨D, X, row, hD, hDj, Proofs.Consensus.Attribution.ancestor_mem_bodies h.closed hD hX, hX, hrow, hH, ?_⟩
    rw [← hDj]
    exact hm

section RunRoot

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の直前のノード `v` の FG root は genesis か、bodies のどれかの `D` の導出の `j` で、`v` がある時刻 `t` に処理した
`D` の祖先 `X` が、honest な署名者 `w` の行を運び、`w` は時刻 `t` 以前にその行を実際に出した。行は `matchesEntry heightPair hJ
(root FG root)`。前提はどの定足数にも honest な署名者がいること(`QuorumHonest`)と、`UnforgeableSignatures` の carried の半分 `hcar`。 -/
theorem stateBefore_fgRoot_honestEmission (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (i : Nat) (v : ValidatorId) :
    getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) = Block.Genesis ∨
      ∃ D X row t t2, D ∈ (worldAt (stateBefore c p a nr s rho i) v).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) ∧
        namedPreceq X D = true ∧ row ∈ namedAttestations X ∧ row.valIndex ∈ rho.honest.elems ∧
        matchesEntry row.heightPair (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core))) = true ∧
        Processes c p a nr s rho v (NamedObject.Block X) t ∧ t2 ≤ t ∧
        Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 := by
  rcases fgRoot_honestRow (stateBefore_inv c p a nr s rho i v) (stateBefore_jcarrier c p a nr s rho i v) hqh with hg | ⟨D, X, row, hD, hDj, hXb, hX, hrow, hH, hm⟩
  · exact Or.inl hg
  · right
    rcases Proofs.Consensus.Attribution.bodies_processed c p a nr s rho v i X hXb with rfl | ⟨t, hproc⟩
    · simp [namedAttestations] at hrow
    · have hhon : rho.honest.contains row.valIndex = true := (contains_iff_mem vid_eq _ _).mpr hH
      obtain ⟨t2, ht2, hem⟩ := hcar v (NamedObject.Block X) t hproc (NamedObject.Attest row)
        (Proofs.Consensus.Attribution.carries_attest hrow) row.valIndex ⟨hhon, rfl⟩
      exact ⟨D, X, row, t, t2, hD, hDj, hX, hrow, hH, hm, hproc, ht2, hem⟩

/-- 時刻 `< time` の読みの版(前提に `EventsSorted` を足し、`stateBefore` の読みに写す)。手書き
`processedJustification_confirmationWitness` の前半に当たる(処理の時刻 `t < time` まで返す版は
`stateBeforeTime_fgRoot_honestEmission_lt`)。 -/
theorem stateBeforeTime_fgRoot_honestEmission (hs : EventsSorted rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (v : ValidatorId) (time : Int) :
    getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) = Block.Genesis ∨
      ∃ D X row t t2, D ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j =
          getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        namedPreceq X D = true ∧ row ∈ namedAttestations X ∧ row.valIndex ∈ rho.honest.elems ∧
        matchesEntry row.heightPair (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))) = true ∧
        Processes c p a nr s rho v (NamedObject.Block X) t ∧ t2 ≤ t ∧
        Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 := by
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs time]
  exact stateBefore_fgRoot_honestEmission c p a nr s rho hqh hcar _ v

/-! ## 処理の時刻を読みの時刻より前に抑える -/

/-- `stateBefore i` のノード `u` の bodies の genesis でないブロックは、添字 `j < i` の event(時刻 `t`)で `u` が処理した
ブロック。`Attribution.bodies_processed` に処理の event の添字を足したもの。手書き `Bridges.processes_block_of_mem_T` の
添字つきの読み。 -/
theorem bodies_processed_before (u : ValidatorId) :
    ∀ (i : Nat) (X : NamedBlock), X ∈ (worldAt (stateBefore c p a nr s rho i) u).st.bodies.elems →
      X = NamedBlock.Genesis ∨ ∃ (j : Nat) (ev : NamedEvent) (t : Int), j < i ∧ rho.events[j]? = some ev ∧
        eventTime ev = t ∧ Processes c p a nr s rho u (NamedObject.Block X) t
  | 0, X, hX => by
    left
    have hX' : X ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hX
    exact (mem_singleton_iff _ _).mp hX'
  | i + 1, X, hX => by
    have lift : (X = NamedBlock.Genesis ∨ ∃ (j : Nat) (ev : NamedEvent) (t : Int), j < i ∧ rho.events[j]? = some ev ∧
        eventTime ev = t ∧ Processes c p a nr s rho u (NamedObject.Block X) t) →
        X = NamedBlock.Genesis ∨ ∃ (j : Nat) (ev : NamedEvent) (t : Int), j < i + 1 ∧ rho.events[j]? = some ev ∧
          eventTime ev = t ∧ Processes c p a nr s rho u (NamedObject.Block X) t := by
      rintro (h | ⟨j, ev, t, hj, hev, ht, hp⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, ev, t, Nat.lt_succ_of_lt hj, hev, ht, hp⟩
    cases hev : rho.events[i]? with
    | none =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_none c p a nr s rho hev] at hX
      exact lift (bodies_processed_before u i X hX)
    | some ev =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at hX
      cases ev with
      | Tick w t =>
        unfold worldStep at hX
        dsimp only at hX
        by_cases hwu : w = u
        · subst hwu
          rw [Proofs.Consensus.Signing.worldAt_insert_self] at hX
          rcases Proofs.Consensus.Attribution.nodeTick_bodies c p a nr s w _ t hX with h | h
          · exact lift (bodies_processed_before w i X h)
          · exact Or.inr ⟨i, _, t, Nat.lt_succ_self i, hev, rfl,
              Or.inl ((Proofs.Consensus.Signing.emits_iff c p a nr s rho w _ t).mpr ⟨i, hev, h⟩)⟩
        · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwu] at hX
          exact lift (bodies_processed_before u i X hX)
      | Deliver w o t =>
        unfold worldStep at hX
        dsimp only at hX
        by_cases hwu : w = u
        · subst hwu
          rw [Proofs.Consensus.Signing.worldAt_insert_self] at hX
          rcases Proofs.Consensus.Attribution.nodeProcess_bodies c p s hX with h | rfl
          · exact lift (bodies_processed_before w i X h)
          · exact Or.inr ⟨i, _, t, Nat.lt_succ_self i, hev, rfl, Or.inr ⟨i, hev⟩⟩
        · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwu] at hX
          exact lift (bodies_processed_before u i X hX)

/-- 添字 `idxLt time` より前の event の時刻は `time` より前(`EventsSorted` の下で。重複なしは要らない)。 -/
theorem time_lt_of_lt_idxLt (hs : EventsSorted rho) {time : Int} {j : Nat} {ev : NamedEvent}
    (hj : j < Proofs.Consensus.ReceiverFinality.idxLt rho time) (hev : rho.events[j]? = some ev) : eventTime ev < time := by
  have hmem : ev ∈ rho.events.take (Proofs.Consensus.ReceiverFinality.idxLt rho time) := by
    rw [List.mem_iff_getElem?]
    refine ⟨j, ?_⟩
    rw [List.getElem?_take]
    split
    · exact hev
    · omega
  rw [← Proofs.Consensus.ReceiverFinality.filter_eq_take_idxLt rho hs] at hmem
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

/-- `stateBefore_fgRoot_honestEmission` に、処理の event の添字が `i` より前であることを足したもの。 -/
theorem stateBefore_fgRoot_honestEmission_before (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (i : Nat) (v : ValidatorId) :
    getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) = Block.Genesis ∨
      ∃ D X row j ev t t2, D ∈ (worldAt (stateBefore c p a nr s rho i) v).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) ∧
        namedPreceq X D = true ∧ row ∈ namedAttestations X ∧ row.valIndex ∈ rho.honest.elems ∧
        matchesEntry row.heightPair (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core))) = true ∧
        j < i ∧ rho.events[j]? = some ev ∧ eventTime ev = t ∧
        Processes c p a nr s rho v (NamedObject.Block X) t ∧ t2 ≤ t ∧
        Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 := by
  rcases fgRoot_honestRow (stateBefore_inv c p a nr s rho i v) (stateBefore_jcarrier c p a nr s rho i v) hqh with hg | ⟨D, X, row, hD, hDj, hXb, hX, hrow, hH, hm⟩
  · exact Or.inl hg
  · right
    rcases bodies_processed_before c p a nr s rho v i X hXb with rfl | ⟨j, ev, t, hj, hev, het, hproc⟩
    · simp [namedAttestations] at hrow
    · have hhon : rho.honest.contains row.valIndex = true := (contains_iff_mem vid_eq _ _).mpr hH
      obtain ⟨t2, ht2, hem⟩ := hcar v (NamedObject.Block X) t hproc (NamedObject.Attest row)
        (Proofs.Consensus.Attribution.carries_attest hrow) row.valIndex ⟨hhon, rfl⟩
      exact ⟨D, X, row, j, ev, t, t2, hD, hDj, hX, hrow, hH, hm, hj, hev, het, hproc, ht2, hem⟩

/-- **時刻 `< time` の読みの FG root の honest な発行は `time` より前**: `stateBeforeTime_fgRoot_honestEmission` に、処理の時刻
`t < time`(よって発行の時刻 `t2 < time`)を足したもの。手書き `processedJustification_confirmationWitness` の前半の `ta < time`
に当たる。 -/
theorem stateBeforeTime_fgRoot_honestEmission_lt (hs : EventsSorted rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (v : ValidatorId) (time : Int) :
    getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) = Block.Genesis ∨
      ∃ D X row t t2, D ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j =
          getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        namedPreceq X D = true ∧ row ∈ namedAttestations X ∧ row.valIndex ∈ rho.honest.elems ∧
        matchesEntry row.heightPair (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))) = true ∧
        Processes c p a nr s rho v (NamedObject.Block X) t ∧ t < time ∧ t2 ≤ t ∧ t2 < time ∧
        Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 := by
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs time]
  rcases stateBefore_fgRoot_honestEmission_before c p a nr s rho hqh hcar _ v with hg | ⟨D, X, row, j, ev, t, t2, hD, hDj, hX, hrow, hH, hm, hj, hev, het, hproc, ht2, hem⟩
  · exact Or.inl hg
  · have htime : t < time := het ▸ time_lt_of_lt_idxLt rho hs hj hev
    exact Or.inr ⟨D, X, row, t, t2, hD, hDj, hX, hrow, hH, hm, hproc, htime, ht2, lt_of_le_of_lt ht2 htime, hem⟩

end RunRoot

end Proofs.Consensus.JustificationCertificate
