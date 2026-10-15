import Proofs.Consensus.Signing
import Proofs.Consensus.Carrier
import Proofs.Consensus.Attribution
import Proofs.Consensus.TreeInv
import Proofs.Consensus.Goldfish
import Mathlib.Tactic

/-!
# attestation の行の FG source(C71 の補題)

honest な行の height pair `Vote h entry nu` が、その tick の attestation の務めが読んだ store の FG source から作られたことを示す。
生成 Model の attestation の務め `attestWith`(`Model/Consensus/Protocol/Duties/Proposals.lean`)は、store `st3`(tick の時計合わせ・
提案・投票・確認の更新の後)を `storeToHealing` で読み、`attestationInput` の欄 `fields` を `getFgVoteWith` の最初の成分にする。
それは FG source `q = fgSourceWith … (roundOf hc st3.s) (grade2BlockWith …)` の chain 状態 `chainStateOf sigma q` の
`(h, root tH, nj)` で、source が無ければ `none`。署名クライアント `namedCreate` は行の height pair を `encodeHeight fields _` で
作り、`fields = none` か元の pair が `Empty` なら `Empty`、元の pair が `Target` / `Timeout` で `fields = some (h, entry, _)` なら
`Vote h entry _` にする。したがって
- 行の height pair が `Vote h entry nu` なら、FG source `q` があり、`(chainStateOf sigma q).h = h`、`root (chainStateOf sigma q).tH = entry`
  (`attestWith_vote_source`)。
- tick の出力に行があれば、それは tick の中の store `st3` での `attestWith` の行で、tick の後の store は `attestWith` の後の store
  (`tick_attest_store`)。`st3` は tick の前の store から `StoreInv` を受け継ぐ。`st3` は tick の引数の関数 `tickDutyStore` で
  (`tick_attest_dutyStore` / `tickDutyStore_inv` / `tickDutyStore_treeInv`。周回 171)、以下の補題はその等式も返す。
- `liveConfirmed` が tree にあり tree が親について閉じていれば(`TreeInv` / `StoreInv`)、`q` は tree にある: `fgSourceWith` は
  `liveConfirmed` の祖先(`deepestClear`)か grade 2 のブロック(filtered tree の `activePrefix`)を返す(`fgSourceWith_mem`)。
- `StoreInv` の下で、`q` が tree にあれば bodies に `eraseBlock D = q` の `D` があり、`deriveNamed D` の `h` / `tH` の根が行の
  `h` / `entry`(`source_named`)。
- run では、`Emits w (Attest row) t` の行が `Vote h entry nu` なら、添字 `i` の event `Tick w t` の中の store `st3` で上が成り立ち、
  `stateBefore (i + 1)` の `w` の store は `st3` での `attestWith` の後の store で、bodies は `st3` の bodies に等しく、`q` は `st3` の tree に
  あって bodies に `eraseBlock D = q` の `D` がある(`emits_vote_source`)。

手書き `HealingSurface.honestEmittedHeightRow_exactFGSelectorWitness_core`(`Protocol/ChainState/FGRootWitness.lean`)の、行の
height pair を務めの FG source に結ぶところに当たる。手書きは務めの store を `actionStoreAt`(`stateBeforeTime (a r)` の時計と cache に
確認の更新を無条件に掛けた store)で読み、source が bodies にあること(`NamedActionSources.action_witness`)と `ta = a r`・
`a = actionAttestationAt …` まで示す。生成 Model の `st3` は、確認の更新を `t = supportCutoff` のときだけ掛け、同じ tick の提案・投票の
更新も含む。ここでは務めの store を tick の中の `st3` として返す。
-/

namespace Proofs.Consensus.AttestationSource

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Duties.Inputs
open Model.Consensus.Protocol.Tick Model.Consensus.Protocol.ValidatorClient Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution
open Proofs.Consensus.Records Proofs.Consensus.Carrier Proofs.Consensus.Trees

/-! ## 署名クライアント -/

/-- `encodeHeight` が `Vote h entry nu` を返すなら、`fields` は `some (h, entry, _)`。 -/
theorem encodeHeight_vote {fields : Option (Nat × BlockId × Bool)} {pair : HeightPair} {h : Nat} {entry : BlockId}
    {nu : Bool} (hv : encodeHeight fields pair = NamedHeightPair.Vote h entry nu) : ∃ x, fields = some (h, entry, x) := by
  cases fields with
  | none => cases pair <;> simp [encodeHeight] at hv
  | some f =>
    obtain ⟨h', e', x⟩ := f
    cases pair <;> simp [encodeHeight] at hv
    all_goals
      obtain ⟨rfl, rfl, -⟩ := hv
      exact ⟨x, rfl⟩

/-- `namedCreate` の行が `Vote h entry nu` なら、入力の `fields` は `some (h, entry, _)`。 -/
theorem namedCreate_vote {rec : NamedRecord} {inp : RecordInput} {h : Nat} {entry : BlockId} {nu : Bool}
    (hv : (namedCreate rec inp).2.heightPair = NamedHeightPair.Vote h entry nu) : ∃ x, inp.fields = some (h, entry, x) := by
  rw [namedCreate_row] at hv
  exact encodeHeight_vote hv

/-! ## attestation の務め -/

/-- 務めの入力の `fields` は FG source の chain 状態の `(h, root tH, nj)`。 -/
theorem attestationInput_fields (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : FGStore) :
    (creatorInput (attestationInput cache e hc nd st)).fields =
      (fgSourceWith cache e hc st (Model.Consensus.Protocol.Grades.roundOf hc st.s)
          (grade2BlockWith cache e hc st (Model.Consensus.Protocol.Grades.roundOf hc st.s))).map
        (fun q => ((chainStateOf st.sigma q).h, root (chainStateOf st.sigma q).tH, (chainStateOf st.sigma q).nj)) :=
  rfl

/-- **行の height pair が `Vote h entry nu` なら、務めの store の FG source `q` があり、その chain 状態の `h` / `tH` の根が
`h` / `entry`**。 -/
theorem attestWith_vote_source (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : NamedRecord) {h : Nat} {entry : BlockId} {nu : Bool}
    (hv : (attestWith cache e hc nd st rec).2.2.heightPair = NamedHeightPair.Vote h entry nu) :
    ∃ q, fgSourceWith cache e hc (storeToHealing st.core) (Model.Consensus.Protocol.Grades.roundOf hc st.core.s)
        (grade2BlockWith cache e hc (storeToHealing st.core) (Model.Consensus.Protocol.Grades.roundOf hc st.core.s)) =
          some q ∧
      (chainStateOf st.core.sigma q).h = h ∧ root (chainStateOf st.core.sigma q).tH = entry := by
  have h2 : (attestWith cache e hc nd st rec).2.2 =
      (namedCreate rec (creatorInput (attestationInput cache e hc nd (storeToHealing st.core)))).2 := rfl
  rw [h2] at hv
  obtain ⟨x, hx⟩ := namedCreate_vote hv
  rw [attestationInput_fields] at hx
  obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hx
  simp only [Prod.mk.injEq] at hqe
  exact ⟨q, hq, hqe.1, hqe.2.1⟩

/-! ## tick -/

/-- tick の中で attestation の務めが読む store(生成 `tick` の `st3`: 時計合わせ・提案・投票・確認の更新の後)。
手書きの `actionStoreAt` に当たる(周回 171)。 -/
def tickDutyStore (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) (t : Int) : NamedStore :=
  let s := slotOf e t
  let st0 : NamedStore := { st with core := { st.core with t := t, s := s } }
  let proposing : Bool :=
    (decide (0 < s) && (t == Model.Consensus.Protocol.Schedule.proposalTime e s)) && (p s == nd.valIndex)
  let st1 := (if proposing then proposeBlockWith c p nr cache e hc cfg nd st0 else (st0, (none : Option NamedBlock))).1
  let voting : Bool := decide (0 < s) && (t == Model.Consensus.Protocol.Schedule.voteTime e s)
  let st2 := (if voting then namedGoldfishVoteWith c cache e hc nd st1 else (st1, (none : Option GoldfishVote))).1
  if decide (0 < s) && (t == Model.Consensus.Protocol.Schedule.supportCutoff e s) then
    namedUpdateConfirmationWith cache e hc st2 (s - 1)
  else st2

/-- tick の出力に行 `row` があれば、それは `tickDutyStore` での `attestWith` の行で、tick の後の store と記録は
`attestWith` の後のもの。 -/
theorem tick_attest_dutyStore {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) (rec : NamedRecord) (t : Int) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    (tick c p a nr cache e hc cfg nd st rec t).1 =
        (attestWith cache e hc nd (tickDutyStore c p nr cache e hc cfg nd st t) rec).1 ∧
      (tick c p a nr cache e hc cfg nd st rec t).2.1 =
        (attestWith cache e hc nd (tickDutyStore c p nr cache e hc cfg nd st t) rec).2.1 ∧
      row = (attestWith cache e hc nd (tickDutyStore c p nr cache e hc cfg nd st t) rec).2.2 := by
  revert hrow
  unfold tick tickDutyStore
  dsimp only
  split_ifs
  all_goals intro hrow
  all_goals simp only [List.mem_append, List.mem_singleton] at hrow
  -- attestation を出さない 8 経路: 出力に行は無い
  all_goals (try (exfalso; rcases hrow with h | h <;> (try split at h) <;> simp at h; done))
  -- attestation を出す 8 経路
  all_goals
    rcases hrow with (h | h) | h
    · exfalso
      (try split at h) <;> simp at h
    · exfalso
      (try split at h) <;> simp at h
    · simp only [NamedObject.Attest.injEq] at h
      exact ⟨rfl, rfl, h⟩

/-- `tickDutyStore` は tick の前の store の `StoreInv` を受け継ぐ。 -/
theorem tickDutyStore_inv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (t : Int) (hi : StoreInv e cfg st) :
    StoreInv e cfg (tickDutyStore c p nr cache e hc cfg nd st t) := by
  have h0 : StoreInv e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    hi.congr rfl ⟨rfl, rfl, rfl⟩
  unfold tickDutyStore
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc (namedGoldfishVoteWith_inv c cache hc nd (proposeBlockWith_inv c p nr cache hc nd h0)) _
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc (namedGoldfishVoteWith_inv c cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc (proposeBlockWith_inv c p nr cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_inv cache hc h0 _
    | with_reducible exact namedGoldfishVoteWith_inv c cache hc nd (proposeBlockWith_inv c p nr cache hc nd h0)
    | with_reducible exact namedGoldfishVoteWith_inv c cache hc nd h0
    | with_reducible exact proposeBlockWith_inv c p nr cache hc nd h0
    | with_reducible exact h0

/-- `tickDutyStore` は(`StoreInv` の下で)tick の前の store の `TreeInv` を受け継ぐ。 -/
theorem tickDutyStore_treeInv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (t : Int) (hi : StoreInv e cfg st)
    (ht : TreeInv st.core) : TreeInv (tickDutyStore c p nr cache e hc cfg nd st t).core := by
  have hinv0 : StoreInv e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    hi.congr rfl ⟨rfl, rfl, rfl⟩
  have h0 : TreeInv { st with core := { st.core with t := t, s := slotOf e t } }.core :=
    ht.congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold tickDutyStore
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc (namedGoldfishVoteWith_treeInv c cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0)) _
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc (namedGoldfishVoteWith_treeInv c cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0) _
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc h0 _
    | with_reducible exact namedGoldfishVoteWith_treeInv c cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0)
    | with_reducible exact namedGoldfishVoteWith_treeInv c cache hc nd h0
    | with_reducible exact proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0
    | with_reducible exact h0

/-- tick の出力に行 `row` があれば、それは tick の中の store `st3`(= `tickDutyStore`)での `attestWith` の行で、tick の後の
store と記録は `attestWith` の後のもの。`st3` は tick の前の store の `StoreInv` と(`StoreInv` の下で)`TreeInv` を受け継ぐ。 -/
theorem tick_attest_store {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) (rec : NamedRecord) (t : Int) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    ∃ st3 : NamedStore, (StoreInv e cfg st → StoreInv e cfg st3) ∧
      (StoreInv e cfg st → TreeInv st.core → TreeInv st3.core) ∧
      (tick c p a nr cache e hc cfg nd st rec t).1 = (attestWith cache e hc nd st3 rec).1 ∧
      (tick c p a nr cache e hc cfg nd st rec t).2.1 = (attestWith cache e hc nd st3 rec).2.1 ∧
      row = (attestWith cache e hc nd st3 rec).2.2 ∧
      st3 = tickDutyStore c p nr cache e hc cfg nd st t := by
  obtain ⟨h1, h2, h3⟩ := tick_attest_dutyStore (e := e) (cfg := cfg) c p a nr cache hc nd st rec t hrow
  exact ⟨_, fun hi => tickDutyStore_inv c p nr cache hc nd t hi,
    fun hi ht => tickDutyStore_treeInv c p nr cache hc nd t hi ht, h1, h2, h3, rfl⟩

/-! ## FG source は tree にある -/

/-- `chainUp n c` の要素は `c` の祖先。 -/
theorem mem_chainUp_preceq : ∀ (n : Nat) {c b : Block},
    b ∈ Model.Consensus.Protocol.Grades.chainUp n c → preceq b c = true := by
  intro n
  induction n with
  | zero =>
    intro c b hb
    rw [Model.Consensus.Protocol.Grades.chainUp] at hb
    simp only [beq_self_eq_true, ↓reduceDIte, List.mem_singleton] at hb
    subst hb
    exact Proofs.Consensus.Blocks.preceq_self _
  | succ n ih =>
    intro c b hb
    rw [Model.Consensus.Protocol.Grades.chainUp] at hb
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceDIte, Nat.add_sub_cancel] at hb
    cases hp : parent? c with
    | none =>
      rw [hp] at hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact Proofs.Consensus.Blocks.preceq_self _
    | some q =>
      rw [hp] at hb
      simp only [List.singleton_append, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact Proofs.Consensus.Blocks.preceq_self _
      · exact Proofs.Consensus.Blocks.preceq_trans (ih hb) (Proofs.Consensus.Goldfish.preceq_of_parent? hp)

/-- `deepestClear floor c test` の結果は `c` の祖先。 -/
theorem deepestClear_preceq {floor : Option Block} {c b : Block} {test : Block → Bool}
    (h : Model.Consensus.Protocol.Grades.deepestClear floor c test = some b) : preceq b c = true := by
  unfold Model.Consensus.Protocol.Grades.deepestClear at h
  have hm := ((mem_filter_iff _ _ _).mp (deepest?_mem h)).1
  rw [Proofs.Consensus.Sets.mem_toSet_iff Proofs.Consensus.Orders.block_compare_eq_iff] at hm
  exact mem_chainUp_preceq _ hm

/-- grade 2 のブロック(`grade2BlockWith`)は tree の要素(filtered tree の `activePrefix`)。 -/
theorem grade2BlockWith_mem {cache : Model.Consensus.Protocol.Grades.Cache} {e : ProtocolEnv}
    {hc : Model.Consensus.Protocol.Grades.HealConfig} {hs : FGStore} {r : Nat} {q : Block}
    (h : grade2BlockWith cache e hc hs r = some q) : q ∈ hs.tree.elems := by
  unfold grade2BlockWith Model.Consensus.Protocol.Grades.frameGradeRead at h
  dsimp only at h
  unfold Model.Consensus.Protocol.Grades.grade2Block at h
  split_ifs at h
  obtain ⟨r', -, hap⟩ := Option.bind_eq_some_iff.mp h
  exact getFilteredBlockTree_sub (activePrefix_mem hap)

/-- **FG source は tree の要素**: `fgSourceWith` は `liveConfirmed` の祖先(`deepestClear`)か grade 2 のブロックを返す。
`liveConfirmed` が tree にあり tree が親について閉じていれば、どちらも tree にある。 -/
theorem fgSourceWith_mem {cache : Model.Consensus.Protocol.Grades.Cache} {e : ProtocolEnv}
    {hc : Model.Consensus.Protocol.Grades.HealConfig} {hs : FGStore} {r r' : Nat} {q : Block}
    (hlive : hs.liveConfirmed ∈ hs.tree.elems) (hclosed : ∀ x, x ∈ hs.tree.elems → parent x ∈ hs.tree.elems)
    (h : fgSourceWith cache e hc hs r (grade2BlockWith cache e hc hs r') = some q) : q ∈ hs.tree.elems := by
  unfold fgSourceWith at h
  cases hg : grade2BlockWith cache e hc hs r' with
  | none =>
    rw [hg] at h
    simp at h
  | some q0 =>
    rw [hg] at h
    dsimp only at h
    split at h
    · rename_i b hb
      simp only [Option.some.injEq] at h
      subst h
      exact ancestor_mem_tree hclosed (deepestClear_preceq hb) hlive
    · simp only [Option.some.injEq] at h
      subst h
      exact grade2BlockWith_mem hg

/-- store の版: `TreeInv` と `StoreInv`(tree が親について閉じている)の下で、務めの store の FG source は tree にある。 -/
theorem fgSource_mem_tree {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (hi : StoreInv e cfg st)
    (ht : TreeInv st.core) {cache : Model.Consensus.Protocol.Grades.Cache} {e' : ProtocolEnv}
    {hc : Model.Consensus.Protocol.Grades.HealConfig} {r r' : Nat} {q : Block}
    (h : fgSourceWith cache e' hc (storeToHealing st.core) r (grade2BlockWith cache e' hc (storeToHealing st.core) r') =
      some q) : q ∈ st.core.tree.elems :=
  fgSourceWith_mem (hs := storeToHealing st.core) ht.live (tree_closed hi) h

/-! ## source の名前付きブロック -/

/-- `StoreInv` の下で、tree にある source `q` は bodies のどれかの `D` の消去で、`D` の導出の `h` / `tH` の根は
`chainStateOf sigma q` のもの。 -/
theorem source_named {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (hi : StoreInv e cfg st) {q : Block}
    (hq : q ∈ st.core.tree.elems) {h : Nat} {entry : BlockId} (hh : (chainStateOf st.core.sigma q).h = h)
    (he : root (chainStateOf st.core.sigma q).tH = entry) :
    ∃ D, D ∈ st.bodies.elems ∧ eraseBlock D = q ∧ (deriveNamed e cfg D).h = h ∧ root (deriveNamed e cfg D).tH = entry := by
  obtain ⟨D, hD, hDq⟩ := hi.named q hq
  have hs := hi.sigma D hD
  rw [hDq] at hs
  rw [hs] at hh he
  exact ⟨D, hD, hDq, hh, he⟩

/-- tick の出力の行が `Vote h entry nu` なら、tick の中の store `st3`(`StoreInv` を受け継ぐ)の FG source `q` の chain 状態の
`h` / `tH` の根が `h` / `entry` で、`q` は `st3` の tree にあり、tick の後の store は `st3` での `attestWith` の後の store。 -/
theorem tick_vote_source {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (hi : StoreInv e cfg st) (ht : TreeInv st.core)
    (rec : NamedRecord) (t : Int) {row : NamedAttestation} (hrow : NamedObject.Attest row ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2)
    {h : Nat} {entry : BlockId} {nu : Bool} (hv : row.heightPair = NamedHeightPair.Vote h entry nu) :
    ∃ st3 q, StoreInv e cfg st3 ∧ (tick c p a nr cache e hc cfg nd st rec t).1 = (attestWith cache e hc nd st3 rec).1 ∧
      row = (attestWith cache e hc nd st3 rec).2.2 ∧
      fgSourceWith cache e hc (storeToHealing st3.core) (Model.Consensus.Protocol.Grades.roundOf hc st3.core.s)
          (grade2BlockWith cache e hc (storeToHealing st3.core) (Model.Consensus.Protocol.Grades.roundOf hc st3.core.s)) =
        some q ∧
      (chainStateOf st3.core.sigma q).h = h ∧ root (chainStateOf st3.core.sigma q).tH = entry ∧
      q ∈ st3.core.tree.elems ∧ st3 = tickDutyStore c p nr cache e hc cfg nd st t := by
  obtain ⟨st3, hinv, htr, hst, -, hr, hd⟩ := tick_attest_store (e := e) (cfg := cfg) c p a nr cache hc nd st rec t hrow
  rw [hr] at hv
  obtain ⟨q, hq, hh, he⟩ := attestWith_vote_source cache e hc nd st3 rec hv
  exact ⟨st3, q, hinv hi, hst, hr, hq, hh, he, fgSource_mem_tree (hinv hi) (htr hi ht) hq, hd⟩

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **run の発行の版**: `w` が時刻 `t` に出した行 `row` の height pair が `Vote h entry nu` なら、添字 `i` の event `Tick w t` の
中の store `st3` があり、`st3` は `StoreInv` を満たし、`stateBefore (i + 1)` の `w` の store は `st3` での `attestWith` の後の store
(よって bodies は `st3` の bodies)で、`row` は `st3` での `attestWith` の行で、`st3` の FG source `q` の chain 状態の `h` / `tH` の根が
`h` / `entry`。`cache` は tick の `onPhaseTick` の cache。`q` は `st3` の tree にあり、`stateBefore (i + 1)` の `w` の bodies に
`eraseBlock D = q` の `D` があり、`deriveNamed D` の `h` / `tH` の根が `h` / `entry`。 -/
theorem emits_vote_source {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {h : Nat} {entry : BlockId} {nu : Bool}
    (hv : row.heightPair = NamedHeightPair.Vote h entry nu) :
    ∃ (i : Nat) (cache : Model.Consensus.Protocol.Grades.Cache) (st3 : NamedStore) (q : Block),
      rho.events[i]? = some (NamedEvent.Tick w t) ∧
      cache = Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
        (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t (worldAt (stateBefore c p a nr s rho i) w).cache ∧
      st3 = tickDutyStore c p nr cache s.e s.hc s.cfg (Model.Consensus.Execution.Setup.setupNode w)
        (worldAt (stateBefore c p a nr s rho i) w).st t ∧
      StoreInv s.e s.cfg st3 ∧
      (worldAt (stateBefore c p a nr s rho (i + 1)) w).st = (attestWith cache s.e s.hc
        (Model.Consensus.Execution.Setup.setupNode w) st3 (worldAt (stateBefore c p a nr s rho i) w).signing).1 ∧
      (worldAt (stateBefore c p a nr s rho (i + 1)) w).st.bodies = st3.bodies ∧
      row = (attestWith cache s.e s.hc (Model.Consensus.Execution.Setup.setupNode w) st3
        (worldAt (stateBefore c p a nr s rho i) w).signing).2.2 ∧
      fgSourceWith cache s.e s.hc (storeToHealing st3.core) (Model.Consensus.Protocol.Grades.roundOf s.hc st3.core.s)
          (grade2BlockWith cache s.e s.hc (storeToHealing st3.core)
            (Model.Consensus.Protocol.Grades.roundOf s.hc st3.core.s)) = some q ∧
      (chainStateOf st3.core.sigma q).h = h ∧ root (chainStateOf st3.core.sigma q).tH = entry ∧
      q ∈ st3.core.tree.elems ∧
      ∃ D, D ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) w).st.bodies.elems ∧
        eraseBlock D = q ∧ (deriveNamed s.e s.cfg D).h = h ∧ root (deriveNamed s.e s.cfg D).tH = entry := by
  obtain ⟨i, hev, hrow⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho w _ t).mp hem
  rw [Proofs.Consensus.Signing.nodeTick_out] at hrow
  obtain ⟨st3, q, hinv, hst, hr, hq, hh, he, hqt, hd⟩ := tick_vote_source c p a nr _ s.hc _
    (stateBefore_inv c p a nr s rho i w) (stateBefore_treeInv c p a nr s rho i w) _ t hrow hv
  have hstore : (worldAt (stateBefore c p a nr s rho (i + 1)) w).st = (attestWith
      (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
        (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t (worldAt (stateBefore c p a nr s rho i) w).cache)
      s.e s.hc (Model.Consensus.Execution.Setup.setupNode w) st3 (worldAt (stateBefore c p a nr s rho i) w).signing).1 := by
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev]
    unfold worldStep
    dsimp only
    rw [Proofs.Consensus.Signing.worldAt_insert_self]
    unfold nodeTick profileTick
    dsimp only
    exact hst
  have hsucc : (worldAt (stateBefore c p a nr s rho (i + 1)) w).st.bodies = st3.bodies := by
    rw [hstore]
    exact Proofs.Consensus.Attribution.attestWith_bodies _ _ _ _ _ _
  refine ⟨i, _, st3, q, hev, rfl, hd, hinv, hstore, hsucc, hr, hq, hh, he, hqt, ?_⟩
  obtain ⟨D, hD, hDq, hDh, hDe⟩ := source_named hinv hqt hh he
  exact ⟨D, hsucc ▸ hD, hDq, hDh, hDe⟩

end Run

end Proofs.Consensus.AttestationSource
