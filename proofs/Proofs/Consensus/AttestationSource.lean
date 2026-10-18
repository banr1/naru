import Proofs.Consensus.Signing
import Proofs.Consensus.Carrier
import Proofs.Consensus.Stores
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

/-- **行の `confirmed` は務めの SG 投票の根、`round` は務めの store の slot の round**: `attestationInput` は `confirmed` に
`getSgVoteWith`(grade 2 の候補を `aG2` に渡した SG 投票)の根を入れ、`namedCreate` はそれと `round` をそのまま行に写す。
手書きの `actionAttestationAt` の `confirmed = some (actionSGBlockAt …).root` に当たる(周回 194)。 -/
theorem attestWith_confirmed_round (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : NamedRecord) :
    (attestWith cache e hc nd st rec).2.2.confirmed =
        some (root (getSgVoteWith cache e hc (storeToHealing st.core) (Model.Consensus.Protocol.Grades.roundOf hc st.core.s)
          (grade2BlockWith cache e hc (storeToHealing st.core) (Model.Consensus.Protocol.Grades.roundOf hc st.core.s)))) ∧
      (attestWith cache e hc nd st rec).2.2.round = Model.Consensus.Protocol.Grades.roundOf hc st.core.s :=
  ⟨rfl, rfl⟩

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

/-! ## 務めの store の `liveConfirmed`(周回 184)

tick の中で `liveConfirmed` を書くのは確認の更新 `updateConfirmationWith` だけで、値は `Goldfish.live`(head が eligible なら
head、そうでなければ FG root)。tick の中の時計合わせ・提案(ブロックの受理)・投票はこの欄を変えない。したがって務めの store の
`liveConfirmed` は、tick の前の store の `liveConfirmed` か、務めの store の FG root か、確認の更新の直前の store の eligible な
head。手書きの段で確認の証人の `T ⪯ live_confirmed` の枝に `hlive`(live_confirmed ⪯ D)を掛けるところの、`live_confirmed` の
出どころの場合分けに当たる(手書きの対応先は `actionStoreAt_liveConfirmed_genuine_or_fgRoot`
(`Execution/RecoveryActionLiveSourceSplit.lean`)で、枝は GenuineConfirmation と FG root の 2 つ。手書きは action の store に
確認の更新を無条件に掛けるので第 1 の枝が無い。ここでは action 時刻の tick が必ず確認の更新を通ることを
`tickDutyStore_live_cases_of_actionTime` で示して 2 枝にする。周回 185)。手書きの FG root の枝は確認の更新の前の store の
FG root で、ここは更新の後の務めの store の FG root だが、確認の更新は FG root の 4 欄を変えないので値は同じ。 -/

theorem onBlockUsing_live (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : (onBlockUsing c p st b build).liveConfirmed = st.liveConfirmed := by
  rcases onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h]
  · rw [h]; exact acceptBody_live c st b _

theorem onBlockCheckedUsing_live (handle : Store → Store) (hh : ∀ s, (handle s).liveConfirmed = s.liveConfirmed)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (b : Block) :
    (onBlockCheckedUsing handle hc st b).liveConfirmed = st.liveConfirmed := by
  rcases onBlockCheckedUsing_eq handle hc st b with h | h
  · rw [h]; exact hh st
  · rw [h]

theorem processBlockCore_live (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    (processBlockCore c p e hc cfg st b).core.liveConfirmed = st.core.liveConfirmed := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · rfl
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    exact onBlockCheckedUsing_live _ (fun cur => onBlockUsing_live c p cur _ _) hc st.core _

theorem admitRow_live (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : NamedStore) (row : NamedAttestation) :
    (admitRow hc st row).core.liveConfirmed = st.core.liveConfirmed := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact (onSgVote_out hc st.core _).live

theorem admitRows_live (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    ∀ (rows : List NamedAttestation) (st : NamedStore),
      (admitRows hc st rows).core.liveConfirmed = st.core.liveConfirmed
  | [], _ => rfl
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_live hc rows (admitRow hc st row)
    unfold admitRows at ih
    exact ih.trans (admitRow_live hc st row)

theorem admitCarried_live (adm : CarriedAdmission) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (before after : NamedStore) (b : NamedBlock) :
    (admitCarried adm hc before after b).core.liveConfirmed = after.core.liveConfirmed := by
  unfold admitCarried
  split_ifs
  · exact admitRows_live hc _ after
  · rfl

theorem onBlockWith_live (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (st : NamedStore)
    (b : NamedBlock) : (onBlockWith c p adm e hc cfg st b).core.liveConfirmed = st.core.liveConfirmed := by
  unfold onBlockWith
  exact (admitCarried_live adm hc st _ b).trans (processBlockCore_live c p e hc cfg st b)

/-- 提案(自分のブロックの受理)は `liveConfirmed` を変えない。 -/
theorem proposeBlockWith_live (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) : (proposeBlockWith c p nr cache e hc cfg nd st).1.core.liveConfirmed = st.core.liveConfirmed := by
  unfold proposeBlockWith
  split
  · rfl
  · rename_i b _
    exact onBlockWith_live c p CarriedAdmission.AlsoCarried e hc cfg st b

/-- 投票は `liveConfirmed` を変えない。 -/
theorem namedGoldfishVoteWith_live (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) : (namedGoldfishVoteWith c cache e hc nd st).1.core.liveConfirmed = st.core.liveConfirmed := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out h
  show core.liveConfirmed = st.core.liveConfirmed
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [h]
  rw [h1]
  exact (goldfishVoteWith_out c cache e hc nd st.core).live

/-- 務めの store の確認の更新の前の段(時計合わせ・提案・投票)。`tickDutyStore` はこれに確認の更新を高々 1 回掛けたもの。 -/
def tickPreUpdateStore (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) (t : Int) : NamedStore :=
  let s := slotOf e t
  let st0 : NamedStore := { st with core := { st.core with t := t, s := s } }
  let proposing : Bool :=
    (decide (0 < s) && (t == Model.Consensus.Protocol.Schedule.proposalTime e s)) && (p s == nd.valIndex)
  let st1 := (if proposing then proposeBlockWith c p nr cache e hc cfg nd st0 else (st0, (none : Option NamedBlock))).1
  let voting : Bool := decide (0 < s) && (t == Model.Consensus.Protocol.Schedule.voteTime e s)
  (if voting then namedGoldfishVoteWith c cache e hc nd st1 else (st1, (none : Option GoldfishVote))).1

theorem tickDutyStore_eq_preUpdate (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (t : Int) :
    tickDutyStore c p nr cache e hc cfg nd st t =
      if decide (0 < slotOf e t) && (t == Model.Consensus.Protocol.Schedule.supportCutoff e (slotOf e t)) then
        namedUpdateConfirmationWith cache e hc (tickPreUpdateStore c p nr cache e hc cfg nd st t) (slotOf e t - 1)
      else tickPreUpdateStore c p nr cache e hc cfg nd st t := rfl

/-- 確認の更新の前の段も(`StoreInv` の下で)tick の前の store の `TreeInv` を受け継ぐ(周回 233)。 -/
theorem tickPreUpdateStore_treeInv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (t : Int) (hi : StoreInv e cfg st)
    (ht : TreeInv st.core) : TreeInv (tickPreUpdateStore c p nr cache e hc cfg nd st t).core := by
  have hinv0 : StoreInv e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    hi.congr rfl ⟨rfl, rfl, rfl⟩
  have h0 : TreeInv { st with core := { st.core with t := t, s := slotOf e t } }.core :=
    ht.congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold tickPreUpdateStore
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact namedGoldfishVoteWith_treeInv c cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0)
    | with_reducible exact namedGoldfishVoteWith_treeInv c cache hc nd h0
    | with_reducible exact proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0
    | with_reducible exact h0

/-- 確認の更新の前の段は `liveConfirmed` を変えない。 -/
theorem tickPreUpdateStore_live (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (t : Int) :
    (tickPreUpdateStore c p nr cache e hc cfg nd st t).core.liveConfirmed = st.core.liveConfirmed := by
  unfold tickPreUpdateStore
  dsimp only
  split_ifs
  all_goals simp only [namedGoldfishVoteWith_live, proposeBlockWith_live]

/-- 確認の更新の後の `liveConfirmed` は、更新の後の store の FG root か、更新の前の store の eligible な head
(`Goldfish.live` の 2 分岐。更新は FG root の 4 欄を変えない)。 -/
theorem updateConfirmationWith_live_cases (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (k : Nat) :
    (updateConfirmationWith cache e hc st k).liveConfirmed =
        getFgRoot (storeToHealing (updateConfirmationWith cache e hc st k)) ∨
      (Proofs.Consensus.Goldfish.eligible e st k (Proofs.Consensus.Goldfish.head cache e hc st k) = true ∧
        (updateConfirmationWith cache e hc st k).liveConfirmed = Proofs.Consensus.Goldfish.head cache e hc st k) := by
  rw [Proofs.Consensus.Goldfish.updateConfirmationWith_eq]
  dsimp only
  unfold Proofs.Consensus.Goldfish.live
  split_ifs with hel
  · exact Or.inr ⟨hel, rfl⟩
  · exact Or.inl rfl

/-- **務めの store の `liveConfirmed` の出どころ**(前提なし): tick の前の store の `liveConfirmed` のままか、務めの store が
確認の更新の後の store で(更新の前の store `st2` が確認の更新の前の段)、`liveConfirmed` は務めの store の FG root か、`st2` の
eligible な head。 -/
theorem tickDutyStore_live_cases (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (t : Int) :
    (tickDutyStore c p nr cache e hc cfg nd st t).core.liveConfirmed = st.core.liveConfirmed ∨
      (tickDutyStore c p nr cache e hc cfg nd st t).core.liveConfirmed =
        getFgRoot (storeToHealing (tickDutyStore c p nr cache e hc cfg nd st t).core) ∨
      (Proofs.Consensus.Goldfish.eligible e (tickPreUpdateStore c p nr cache e hc cfg nd st t).core (slotOf e t - 1)
          (Proofs.Consensus.Goldfish.head cache e hc (tickPreUpdateStore c p nr cache e hc cfg nd st t).core
            (slotOf e t - 1)) = true ∧
        (tickDutyStore c p nr cache e hc cfg nd st t).core.liveConfirmed =
          Proofs.Consensus.Goldfish.head cache e hc (tickPreUpdateStore c p nr cache e hc cfg nd st t).core
            (slotOf e t - 1)) := by
  rw [tickDutyStore_eq_preUpdate]
  split_ifs
  · exact Or.inr (updateConfirmationWith_live_cases cache e hc _ _)
  · exact Or.inl (tickPreUpdateStore_live c p nr cache e hc cfg nd st t)

/-- **action 時刻の slot は opening slot の次**(Δ > 0): `4Δ · (r · R) + 6Δ = 4Δ · (r · R + 1) + 2Δ` で `0 ≤ 2Δ < 4Δ` なので、
`4Δ` で割った床は `r · R + 1`(周回 185)。 -/
theorem slotOf_actionTime {e : ProtocolEnv} (hδ : 0 < e.delta) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (r : Nat) :
    slotOf e (Model.Consensus.Protocol.Grades.actionTime hc e.delta r) =
      Model.Consensus.Protocol.Grades.openingSlot hc r + 1 := by
  unfold slotOf Model.Consensus.Objects.Time.slotOfTime Model.Consensus.Protocol.Grades.actionTime
    Model.Consensus.Objects.Time.slotStart
  have hb : (0 : Int) < e.delta * 4 := by linarith
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb.le]
  have h : e.delta * 4 * Int.ofNat (Model.Consensus.Protocol.Grades.openingSlot hc r) + 6 * e.delta =
      2 * e.delta + ((Model.Consensus.Protocol.Grades.openingSlot hc r + 1 : Nat) : Int) * (e.delta * 4) := by
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [h, Int.add_mul_ediv_right _ _ hb.ne', Int.ediv_eq_zero_of_lt (by linarith) (by linarith), zero_add]
  simp

/-- **action 時刻は supportCutoff の時刻**(Δ > 0): action 時刻の slot `r · R + 1` は正で、その supportCutoff
`4Δ · (r · R + 1) + 2Δ` は action 時刻 `4Δ · (r · R) + 6Δ` に等しい。したがって action 時刻の tick は確認の更新の側を通る
(周回 185)。 -/
theorem supportCutoff_actionTime {e : ProtocolEnv} (hδ : 0 < e.delta) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (r : Nat) :
    (decide (0 < slotOf e (Model.Consensus.Protocol.Grades.actionTime hc e.delta r)) &&
      (Model.Consensus.Protocol.Grades.actionTime hc e.delta r ==
        Model.Consensus.Protocol.Schedule.supportCutoff e
          (slotOf e (Model.Consensus.Protocol.Grades.actionTime hc e.delta r)))) = true := by
  rw [slotOf_actionTime hδ hc r]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨Nat.succ_pos _, ?_⟩
  unfold Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Protocol.Schedule.supportCutoff slotTime
    Model.Consensus.Objects.Time.slotStart
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- **action 時刻の務めの store の `liveConfirmed`**(Δ > 0): tick の時刻 `t` が action 時刻なら、務めの store は必ず確認の更新を
通る(`supportCutoff_actionTime`)ので、`liveConfirmed` は務めの store の FG root か、確認の更新の前の段の eligible な head
(`tickDutyStore_live_cases` の第 1 の枝(tick の前の値のまま)は起きない。周回 185)。 -/
theorem tickDutyStore_live_cases_of_actionTime (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (hδ : 0 < e.delta) {t : Int} {r : Nat}
    (ht : t = Model.Consensus.Protocol.Grades.actionTime hc e.delta r) :
    (tickDutyStore c p nr cache e hc cfg nd st t).core.liveConfirmed =
        getFgRoot (storeToHealing (tickDutyStore c p nr cache e hc cfg nd st t).core) ∨
      (Proofs.Consensus.Goldfish.eligible e (tickPreUpdateStore c p nr cache e hc cfg nd st t).core (slotOf e t - 1)
          (Proofs.Consensus.Goldfish.head cache e hc (tickPreUpdateStore c p nr cache e hc cfg nd st t).core
            (slotOf e t - 1)) = true ∧
        (tickDutyStore c p nr cache e hc cfg nd st t).core.liveConfirmed =
          Proofs.Consensus.Goldfish.head cache e hc (tickPreUpdateStore c p nr cache e hc cfg nd st t).core
            (slotOf e t - 1)) := by
  subst ht
  rw [tickDutyStore_eq_preUpdate]
  split_ifs with hcut
  · exact updateConfirmationWith_live_cases cache e hc _ _
  · exact absurd (supportCutoff_actionTime hδ hc r) hcut

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

/-- **FG source の 2 つの場合**(前提なし): `fgSourceWith` の結果 `q` は、`deepestClear` が clear な祖先を見つけたなら
`liveConfirmed` の祖先、見つけなかったなら渡した grade 2 の候補 `aG2` そのもの。手書き
`actionGradeFormationAt_of_awakeWindowMajority` の `witness` の欄で `fg_source_with` を割る場合分け(`nodeQ2` で割り、
`deepest_clear` で割る。`deepest_clear_preceq` の枝が前者)に当たる(周回 182)。 -/
theorem fgSourceWith_cases {cache : Model.Consensus.Protocol.Grades.Cache} {e : ProtocolEnv}
    {hc : Model.Consensus.Protocol.Grades.HealConfig} {hs : FGStore} {r : Nat} {aG2 : Option Block} {q : Block}
    (h : fgSourceWith cache e hc hs r aG2 = some q) : preceq q hs.liveConfirmed = true ∨ aG2 = some q := by
  unfold fgSourceWith at h
  cases aG2 with
  | none => simp at h
  | some q0 =>
    dsimp only at h
    split at h
    · rename_i b hb
      simp only [Option.some.injEq] at h
      subst h
      exact Or.inl (deepestClear_preceq hb)
    · simp only [Option.some.injEq] at h
      subst h
      exact Or.inr rfl

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

/-- `StoreInv` の下で、tree にある `q` の chain 状態の `tH` は `q` の祖先(`q` は bodies の `D` の消去で、`D` の導出の
`Derivation.Inv.tH_preceq`)。手書き `derive_named_T_h_preceq`(`σ[C].T_h ⪯ C`)に当たる(周回 183)。 -/
theorem chainState_tH_preceq {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (hi : StoreInv e cfg st) {q : Block}
    (hq : q ∈ st.core.tree.elems) : preceq (chainStateOf st.core.sigma q).tH q = true := by
  obtain ⟨D, hD, rfl⟩ := hi.named q hq
  rw [hi.sigma D hD]
  exact (Proofs.Consensus.Derivation.deriveNamed_inv e cfg D).tH_preceq

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
