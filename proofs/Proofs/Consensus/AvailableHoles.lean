import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Available
import Proofs.Consensus.ShortHorizon
import Proofs.Consensus.Voting
import Mathlib.Tactic

/-!
# claim `available` の骨格(IDEAL.md C76)

claim `available` は `SetupWellFormed ∧ RunDomain ∧ SleepyRegime t0 → AvailableAt t0`。`Available.lean` の `availableAt_of_fields` が結論を
5 つの事実に還元しているので、骨格は次のとおり(入口は `Proofs/Consensus/Spec/Claims.lean` の theorem `available`):

1. 入口 `availableAt`: `t0 = 0`(GST-zero の枝。`RecoveredBy` の `genesis`)なら finalized の一致を `finalizedAgree_genesis`(確認の出力の一致
   `confirmedAgree_genesis` から `agreeFrom_finalized_of_confirmed` で下ろす。周回 214)から、
   `t0 ≠ 0`(回復の枝)なら証明済みの `agreeFrom_finalized_of_recovered` から取り、残る 4 つの事実を `availableAt_of_fields` で組み立てる。
2. GST-zero の枝の 3 つの一致(確認の記録の一致・finalized との交差の互換・確認の出力の一致)は、どれも `commonUpper_genesis`
   (2 つの読みの finalized と確認の記録の共通の上界 `CommonUpperFrom`。手書きの後の投票の務めの head)から証明済みの
   `recordAgreeFrom_of_commonUpper` / `crossAgreeFrom_of_commonUpper` / `agreeFrom_confirmed_of_commonUpper` で出す(周回 216)。
   `commonUpper_genesis` は最初の確認の時刻 `confirmationTime e 0` が `horizon` 以下なら `commonUpper_genesis_long`、より前に run が終わるなら
   確認の記録は genesis(証明済みの `ShortHorizon.storeAt_rec_short`)で finalized も genesis(証明済みの `ShortHorizon.storeAt_f_short`)なので
   上界は genesis(枝の分け方は周回 218、finalized の側は周回 220)。`commonUpper_genesis_long` は、確認の記録と finalized がそれぞれ
   ある slot 以後の投票の務めの head `voteDutyHeadAt` の祖先であることを言う穴 `recordAt_preceq_laterVoteHead` / `finalizedAt_preceq_laterVoteHead`
   から、4 つの slot の最大で上界を揃えて証明する(周回 222)。回復の枝の記録の一致と交差の互換は穴 `recordAgree_recovered` / `crossAgree_recovered`。
3. 穴(6 件): `recordAt_preceq_laterVoteHead` / `finalizedAt_preceq_laterVoteHead`(手書き `latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero` /
   `finalizedAt_preceq_laterVoteDutyHead_of_gstZero`、`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)/
   `recordAgree_recovered`(手書き `available_confirmedSafe` の `recovered` の枝)/ `crossAgree_recovered`(手書き
   `SettledBootstrapPreparedV4.latest_compatible_finalized_core`)/ `confirmedIncluded`(手書き `available_confirmedIncluded`)/
   `stableIncluded`(手書き `available_stableIncluded_any`)。

手書きは `RecoveredBy` の 2 枝で分ける: `genesis` は `WeakGenesis` に写して `gstZeroGuarantees_of_weakGenesis`
(`DecoupledConsensusProofs/Execution/GSTZeroSafetyClosedNamed.lean`)、`recovered` は `recoveryProducesHealedState` /
`boundedSafety`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の位相の保証から。一致の穴はすでに枝ごとに分けた(`commonUpper_genesis` は
`t0 = 0`、`_recovered` の 2 件は `hne : t0 ≠ 0` を受け取る)。包含の穴 2 件は義務の前提(`SetupWellFormed ∧ RunDomain ∧ SleepyRegime t0`)を
そのまま受け取り、細分するときはこの 2 枝から切る。`commonUpper_genesis` は手書きと同じく `confirmation_time S.E 0 ≤ rho.horizon` か否かでさらに分けた。
-/

namespace Proofs.Consensus.AvailableHoles

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes
open Statements.Consensus.Spec.Claims
open Proofs.Consensus.Outputs Proofs.Consensus.Available

section Holes

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- ノード `x` の slot `k` の投票の務めの head(手書き `voterHeadAt`): 投票の時刻 `voteTime e k` より前の event を畳んだ `x` の状態に
時計を合わせ、`preparedCache`(tick の前の `onPhaseTick`)で読んだ fork choice の head(`Voting.voteHeadBlock`)。
`Voting.clocked` は `setClock` と同じ式なので、読みは生成 Model の `confirmationReadAt x (voteTime e k)`(手書き `voteDutyRead`)と同じ。 -/
def voteDutyHeadAt (x : ValidatorId) (k : Nat) : Block :=
  let tv := Model.Consensus.Protocol.Schedule.voteTime s.e k
  let n := worldAt (stateBeforeTime c p a nr s rho tv) x
  Proofs.Consensus.Voting.voteHeadBlock (preparedCache s n tv) s.e s.hc
    (Proofs.Consensus.Voting.clocked s.e n.st tv).core

/-- 穴: GST-zero の枝で最初の確認の時刻が `horizon` 以下の run の、honest なノード `v` の時刻 `t` の読みの確認の記録 `latestConfirmed` は、
ある slot `first`(確認の時刻が `horizon` 以下)以後の確認の時刻が `horizon` 以下のどの slot `last` についても、honest などのノードの
slot `last + 1` の投票の務めの head の祖先。手書き `latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)に当たる。
閉じるのに要るもの: 確認の記録の出どころ(genesis・確認の選択・stable root)の場合分けと、確認の walk が後の投票の head の祖先であること
(手書き `preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero` / `protectedVoteSlots_of_gstZero_v2`)。 -/
theorem recordAt_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon)
    {v : ValidatorId} (hv : rho.honest.contains v = true) (t : Int) :
    ∃ first : Nat, Model.Consensus.Protocol.Schedule.confirmationTime s.e first ≤ rho.horizon ∧
      ∀ last, first ≤ last → Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon →
        ∀ x, rho.honest.contains x = true →
          preceq (storeAt c p a nr s rho v t).core.latestConfirmed (voteDutyHeadAt c p a nr s rho x (last + 1)) = true := by
  sorry

/-- 穴: `recordAt_preceq_laterVoteHead` の finalized の版。手書き `finalizedAt_preceq_laterVoteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)に当たる。
閉じるのに要るもの: finalized が FG root の祖先であること、FG root の確認の証人(手書き `WeakFG.fgRoot_confirmationWitness_at_read`)、
務めの出どころが後の投票の head の祖先であること(手書き `actionSources_preceq_voteDutyHead_of_gstZero`)を生成 Model の store で示すこと。
genesis の枝は `SlashableBound` を与えないので `finalizedSafe` の本体は使えない。 -/
theorem finalizedAt_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon)
    {v : ValidatorId} (hv : rho.honest.contains v = true) (t : Int) :
    ∃ first : Nat, Model.Consensus.Protocol.Schedule.confirmationTime s.e first ≤ rho.horizon ∧
      ∀ last, first ≤ last → Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon →
        ∀ x, rho.honest.contains x = true →
          preceq (storeAt c p a nr s rho v t).core.f (voteDutyHeadAt c p a nr s rho x (last + 1)) = true := by
  sorry

/-- GST-zero の枝(`t0 = 0`)で最初の確認の時刻 `confirmationTime e 0` が `horizon` 以下の run の、honest な 2 ノードの時刻 0 以後の
2 つの読みの finalized と確認の記録 `latestConfirmed` の共通の上界(`CommonUpperFrom`): 穴 `finalizedAt_preceq_laterVoteHead` /
`recordAt_preceq_laterVoteHead` の 4 つの `first` の最大を `last` とし、`u` の slot `last + 1` の投票の務めの head を上界にする
(`last` は 4 つのどれかなので確認の時刻は `horizon` 以下)。手書き `latestConfirmed_compatible_finalized_of_weakGenesis` /
`confirmedOutputCompatibleFrom_of_weakGenesis_named` の上界の揃え方。 -/
theorem commonUpper_genesis_long (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon) :
    CommonUpperFrom c p a nr s rho 0 := by
  intro u v t t2 hu hv _ _ _ _
  obtain ⟨f1, h1, hb1⟩ := finalizedAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hu t
  obtain ⟨f2, h2, hb2⟩ := recordAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hu t
  obtain ⟨f3, h3, hb3⟩ := finalizedAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hv t2
  obtain ⟨f4, h4, hb4⟩ := recordAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hv t2
  have hmax : ∀ x y : Nat, Model.Consensus.Protocol.Schedule.confirmationTime s.e x ≤ rho.horizon →
      Model.Consensus.Protocol.Schedule.confirmationTime s.e y ≤ rho.horizon →
      Model.Consensus.Protocol.Schedule.confirmationTime s.e (max x y) ≤ rho.horizon := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy]; exact hy
    · rw [max_eq_left hyx]; exact hx
  let last := max (max f1 f2) (max f3 f4)
  have hlast : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon :=
    hmax _ _ (hmax _ _ h1 h2) (hmax _ _ h3 h4)
  refine ⟨voteDutyHeadAt c p a nr s rho u (last + 1), ?_, ?_, ?_, ?_⟩
  · exact hb1 last (by omega) hlast u hu
  · exact hb2 last (by omega) hlast u hu
  · exact hb3 last (by omega) hlast u hu
  · exact hb4 last (by omega) hlast u hu

/-- 最初の確認の時刻 `confirmationTime e 0` より前に終わる run では、どのノード・どの時刻の読みでも finalized は genesis
(証明済みの `ShortHorizon.storeAt_f_short`。周回 220)。手書き `confirmedOutputCompatibleFrom_of_weakGenesis_named`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)の短い horizon の枝の局所の事実 `hfinalized` に当たる。 -/
theorem finalized_genesis_short (hwf : SetupWellFormed c p s)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hshort : rho.horizon < Model.Consensus.Protocol.Schedule.confirmationTime s.e 0) (v : ValidatorId) (t : Int) :
    (storeAt c p a nr s rho v t).core.f = Block.Genesis := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  exact Proofs.Consensus.ShortHorizon.storeAt_f_short c p a nr s rho hexec.1.1.1
    (Proofs.Consensus.Liveness.wf_facts hwf).1 hshort v t

/-- GST-zero の枝(`t0 = 0`)の共通の上界: 最初の確認の時刻が `horizon` 以下なら `commonUpper_genesis_long` から、
そうでなければ確認の記録は genesis(`ShortHorizon.storeAt_rec_short`。手書き `latestConfirmedAt_eq_genesis_of_short_horizon`)で
finalized も genesis(`finalized_genesis_short`)なので、上界は genesis。 -/
theorem commonUpper_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) :
    CommonUpperFrom c p a nr s rho 0 := by
  by_cases hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon
  · exact commonUpper_genesis_long c p a nr s rho hwf hdom hsleep hzero
  · have hshort := lt_of_not_ge hzero
    have hsch : ScheduleWellFormed s rho := by
      have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
      unfold ExecutionValid at hexec
      exact hexec.1.1.1
    have hδ : 0 ≤ s.e.delta := (Proofs.Consensus.Liveness.wf_facts hwf).1.le
    have hL (w : ValidatorId) (r : Int) : (storeAt c p a nr s rho w r).core.latestConfirmed = Block.Genesis :=
      (Proofs.Consensus.ShortHorizon.storeAt_rec_short c p a nr s rho hsch hδ hshort w r).1
    have hF (w : ValidatorId) (r : Int) : (storeAt c p a nr s rho w r).core.f = Block.Genesis :=
      finalized_genesis_short c p a nr s rho hwf hsleep hshort w r
    intro u v t t2 _ _ _ _ _ _
    refine ⟨Block.Genesis, ?_, ?_, ?_, ?_⟩
    all_goals first
      | rw [hF]; exact Proofs.Consensus.Blocks.preceq_self _
      | rw [hL]; exact Proofs.Consensus.Blocks.preceq_self _

/-- 穴: 回復の枝(`t0 ≠ 0`。`RecoveredBy` の `recovered`)の確認の記録 `latestConfirmed` の honest な 2 ノード・`t0` 以後の読みの一致。
手書き `available_confirmedSafe`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)の `recovered` の枝に当たる。
閉じるのに要るもの: `boundedSafety`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の位相の `UserConfirmationAfterHealing.latestCompatible`。 -/
theorem recordAgree_recovered {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) (hne : t0 ≠ 0) :
    RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  sorry

/-- 穴: 回復の枝(`t0 ≠ 0`)の確認の記録 `latestConfirmed` と finalized の、honest な 2 ノード・`t0` 以後の読みの交差の互換。
手書き `SettledBootstrapPreparedV4.latest_compatible_finalized_core`
(`DecoupledConsensusProofs/Execution/PreparedV4LatestFinalizedCompatibilityClosed.lean`)に当たる。
閉じるのに要るもの: 確認の記録が finalized を延ばすこと(記録についての事実。`Nested.lean` は出力 `getConfirmed` についてだけ)と、
`recordAgree_recovered` と同じ位相の一致。 -/
theorem crossAgree_recovered {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) (hne : t0 ≠ 0) :
    CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  sorry

/-- 確認の記録の一致: GST-zero の枝は共通の上界(穴 `commonUpper_genesis`)から、回復の枝は穴 `recordAgree_recovered` から。
手書き `available_confirmedSafe` の一致の半分(`RecoveredBy` の 2 枝で分ける)。 -/
theorem recordAgree {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  by_cases h0 : t0 = 0
  · subst h0
    exact recordAgreeFrom_of_commonUpper c p a nr s rho (commonUpper_genesis c p a nr s rho hwf hdom hsleep)
  · exact recordAgree_recovered c p a nr s rho hwf hdom hsleep h0

/-- 確認の記録と finalized の交差の互換: GST-zero の枝は共通の上界から(手書き `latestConfirmed_compatible_finalized_of_weakGenesis`)、
回復の枝は穴 `crossAgree_recovered` から。 -/
theorem crossAgree {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  by_cases h0 : t0 = 0
  · subst h0
    exact crossAgreeFrom_of_commonUpper c p a nr s rho (commonUpper_genesis c p a nr s rho hwf hdom hsleep)
  · exact crossAgree_recovered c p a nr s rho hwf hdom hsleep h0

/-- GST-zero の枝(`t0 = 0`)の確認の出力の一致: 共通の上界(穴 `commonUpper_genesis`)から `agreeFrom_confirmed_of_commonUpper`。
手書き `gstZeroGuarantees_of_weakGenesis` の欄 `outputCompatible`(`confirmedOutputCompatibleFrom_of_weakGenesis_named`)に当たる。 -/
theorem confirmedAgree_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) :
    AgreeFrom c p a nr s rho Output.Confirmed 0 :=
  agreeFrom_confirmed_of_commonUpper c p a nr s rho (commonUpper_genesis c p a nr s rho hwf hdom hsleep)

/-- GST-zero の枝(`t0 = 0`)の finalized の一致: 確認の出力の一致(`confirmedAgree_genesis`)を `agreeFrom_finalized_of_confirmed` で
finalized に下ろす。手書き `available_stableSafe` の `genesis` の枝の `finalized_compatible_of_confirmed_compatible` の筋。
回復の枝は `agreeFrom_finalized_of_recovered`(証明済み)。 -/
theorem finalizedAgree_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) :
    AgreeFrom c p a nr s rho Output.Finalized 0 :=
  agreeFrom_finalized_of_confirmed c p a nr s rho (confirmedAgree_genesis c p a nr s rho hwf hdom hsleep)

/-- 穴: honest な提案の確認の出力への期限 `confirmationDelay` 以内の包含。
手書き `available_confirmedIncluded`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)に当たる。
閉じるのに要るもの: `genesis` の枝は `gstZeroGuarantees_of_weakGenesis` の `userProposals`、`recovered` の枝は位相の `userConfirmation.proposals`。
どちらも honest な提案が適格な子の一意な最大になって `ghost_reaches`(`Goldfish.lean`)で選ばれることと、提案が締切までに各ノードの tree に入ること
(`ProposerRoot.lean` の `partialSynchrony_emitted_block_mem_of_fgRoot`。FG root の上界 = 手書き `hreadBound`)。 -/
theorem confirmedIncluded {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    IncludedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s) := by
  sorry

/-- 穴: honest な提案の stable の出力への期限 `stableInclusionDelay` 以内の包含。
手書き `available_stableIncluded_any`(`DecoupledConsensusProofs/Bridge/StableIncludedAnySlot.lean`)に当たる。
閉じるのに要るもの: `confirmedIncluded` と同じ包含を grade の候補 `frameSgCandidate` と stable の記録の床 `floorOnStable` に移すこと。 -/
theorem stableIncluded {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    IncludedFrom c p a nr s rho Output.Stable t0 (stableInclusionDelay s) := by
  sorry

end Holes

/-- claim `available` の骨格の入口: `t0` が 0 か否かで finalized の一致の出どころを分け、残りの 4 つの事実を穴から取って組み立てる。
手書き `concreteConsensus`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の `available` の枝に当たる。 -/
theorem availableAt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t0 : Int)
    (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) (hsleep : SleepyRegime c p a nr s rho t0) :
    AvailableAt c p a nr s rho t0 := by
  have hL := recordAgree c p a nr s rho hwf hdom hsleep
  have hX := crossAgree c p a nr s rho hwf hdom hsleep
  have hIc := confirmedIncluded c p a nr s rho hwf hdom hsleep
  have hIs := stableIncluded c p a nr s rho hwf hdom hsleep
  by_cases h0 : t0 = 0
  · subst h0
    exact availableAt_of_fields c p a nr s rho hsleep hL hX (finalizedAgree_genesis c p a nr s rho hwf hdom hsleep) hIc hIs
  · exact availableAt_of_fields_recovered c p a nr s rho hwf hdom hsleep h0 hL hX hIc hIs

end Proofs.Consensus.AvailableHoles
