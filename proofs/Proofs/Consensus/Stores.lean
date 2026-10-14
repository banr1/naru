import Model.Consensus.Execution.Node
import Proofs.Consensus.Blocks
import Mathlib.Tactic

/-!
# store の finalized 欄 `f` を縮めないハンドラ(C71 の補題)

生成 Model のハンドラ(`Model/Consensus/Protocol/Handlers.lean` / `Duties/Proposals.lean` / `Tick.lean` / `Execution/Node.lean`)のうち、
store の finalized ブロック `Store.f` を変えるのは `updateFinality` の最後の分岐だけで、そこでは
`prec afterJustification.f sigma.f`(真の接頭辞)が条件に入っている。したがってどのハンドラも `preceq st.f st'.f`(新しい `f` は
古い `f` の延長)を保つ。ここではそれを `Store` → `NamedStore` → `NamedNodeState`(`nodeTick` / `nodeProcess`)の順に積み上げる。
手書き `finalized_readAt_mono_of_sorted`(`DecoupledConsensusProofs/Bridge/FinalizedLive.lean`)が使う store の不変条件に当たる。
`f` を触らないハンドラは等式(`… .f = st.f`)、`f` を延ばしうるものは `preceq`(`updateFinality` / `onBlockUsing` /
`processBlockCore` / `onBlockWith` / `nodeProcess` / `proposeBlockWith` / `tick` / `nodeTick`)で述べる。
-/

namespace Proofs.Consensus.Stores

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Execution.Node
open Proofs.Consensus.Blocks

/-! ## `Store` のハンドラ -/

/-- `onGoldfishVote` は `f` を変えない(timestampVote / gfVotes だけを更新する)。 -/
theorem onGoldfishVote_f (st : Store) (u : GoldfishVote) : (onGoldfishVote st u).f = st.f := by
  unfold onGoldfishVote
  split_ifs <;> rfl

/-- `onGoldfishVoteChecked` は `f` を変えない。 -/
theorem onGoldfishVoteChecked_f (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    (onGoldfishVoteChecked c st u).f = st.f := by
  unfold onGoldfishVoteChecked
  split_ifs
  · rfl
  · exact onGoldfishVote_f st u

/-- `f` を変えない関数の `foldl` は `f` を変えない。 -/
theorem foldl_f_eq {β : Type} (g : Store → β → Store) (hg : ∀ s x, (g s x).f = s.f) :
    ∀ (l : List β) (s : Store), (List.foldl g s l).f = s.f
  | [], _ => rfl
  | x :: l, s => by rw [List.foldl_cons, foldl_f_eq g hg l, hg]

/-- `onSgVote` は `f` を変えない(timestampSgVote / sgVotes だけを更新する)。 -/
theorem onSgVote_f (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (a : CombinedAttestation) :
    (onSgVote hc st a).f = st.f := by
  unfold onSgVote
  dsimp only
  split_ifs <;> rfl

/-- `updateConfirmationWith` は `f` を変えない(liveConfirmed / latestConfirmed / latestStable だけを更新する)。 -/
theorem updateConfirmationWith_f (c : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (st : Store) (s : Nat) :
    (updateConfirmationWith c e hc st s).f = st.f := rfl

/-- `goldfishVoteWith` の store 側は `f` を変えない。 -/
theorem goldfishVoteWith_f (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : Store) :
    (goldfishVoteWith c cache e hc nd st).1.f = st.f := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_f c st _
  · rfl

/-- `updateFinality` は `f` を延ばすだけ: 変える分岐の条件に `prec afterJustification.f sigma.f` が入っている
(`afterJustification.f = st.f`)。 -/
theorem updateFinality_f (st : Store) (σ : Model.Consensus.Protocol.ChainState.ChainState) :
    preceq st.f (updateFinality st σ).f = true := by
  unfold updateFinality
  dsimp only
  split_ifs with h1 h2 h3
  all_goals first
    | exact preceq_self _
    | exact preceq_of_prec (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h2).1).1
    | exact preceq_of_prec (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h3).1).1

/-- `updateFinality_f` を、`f` が等しい別の store から始める形にしたもの。 -/
theorem updateFinality_f' {st st' : Store} (hf : st'.f = st.f) (σ : Model.Consensus.Protocol.ChainState.ChainState) :
    preceq st.f (updateFinality st' σ).f = true := hf ▸ updateFinality_f st' σ

/-- `onBlockUsing` は `f` を延ばすだけ: 拒否の分岐は store をそのまま返し、受理の分岐は `f` を変えない更新と
`onGoldfishVoteChecked` の `foldl` の後に `updateFinality` を呼ぶ。 -/
theorem onBlockUsing_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : Model.Consensus.Protocol.ChainState.ChainState → Model.Consensus.Protocol.ChainState.ChainState) :
    preceq st.f (onBlockUsing c p st b build).f = true := by
  unfold onBlockUsing
  split_ifs
  · exact preceq_self _
  · exact preceq_self _
  · exact preceq_self _
  · exact preceq_self _
  · refine updateFinality_f' ?_ _
    exact (foldl_f_eq _ (fun s u => onGoldfishVoteChecked_f c s u) _ _).trans rfl

/-- `onBlockCheckedUsing handle` は、`handle` が `f` を延ばすだけなら `f` を延ばすだけ。 -/
theorem onBlockCheckedUsing_f (handle : Store → Store) (hh : ∀ s, preceq s.f (handle s).f = true)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (b : Block) :
    preceq st.f (onBlockCheckedUsing handle hc st b).f = true := by
  unfold onBlockCheckedUsing
  split_ifs
  · exact hh st
  · exact preceq_self _

/-! ## `NamedStore` のハンドラ -/

/-- `commitBlock` の core は渡された `after` そのもの(bodies だけが分岐で変わる)。 -/
theorem commitBlock_core (before : NamedStore) (after : Store) (b : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    (commitBlock before after b).core = after := by
  unfold commitBlock
  dsimp only
  split_ifs <;> rfl

/-- `processBlockCore` は `f` を延ばすだけ(`onBlockCheckedUsing` + `onBlockUsing` を経る)。 -/
theorem processBlockCore_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (st : NamedStore)
    (b : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    preceq st.core.f (processBlockCore c p e hc cfg st b).core.f = true := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · exact preceq_self _
  · rw [commitBlock_core]
    exact onBlockCheckedUsing_f _ (fun cur => onBlockUsing_f c p cur _ _) hc st.core _

/-- `admitRow` は `f` を変えない(`onSgVote` と sgRows)。 -/
theorem admitRow_core_f (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : NamedStore)
    (row : Model.Consensus.Objects.NamedBlocks.NamedAttestation) :
    (admitRow hc st row).core.f = st.core.f := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_f hc st.core _

/-- `admitRows` は `f` を変えない。 -/
theorem admitRows_core_f (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    ∀ (rows : List Model.Consensus.Objects.NamedBlocks.NamedAttestation) (st : NamedStore),
      (admitRows hc st rows).core.f = st.core.f
  | [], _ => rfl
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_core_f hc rows (admitRow hc st row)
    unfold admitRows at ih
    rw [ih, admitRow_core_f]

/-- `admitCarried` の `f` は渡された `after` の `f`。 -/
theorem admitCarried_core_f (adm : CarriedAdmission) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (before after : NamedStore) (b : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    (admitCarried adm hc before after b).core.f = after.core.f := by
  unfold admitCarried
  split_ifs
  · exact admitRows_core_f hc _ after
  · rfl

/-- `onBlockWith` は `f` を延ばすだけ。 -/
theorem onBlockWith_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (st : NamedStore)
    (b : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    preceq st.core.f (onBlockWith c p adm e hc cfg st b).core.f = true := by
  unfold onBlockWith
  rw [admitCarried_core_f]
  exact processBlockCore_f c p e hc cfg st b

/-- 受信した object の処理 `receiptProcess` は `f` を延ばすだけ(block は `onBlockWith`、vote / attestation は `f` 不変)。 -/
theorem receiptProcess_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore)
    (o : Model.Consensus.Execution.Objects.NamedObject) :
    preceq st.core.f (receiptProcess c p s st o).core.f = true := by
  cases o with
  | Block b => exact onBlockWith_f c p _ _ _ _ st b
  | GfVote u =>
    show preceq st.core.f (onGoldfishVoteChecked c st.core u).f = true
    rw [onGoldfishVoteChecked_f]
    exact preceq_self _
  | Attest a =>
    show preceq st.core.f (admitRow s.hc st a).core.f = true
    rw [admitRow_core_f]
    exact preceq_self _

/-- Deliver の処理 `nodeProcess` は `f` を延ばすだけ。 -/
theorem nodeProcess_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState)
    (o : Model.Consensus.Execution.Objects.NamedObject) :
    preceq n.st.core.f (nodeProcess c p s n o).st.core.f = true :=
  receiptProcess_f c p s n.st o

/-! ## Tick の務め -/

/-- 提案 `proposeBlockWith` は `f` を延ばすだけ(自分のブロックを `onBlockWith` で処理する)。 -/
theorem proposeBlockWith_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) :
    preceq st.core.f (proposeBlockWith c p nr cache e hc cfg nd st).1.core.f = true := by
  unfold proposeBlockWith
  split
  · exact preceq_self _
  · rename_i b _
    exact onBlockWith_f c p CarriedAdmission.AlsoCarried e hc cfg st b

/-- `proposeBlockWith_f` を、始点の `f` を等式で与える形にしたもの(`tick_f` の `split_ifs` の後で使う)。 -/
theorem proposeBlockWith_f' (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st0 : NamedStore} {f0 : Block} (hf : st0.core.f = f0) :
    preceq f0 (proposeBlockWith c p nr cache e hc cfg nd st0).1.core.f = true :=
  hf ▸ proposeBlockWith_f c p nr cache e hc cfg nd st0

/-- 投票 `namedGoldfishVoteWith` は `f` を変えない。 -/
theorem namedGoldfishVoteWith_f (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) :
    (namedGoldfishVoteWith c cache e hc nd st).1.core.f = st.core.f := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out h
  show core.f = st.core.f
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [h]
  rw [h1]
  exact goldfishVoteWith_f c cache e hc nd st.core

/-- 確認の更新 `namedUpdateConfirmationWith` は `f` を変えない。 -/
theorem namedUpdateConfirmationWith_core_f (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (st : NamedStore) (k : Nat) :
    (namedUpdateConfirmationWith cache e hc st k).core.f = st.core.f := rfl

/-- attestation の作成 `attestWith` は `f` を変えない(`admitRow`)。 -/
theorem attestWith_f (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    (attestWith cache e hc nd st rec).1.core.f = st.core.f := by
  unfold attestWith
  split
  exact admitRow_core_f hc st _

/-- 1 tick の務め `tick` は `f` を延ばすだけ: 時計合わせは `f` 不変、提案は `proposeBlockWith_f`、投票・確認・attestation は `f` 不変。
`dsimp only` が pair の `match` を射影に落とすので、4 つの `if` を `split_ifs` で割って各経路を閉じる。 -/
theorem tick_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    preceq st.core.f (tick c p a nr cache e hc cfg nd st rec t).1.core.f = true := by
  unfold tick
  dsimp only
  split_ifs
  all_goals simp only [attestWith_f, namedUpdateConfirmationWith_core_f, namedGoldfishVoteWith_f]
  all_goals first
    | exact proposeBlockWith_f' c p nr cache e hc cfg nd rfl
    | exact preceq_self _

/-- Tick の処理 `nodeTick` は `f` を延ばすだけ。 -/
theorem nodeTick_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) :
    preceq n.st.core.f (nodeTick c p a nr s v n t).1.st.core.f = true := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_f c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

end Proofs.Consensus.Stores
