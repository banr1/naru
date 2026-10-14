import Model.Consensus.Execution.Run
import Proofs.Consensus.Blocks
import Proofs.Consensus.Runs
import Proofs.Consensus.ConfirmationRecords
import Proofs.Consensus.Outputs
import Mathlib.Tactic

/-!
# 記録の順序 `latestStable ⪯ latestConfirmed` は store の不変条件(C71 の liveness 系 claim の足場)

`Outputs.lean` は確認の出力 `getConfirmed` の単調性と一致を、欄の事実と「stable の記録は確認の記録の接頭辞」
(`StableBelowConfirmed st := preceq st.latestStable st.latestConfirmed = true`)に還元した。ここではその事実が regime の
前提なしに成り立つことを示す: 2 つの記録を書くのは `updateConfirmationWith` だけで(`ConfirmationRecords.lean` の `SameRec`)、
そこでは `latestStable := stable`、`latestConfirmed := floorOnStable stable candidate old` と書く
(`Model/Consensus/Protocol/Handlers.lean`)。`floorOnStable stable cand old` は `stable ⪯ cand` なら `cand`、
`stable ⪯ old` なら `old`、でなければ `stable` 自身を返すので、どの分岐でも `stable ⪯ 結果`。初期 store では両方の記録が
`Genesis`。したがって run のどの読み(`storeAt` / `stateBefore`)の store でも成り立ち、`Outputs.lean` の
`safeFrom_confirmed_of_fields` の前提 `StableBelowConfirmedFrom` は無条件に満たされる(`stableBelowConfirmedFrom`)。さらに、stable の
記録についての欄の事実(2 ノードの一致 `RecordAgreeFrom`・finalized との交差の互換 `CrossAgreeFrom`)は確認の記録のそれから従う
(`recordAgreeFrom_stable_of_confirmed` / `crossAgreeFrom_stable_of_confirmed`)ので、2 つの出力の `SafeFrom` はどちらも確認の記録の
一致・交差の互換・finalized の一致の 3 つだけに還元される(`safeFrom_confirmed_of_records` / `safeFrom_stable_of_records`)。

手書き `DecoupledConsensusProofs/Protocol/Handlers/ConfirmationRecordOrigin.lean`(`update_confirmation_stable_le_confirmed` /
`stateBefore_stable_below_confirmed` / `StableRecord.stableBelowConfirmed_storeAt`)の筋。手書きは `storeAt` を `stateBefore` に
結ぶために `ScheduleWellFormed` を使うが、生成 Model の `storeAt` は `readAt`(event 列の `filter` の畳み込み)そのものなので、
前提は要らない。手書き `ConfirmedOutput.lean` の注記(「regime の事実で run の不変条件ではない」)は古い記述で、
手書き自身の `ConfirmationRecordOrigin.lean` がこの不変条件を示している。
-/

namespace Proofs.Consensus.RecordOrder

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers
open Model.Consensus.Protocol.Grades Model.Consensus.Protocol.Tick Model.Consensus.Protocol.ChainState
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run Model.Consensus.Spec.Interface
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Blocks Proofs.Consensus.ConfirmationRecords Proofs.Consensus.Outputs

/-! ## `updateConfirmationWith` -/

/-- `floorOnStable stable cand old` はどの分岐でも `stable` を延ばす。 -/
theorem stable_preceq_floorOnStable (stable cand old : Block) :
    preceq stable (floorOnStable stable cand old) = true := by
  unfold floorOnStable
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact preceq_self stable

/-- 確認の更新の直後は常に stable の記録 ⪯ 確認の記録(前提なし)。手書き `update_confirmation_stable_le_confirmed`。 -/
theorem updateConfirmationWith_sbc (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (k : Nat) :
    StableBelowConfirmed (updateConfirmationWith cache e hc st k) := by
  unfold StableBelowConfirmed updateConfirmationWith
  dsimp only
  exact stable_preceq_floorOnStable _ _ _

/-- 2 つの記録が等しい store の間で不変条件は移る。 -/
theorem sbc_of_sameRec {a b : Store} (h : SameRec a b) (hb : StableBelowConfirmed b) : StableBelowConfirmed a := by
  unfold StableBelowConfirmed at hb ⊢
  rw [h.confirmed, h.stable]
  exact hb

/-! ## tick と deliver -/

/-- 1 tick の務め `tick` は不変条件を保つ(記録を変えない務めは移し、確認の更新は無条件に成り立つ)。 -/
theorem tick_sbc (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : StableBelowConfirmed st.core)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    StableBelowConfirmed (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  obtain ⟨st2, h2, h3 | h3⟩ := tick_rec_shape c p a nr cache e hc cfg nd st rec t
  · exact sbc_of_sameRec h3 (sbc_of_sameRec h2 h)
  · exact sbc_of_sameRec h3 (updateConfirmationWith_sbc cache e hc st2.core _)

/-- Tick の処理 `nodeTick` は不変条件を保つ。 -/
theorem nodeTick_sbc (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    {n : NamedNodeState} (h : StableBelowConfirmed n.st.core) (t : Int) :
    StableBelowConfirmed (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_sbc c p a nr _ s.e s.hc s.cfg _ h n.signing t

/-- Deliver の処理 `nodeProcess` は記録を変えないので不変条件を保つ。 -/
theorem nodeProcess_sbc (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (h : StableBelowConfirmed n.st.core)
    (o : Model.Consensus.Execution.Objects.NamedObject) :
    StableBelowConfirmed (nodeProcess c p s n o).st.core :=
  sbc_of_sameRec (nodeProcess_rec c p s n o) h

/-- 初期 store では両方の記録が `Genesis`。 -/
theorem initial_sbc : StableBelowConfirmed initialNamedStore.core :=
  preceq_self Block.Genesis

/-! ## world と run の読み -/

/-- world のどのノードの store も不変条件を満たす。 -/
def WorldSbc (w : NamedWorld) : Prop :=
  ∀ v, StableBelowConfirmed (worldAt w v).st.core

theorem worldInit_sbc : WorldSbc worldInit := fun _ => initial_sbc

theorem worldStep_sbc (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) {w : NamedWorld}
    (h : WorldSbc w) (ev : NamedEvent) : WorldSbc (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_sbc c p a nr s u (h u) t
    · rw [hw]
      exact h v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_sbc c p s (h u) o
    · rw [hw]
      exact h v

theorem foldl_worldStep_sbc (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, WorldSbc w →
      WorldSbc (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, h => h
  | ev :: l, _, h => by
    rw [List.foldl_cons]
    exact foldl_worldStep_sbc c p a nr s l (worldStep_sbc c p a nr s h ev)

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 時刻 `t` の読み `readAt` の world は不変条件を満たす(run への前提なし)。 -/
theorem readAt_sbc (t : Int) : WorldSbc (readAt c p a nr s rho t) := by
  unfold readAt
  exact foldl_worldStep_sbc c p a nr s _ worldInit_sbc

/-- 添字 `i` の前の world `stateBefore` も不変条件を満たす。手書き `stateBefore_stable_below_confirmed`。 -/
theorem stateBefore_sbc (i : Nat) : WorldSbc (stateBefore c p a nr s rho i) := by
  unfold stateBefore
  exact foldl_worldStep_sbc c p a nr s _ worldInit_sbc

/-- どのノードのどの時刻の store でも stable の記録 ⪯ 確認の記録。手書き `StableRecord.stableBelowConfirmed_storeAt`
(手書きは `ScheduleWellFormed` を前提にするが、ここでは不要)。 -/
theorem storeAt_sbc (v : ValidatorId) (t : Int) : StableBelowConfirmed (storeAt c p a nr s rho v t).core :=
  readAt_sbc c p a nr s rho t v

/-- `Outputs.lean` の仮定 `StableBelowConfirmedFrom t0` は、どの `t0` でも前提なしに成り立つ。 -/
theorem stableBelowConfirmedFrom (t0 : Int) : StableBelowConfirmedFrom c p a nr s rho t0 :=
  fun v t _ _ _ => storeAt_sbc c p a nr s rho v t

/-! ## `Outputs.lean` の還元から仮定 `StableBelowConfirmedFrom` を外した系 -/

/-- 確認の出力の単調性: 同じノードでの `latestConfirmed` の一致と、後の finalized との互換だけから。 -/
theorem monotoneFrom_confirmed_of_records (hs : EventsSorted rho) (hnd : EventsNodup rho) (t0 : Int)
    (hL : RecordSelfAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hX : CrossSelfAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    MonotoneFrom c p a nr s rho Output.Confirmed t0 :=
  monotoneFrom_confirmed_of_fields c p a nr s rho hs hnd t0 (stableBelowConfirmedFrom c p a nr s rho t0) hL hX

/-- 確認の出力の一致: `latestConfirmed` の一致、finalized の一致、交差の互換だけから。 -/
theorem agreeFrom_confirmed_of_records (t0 : Int)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    AgreeFrom c p a nr s rho Output.Confirmed t0 :=
  agreeFrom_confirmed_of_fields c p a nr s rho t0 (stableBelowConfirmedFrom c p a nr s rho t0) hL hF hX

/-- 確認の出力の `SafeFrom`(claim `available` の結論の一部)は、3 つの欄の事実(`latestConfirmed` の一致・finalized の一致・
交差の互換)だけに還元される。 -/
theorem safeFrom_confirmed_of_records (hs : EventsSorted rho) (hnd : EventsNodup rho) (t0 : Int)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    SafeFrom c p a nr s rho Output.Confirmed t0 :=
  safeFrom_confirmed_of_fields c p a nr s rho hs hnd t0 (stableBelowConfirmedFrom c p a nr s rho t0) hL hF hX

/-! ## stable の記録の欄の事実は確認の記録のそれから従う -/

/-- 確認の記録の一致から stable の記録の一致: `latestStable ⪯ latestConfirmed` の下で、2 つの確認の記録が互換なら一方が他方の
接頭辞なので、2 つの stable の記録はともに大きい方の接頭辞(reviewer の指摘)。 -/
theorem recordAgreeFrom_stable_of_confirmed (t0 : Int)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    RecordAgreeFrom c p a nr s rho (fun st => st.latestStable) t0 := by
  intro u v t t2 hu hv h1 h2 h3 h4
  have hu' := storeAt_sbc c p a nr s rho u t
  have hv' := storeAt_sbc c p a nr s rho v t2
  have hc := hL u v t t2 hu hv h1 h2 h3 h4
  unfold StableBelowConfirmed at hu' hv'
  unfold compatible at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact compatible_of_preceq_common (preceq_trans hu' h) hv'
  · exact compatible_of_preceq_common hu' (preceq_trans hv' h)

/-- 確認の記録と finalized の交差の互換から stable の記録のそれ: `C ⪯ F` なら `S ⪯ C ⪯ F`、`F ⪯ C` なら `S` と `F` はともに `C` の接頭辞。 -/
theorem crossAgreeFrom_stable_of_confirmed (t0 : Int)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    CrossAgreeFrom c p a nr s rho (fun st => st.latestStable) t0 := by
  intro u v t t2 hu hv h1 h2 h3 h4
  have hu' := storeAt_sbc c p a nr s rho u t
  have hc := hX u v t t2 hu hv h1 h2 h3 h4
  unfold StableBelowConfirmed at hu'
  unfold compatible at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact compatible_of_preceq_common (preceq_trans hu' h) (preceq_self _)
  · exact compatible_of_preceq_common hu' h

/-- stable の出力の `SafeFrom` も、確認の記録についての 2 つの欄の事実と finalized の一致だけに還元される。 -/
theorem safeFrom_stable_of_records (hs : EventsSorted rho) (hnd : EventsNodup rho) (t0 : Int)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    SafeFrom c p a nr s rho Output.Stable t0 :=
  safeFrom_stable_of_fields c p a nr s rho hs hnd t0 (recordAgreeFrom_stable_of_confirmed c p a nr s rho t0 hL) hF
    (crossAgreeFrom_stable_of_confirmed c p a nr s rho t0 hX)

/-! ## 出力の述語の `t0` についての単調性 -/

/-- `ConsistentFrom` は開始時刻を遅らせても成り立つ。 -/
theorem ConsistentFrom.mono {g1 g2 : Model.Consensus.Spec.Interface.Output} {t0 t1 : Int} (h01 : t0 ≤ t1)
    (h : ConsistentFrom c p a nr s rho g1 g2 t0) : ConsistentFrom c p a nr s rho g1 g2 t1 := by
  unfold ConsistentFrom at h ⊢
  intro u v t t2 hh
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, ht⟩, hhor⟩, ht2⟩, hhor2⟩ := hh
  exact h u v t t2 ⟨⟨⟨⟨⟨hu, hv⟩, h01.trans ht⟩, hhor⟩, h01.trans ht2⟩, hhor2⟩

/-- `AgreeFrom` は開始時刻を遅らせても成り立つ(`finalizedSafe` の `AgreeFrom … Finalized 0` を `t0 ≥ 0` の窓に使う)。 -/
theorem AgreeFrom.mono {g : Model.Consensus.Spec.Interface.Output} {t0 t1 : Int} (h01 : t0 ≤ t1)
    (h : AgreeFrom c p a nr s rho g t0) : AgreeFrom c p a nr s rho g t1 :=
  ConsistentFrom.mono c p a nr s rho h01 h

/-- `MonotoneFrom` は開始時刻を遅らせても成り立つ。 -/
theorem MonotoneFrom.mono {g : Model.Consensus.Spec.Interface.Output} {t0 t1 : Int} (h01 : t0 ≤ t1)
    (h : MonotoneFrom c p a nr s rho g t0) : MonotoneFrom c p a nr s rho g t1 := by
  unfold MonotoneFrom at h ⊢
  intro v t t2 hh
  obtain ⟨⟨⟨hv, ht⟩, htt2⟩, hhor⟩ := hh
  exact h v t t2 ⟨⟨⟨hv, h01.trans ht⟩, htt2⟩, hhor⟩

/-- `SafeFrom` は開始時刻を遅らせても成り立つ。 -/
theorem SafeFrom.mono {g : Model.Consensus.Spec.Interface.Output} {t0 t1 : Int} (h01 : t0 ≤ t1)
    (h : SafeFrom c p a nr s rho g t0) : SafeFrom c p a nr s rho g t1 :=
  ⟨AgreeFrom.mono c p a nr s rho h01 h.1, MonotoneFrom.mono c p a nr s rho h01 h.2⟩

end Run

end Proofs.Consensus.RecordOrder
