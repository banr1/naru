import Model.Consensus.Spec.Interface
import Statements.Consensus.Spec.Properties
import Proofs.Consensus.Nested
import Proofs.Consensus.FinalizedMonotone
import Proofs.Consensus.RecordGrowth
import Mathlib.Tactic

/-!
# 出力 `getConfirmed` / `getStable` への転送(C71 の liveness 系 claim の足場)

利用者が読む出力は記録そのものではなく `getStable st = if f ⪯ latestStable then latestStable else f`、
`getConfirmed st = if getStable ⪯ latestConfirmed then latestConfirmed else getStable`(`Model/Consensus/Protocol/Handlers.lean`)。
claim `available` の結論 `SafeFrom g t0 = AgreeFrom g t0 ∧ MonotoneFrom g t0`(`g` は Confirmed / Stable)を、store の欄
(`f` / `latestConfirmed` / `latestStable`)についての事実に還元する:
- stable の出力: `f` の単調性(`FinalizedMonotone.lean`、`EventsSorted` だけ)、`latestStable` の単調性(`RecordGrowth.lean`、
  時刻をまたぐ記録の一致から)、`latestStable` と後の `f` の互換(`getStable_mono`)。一致は 4 つの欄の組の互換から
  (`getStable_compatible`)。
- 確認の出力: 上に加えて regime の事実 `StableBelowConfirmed`(stable の記録は確認の記録の接頭辞。`updateConfirmationWith` の
  不変条件ではなく、honest な Goldfish head の SG root に対する正準性が安全性の regime の下で与える — 手書きの注記)が、
  読みの `getStable` を `latestConfirmed` の下に置く(`getConfirmed_mono` / `getConfirmed_compatible`)。
残るのは、`SleepyRegime` の下でこれらの欄の事実(記録の一致・交差の互換・`StableBelowConfirmed`・finalized の一致)を
Goldfish の投票と確認の本体から示すことで、それはまだ証明していない。
手書き `DecoupledConsensusProofs/Protocol/Handlers/ConfirmedOutput.lean`(`finalized_preceq_get_confirmed` /
`get_stable_eq_finalized_of_not_preceq` / `get_confirmed_mono` / `confirmedOutputCompatibleFrom_of_fields` /
`confirmedOutputMonotoneFrom_of_cross`)の筋。
-/

namespace Proofs.Consensus.Outputs

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Blocks Proofs.Consensus.Nested Proofs.Consensus.Runs Proofs.Consensus.RecordGrowth

/-! ## store の出力 -/

/-- regime の事実: stable の記録は確認の記録の接頭辞。手書き `Protocol.StableBelowConfirmed`。 -/
def StableBelowConfirmed (st : Store) : Prop := preceq st.latestStable st.latestConfirmed = true

/-- finalized は確認の出力の接頭辞(任意の store)。 -/
theorem f_preceq_getConfirmed (st : Store) : preceq st.f (getConfirmed st) = true :=
  preceq_trans (f_preceq_getStable st) (getStable_preceq_getConfirmed st)

/-- `getStable` の分岐。 -/
theorem getStable_eq (st : Store) :
    (preceq st.f st.latestStable = true ∧ getStable st = st.latestStable) ∨
      (¬ preceq st.f st.latestStable = true ∧ getStable st = st.f) := by
  unfold getStable
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- `getConfirmed` の分岐。 -/
theorem getConfirmed_eq (st : Store) :
    (preceq (getStable st) st.latestConfirmed = true ∧ getConfirmed st = st.latestConfirmed) ∨
      (¬ preceq (getStable st) st.latestConfirmed = true ∧ getConfirmed st = getStable st) := by
  unfold getConfirmed
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- stable の出力は確認の記録の下にある(regime の事実と `f ⪯ latestConfirmed` の下で)。手書き `get_stable_preceq_latest`。 -/
theorem getStable_preceq_latestConfirmed {st : Store} (hs : StableBelowConfirmed st)
    (h : preceq st.f st.latestConfirmed = true) : preceq (getStable st) st.latestConfirmed = true := by
  rcases getStable_eq st with ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he]
  · exact hs
  · exact h

/-- 確認の記録に届かない stable の出力は finalized そのもの(regime の事実の下で)。手書き `get_stable_eq_finalized_of_not_preceq`。 -/
theorem getStable_eq_f_of_not_preceq {st : Store} (hs : StableBelowConfirmed st)
    (hnot : ¬ preceq (getStable st) st.latestConfirmed = true) : getStable st = st.f := by
  rcases getStable_eq st with ⟨-, he⟩ | ⟨-, he⟩
  · exact absurd (he ▸ hs) hnot
  · exact he

/-- finalized を延ばす確認の記録はそのまま出力される(regime の事実の下で)。手書き `get_confirmed_eq_latest`。 -/
theorem getConfirmed_eq_latest {st : Store} (hs : StableBelowConfirmed st)
    (h : preceq st.f st.latestConfirmed = true) : getConfirmed st = st.latestConfirmed := by
  rcases getConfirmed_eq st with ⟨-, he⟩ | ⟨hn, -⟩
  · exact he
  · exact absurd (getStable_preceq_latestConfirmed hs h) hn

/-- 確認の記録と finalized の共通の上界は出力の上界(regime の事実の下で)。手書き `get_confirmed_preceq`。 -/
theorem getConfirmed_preceq {st : Store} {B : Block} (hs : StableBelowConfirmed st)
    (hF : preceq st.f B = true) (hL : preceq st.latestConfirmed B = true) : preceq (getConfirmed st) B = true := by
  rcases getConfirmed_eq st with ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he]
  · exact hL
  · rcases getStable_eq st with ⟨-, hs'⟩ | ⟨-, hs'⟩ <;> rw [hs']
    · exact preceq_trans hs hL
    · exact hF

/-- 確認の記録の接頭辞は、finalized と互換なら出力の接頭辞(regime の事実の下で)。手書き `preceq_get_confirmed_of_latest`。 -/
theorem preceq_getConfirmed_of_latest {st : Store} {B : Block} (hs : StableBelowConfirmed st)
    (hL : preceq B st.latestConfirmed = true) (hF : compatible B st.f = true) : preceq B (getConfirmed st) = true := by
  rcases getConfirmed_eq st with ⟨-, he⟩ | ⟨hn, he⟩ <;> rw [he]
  · exact hL
  · rw [getStable_eq_f_of_not_preceq hs hn]
    unfold compatible at hF
    rw [Bool.or_eq_true] at hF
    rcases hF with h | h
    · exact h
    · exact absurd (getStable_preceq_latestConfirmed hs (preceq_trans h hL)) hn

/-- 確認の出力の単調性: `f` と確認の記録が進み、古い記録が新しい finalized と互換で、両方の store で regime の事実が成り立つとき。
手書き `get_confirmed_mono`。 -/
theorem getConfirmed_mono {old new : Store} (hsold : StableBelowConfirmed old) (hsnew : StableBelowConfirmed new)
    (hF : preceq old.f new.f = true) (hL : preceq old.latestConfirmed new.latestConfirmed = true)
    (hcross : compatible old.latestConfirmed new.f = true) : preceq (getConfirmed old) (getConfirmed new) = true := by
  rcases getConfirmed_eq old with ⟨-, he⟩ | ⟨hn, he⟩ <;> rw [he]
  · exact preceq_getConfirmed_of_latest hsnew hL hcross
  · rw [getStable_eq_f_of_not_preceq hsold hn]
    exact preceq_trans hF (f_preceq_getConfirmed new)

/-- stable の出力の単調性: `f` と stable の記録が進み、古い記録が新しい finalized と互換なら(regime の事実は要らない)。 -/
theorem getStable_mono {old new : Store} (hF : preceq old.f new.f = true)
    (hL : preceq old.latestStable new.latestStable = true) (hcross : compatible old.latestStable new.f = true) :
    preceq (getStable old) (getStable new) = true := by
  rcases getStable_eq old with ⟨-, ho⟩ | ⟨-, ho⟩ <;> rcases getStable_eq new with ⟨hn, hne⟩ | ⟨hn, hne⟩ <;> rw [ho, hne]
  · exact hL
  · unfold compatible at hcross
    rw [Bool.or_eq_true] at hcross
    rcases hcross with h | h
    · exact h
    · exact absurd (preceq_trans h hL) hn
  · exact preceq_trans hF hn
  · exact hF

/-- stable の出力の一致: 2 つの store の `f` / `latestStable` の 4 つの組がすべて互換なら。 -/
theorem getStable_compatible {st1 st2 : Store} (hLL : compatible st1.latestStable st2.latestStable = true)
    (hFF : compatible st1.f st2.f = true) (hLF : compatible st1.latestStable st2.f = true)
    (hFL : compatible st1.f st2.latestStable = true) : compatible (getStable st1) (getStable st2) = true := by
  rcases getStable_eq st1 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rcases getStable_eq st2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h1, h2]
  · exact hLL
  · exact hLF
  · exact hFL
  · exact hFF

/-- 確認の出力の一致: 2 つの store の `f` / `latestConfirmed` の 4 つの組がすべて互換で、両方で regime の事実が成り立つなら。
手書き `confirmedOutputCompatibleFrom_of_fields` の store の部分。 -/
theorem getConfirmed_compatible {st1 st2 : Store} (hs1 : StableBelowConfirmed st1) (hs2 : StableBelowConfirmed st2)
    (hLL : compatible st1.latestConfirmed st2.latestConfirmed = true) (hFF : compatible st1.f st2.f = true)
    (hLF : compatible st1.latestConfirmed st2.f = true) (hFL : compatible st1.f st2.latestConfirmed = true) :
    compatible (getConfirmed st1) (getConfirmed st2) = true := by
  rcases getConfirmed_eq st1 with ⟨-, h1⟩ | ⟨hn1, h1⟩ <;> rcases getConfirmed_eq st2 with ⟨-, h2⟩ | ⟨hn2, h2⟩ <;> rw [h1, h2]
  · exact hLL
  · rw [getStable_eq_f_of_not_preceq hs2 hn2]; exact hLF
  · rw [getStable_eq_f_of_not_preceq hs1 hn1]; exact hFL
  · rw [getStable_eq_f_of_not_preceq hs1 hn1, getStable_eq_f_of_not_preceq hs2 hn2]; exact hFF

/-! ## run の読みへ -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

theorem outputAt_confirmed (v : ValidatorId) (t : Int) :
    outputAt c p a nr Output.Confirmed s rho v t = getConfirmed (storeAt c p a nr s rho v t).core := rfl

theorem outputAt_stable (v : ValidatorId) (t : Int) :
    outputAt c p a nr Output.Stable s rho v t = getStable (storeAt c p a nr s rho v t).core := rfl

theorem outputAt_finalized (v : ValidatorId) (t : Int) :
    outputAt c p a nr Output.Finalized s rho v t = (storeAt c p a nr s rho v t).core.f := rfl

/-- `EventsSorted` の下で finalized は時刻について単調(`FinalizedMonotone.lean` の本体。honest / horizon の前提なし)。 -/
theorem storeAt_f_mono (hs : EventsSorted rho) (v : ValidatorId) {t t2 : Int} (h : t ≤ t2) :
    preceq (storeAt c p a nr s rho v t).core.f (storeAt c p a nr s rho v t2).core.f = true := by
  unfold storeAt readAt
  obtain ⟨l2, hl2⟩ := filter_le_append t t2 h rho.events (pairwise_of_eventsSorted rho hs)
  rw [hl2, List.foldl_append]
  exact Proofs.Consensus.FinalizedMonotone.foldl_worldStep_f c p a nr s l2 _ v

/-- 記録 `R` の時刻をまたぐ一致: honest な 2 ノードの `t0` 以後の読みの記録は互換。手書き `ConfirmationCompatibleFrom` /
`StableRecordCompatibleFrom`。 -/
def RecordAgreeFrom (R : Store → Block) (t0 : Int) : Prop :=
  ∀ u v t t2, rho.honest.contains u = true → rho.honest.contains v = true →
    t0 ≤ t → t ≤ rho.horizon → t0 ≤ t2 → t2 ≤ rho.horizon →
    compatible (R (storeAt c p a nr s rho u t).core) (R (storeAt c p a nr s rho v t2).core) = true

/-- 記録 `R` と finalized の交差の互換: honest な 2 ノードの `t0` 以後の読みで、記録は finalized と互換。 -/
def CrossAgreeFrom (R : Store → Block) (t0 : Int) : Prop :=
  ∀ u v t t2, rho.honest.contains u = true → rho.honest.contains v = true →
    t0 ≤ t → t ≤ rho.horizon → t0 ≤ t2 → t2 ≤ rho.horizon →
    compatible (R (storeAt c p a nr s rho u t).core) (storeAt c p a nr s rho v t2).core.f = true

/-- regime の事実 `StableBelowConfirmed` が honest なノードの `t0` 以後のすべての読みで成り立つ。 -/
def StableBelowConfirmedFrom (t0 : Int) : Prop :=
  ∀ v t, rho.honest.contains v = true → t0 ≤ t → t ≤ rho.horizon → StableBelowConfirmed (storeAt c p a nr s rho v t).core

/-- 記録 `R` の同じノードでの時刻をまたぐ一致(単調性に要る分だけ: honest な `v` の `t0 ≤ t ≤ t2 ≤ horizon` の 2 つの読み)。 -/
def RecordSelfAgreeFrom (R : Store → Block) (t0 : Int) : Prop :=
  ∀ v t t2, rho.honest.contains v = true → t0 ≤ t → t ≤ t2 → t2 ≤ rho.horizon →
    compatible (R (storeAt c p a nr s rho v t).core) (R (storeAt c p a nr s rho v t2).core) = true

/-- 記録 `R` と後の finalized の互換(単調性に要る分だけ: 同じノードの `t ≤ t2`)。手書き `confirmedOutputMonotoneFrom_of_cross` の `hcross`。 -/
def CrossSelfAgreeFrom (R : Store → Block) (t0 : Int) : Prop :=
  ∀ v t t2, rho.honest.contains v = true → t0 ≤ t → t ≤ t2 → t2 ≤ rho.horizon →
    compatible (R (storeAt c p a nr s rho v t).core) (storeAt c p a nr s rho v t2).core.f = true

theorem RecordAgreeFrom.self {R : Store → Block} {t0 : Int} (h : RecordAgreeFrom c p a nr s rho R t0) :
    RecordSelfAgreeFrom c p a nr s rho R t0 :=
  fun v t t2 hv ht0 htt2 hhor => h v v t t2 hv hv ht0 (htt2.trans hhor) (ht0.trans htt2) hhor

theorem CrossAgreeFrom.self {R : Store → Block} {t0 : Int} (h : CrossAgreeFrom c p a nr s rho R t0) :
    CrossSelfAgreeFrom c p a nr s rho R t0 :=
  fun v t t2 hv ht0 htt2 hhor => h v v t t2 hv hv ht0 (htt2.trans hhor) (ht0.trans htt2) hhor

/-- stable の出力の単調性(property `MonotoneFrom … Stable t0`): 同じノードでの `latestStable` の一致と、`latestStable` と後の finalized の互換から。 -/
theorem monotoneFrom_stable_of_fields (hs : EventsSorted rho) (hnd : EventsNodup rho) (t0 : Int)
    (hL : RecordSelfAgreeFrom c p a nr s rho (fun st => st.latestStable) t0)
    (hX : CrossSelfAgreeFrom c p a nr s rho (fun st => st.latestStable) t0) :
    MonotoneFrom c p a nr s rho Output.Stable t0 := by
  unfold MonotoneFrom
  intro v t t2 h
  obtain ⟨⟨⟨hv, ht0⟩, htt2⟩, hhor⟩ := h
  rw [outputAt_stable, outputAt_stable]
  refine getStable_mono (storeAt_f_mono c p a nr s rho hs v htt2) ?_ (hX v t t2 hv ht0 htt2 hhor)
  exact stable_mono_of_compatible c p a nr s rho hs (nodup_of_eventsNodup rho hnd) v htt2
    (fun τ hτ hτ2 => hL v t τ hv ht0 hτ (hτ2.trans hhor))

/-- 確認の出力の単調性(property `MonotoneFrom … Confirmed t0`): regime の事実と、同じノードでの `latestConfirmed` の一致・後の finalized との互換から。
手書き `confirmedOutputMonotoneFrom_of_cross`。 -/
theorem monotoneFrom_confirmed_of_fields (hs : EventsSorted rho) (hnd : EventsNodup rho) (t0 : Int)
    (hsbc : StableBelowConfirmedFrom c p a nr s rho t0)
    (hL : RecordSelfAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hX : CrossSelfAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    MonotoneFrom c p a nr s rho Output.Confirmed t0 := by
  unfold MonotoneFrom
  intro v t t2 h
  obtain ⟨⟨⟨hv, ht0⟩, htt2⟩, hhor⟩ := h
  rw [outputAt_confirmed, outputAt_confirmed]
  refine getConfirmed_mono (hsbc v t hv ht0 (htt2.trans hhor)) (hsbc v t2 hv (ht0.trans htt2) hhor)
    (storeAt_f_mono c p a nr s rho hs v htt2) ?_ (hX v t t2 hv ht0 htt2 hhor)
  exact confirmed_mono_of_compatible c p a nr s rho hs (nodup_of_eventsNodup rho hnd) v htt2
    (fun τ hτ hτ2 => hL v t τ hv ht0 hτ (hτ2.trans hhor))

/-- stable の出力の一致(property `AgreeFrom … Stable t0`): `latestStable` の一致、finalized の一致、交差の互換から。 -/
theorem agreeFrom_stable_of_fields (t0 : Int)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestStable) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestStable) t0) :
    AgreeFrom c p a nr s rho Output.Stable t0 := by
  unfold AgreeFrom ConsistentFrom at hF ⊢
  intro u v t t2 h
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, ht0⟩, hhor⟩, ht02⟩, hhor2⟩ := h
  rw [outputAt_stable, outputAt_stable]
  refine getStable_compatible (hL u v t t2 hu hv ht0 hhor ht02 hhor2) ?_ (hX u v t t2 hu hv ht0 hhor ht02 hhor2) ?_
  · have := hF u v t t2 ⟨⟨⟨⟨⟨hu, hv⟩, ht0⟩, hhor⟩, ht02⟩, hhor2⟩
    rw [outputAt_finalized, outputAt_finalized] at this
    exact this
  · rw [compatible_comm]
    exact hX v u t2 t hv hu ht02 hhor2 ht0 hhor

/-- 確認の出力の一致(property `AgreeFrom … Confirmed t0`): regime の事実、`latestConfirmed` の一致、finalized の一致、交差の互換から。
手書き `confirmedOutputCompatibleFrom_of_fields`。 -/
theorem agreeFrom_confirmed_of_fields (t0 : Int) (hsbc : StableBelowConfirmedFrom c p a nr s rho t0)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    AgreeFrom c p a nr s rho Output.Confirmed t0 := by
  unfold AgreeFrom ConsistentFrom at hF ⊢
  intro u v t t2 h
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, ht0⟩, hhor⟩, ht02⟩, hhor2⟩ := h
  rw [outputAt_confirmed, outputAt_confirmed]
  refine getConfirmed_compatible (hsbc u t hu ht0 hhor) (hsbc v t2 hv ht02 hhor2) (hL u v t t2 hu hv ht0 hhor ht02 hhor2) ?_
    (hX u v t t2 hu hv ht0 hhor ht02 hhor2) ?_
  · have := hF u v t t2 ⟨⟨⟨⟨⟨hu, hv⟩, ht0⟩, hhor⟩, ht02⟩, hhor2⟩
    rw [outputAt_finalized, outputAt_finalized] at this
    exact this
  · rw [compatible_comm]
    exact hX v u t2 t hv hu ht02 hhor2 ht0 hhor

/-- stable の出力の `SafeFrom`(claim `available` の結論の一部)を store の欄の事実に還元する。 -/
theorem safeFrom_stable_of_fields (hs : EventsSorted rho) (hnd : EventsNodup rho) (t0 : Int)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestStable) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestStable) t0) :
    SafeFrom c p a nr s rho Output.Stable t0 :=
  ⟨agreeFrom_stable_of_fields c p a nr s rho t0 hL hF hX,
   monotoneFrom_stable_of_fields c p a nr s rho hs hnd t0 hL.self hX.self⟩

/-- 確認の出力の `SafeFrom`(claim `available` の結論の一部)を store の欄の事実と regime の事実に還元する。 -/
theorem safeFrom_confirmed_of_fields (hs : EventsSorted rho) (hnd : EventsNodup rho) (t0 : Int)
    (hsbc : StableBelowConfirmedFrom c p a nr s rho t0)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0) :
    SafeFrom c p a nr s rho Output.Confirmed t0 :=
  ⟨agreeFrom_confirmed_of_fields c p a nr s rho t0 hsbc hL hF hX,
   monotoneFrom_confirmed_of_fields c p a nr s rho hs hnd t0 hsbc hL.self hX.self⟩

end Run

end Proofs.Consensus.Outputs
