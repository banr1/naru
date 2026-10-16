import Model.Consensus.Protocol.Duties.Inputs
import Proofs.Consensus.TreeInv
import Mathlib.Tactic

/-!
# grade 2 の候補は、凍結した G2 の root の祖先(C71 の補題)

生成 Model の grade 2 の候補 `grade2BlockWith c e hc st r`(`Duties/Inputs`)は、cache `c` の round `r` の frame を
`clipFrame st.f` で切り詰めた frame の G2 の結果 `some (some b)` を、filtered tree の `activePrefix` で `b` の祖先に写したもの。
G2 の結果は phase tick `onPhaseTick` が、tick の時刻がちょうど G2 の domain 時刻のときに `freezeRoot` で凍結し、
以後は再計算せず、切り詰め(`clipGrade`。結果は元の root の祖先)だけを受ける。ここではその 1 段を示す。

1. `clipGrade g f` は `g` の祖先(`clipGrade_preceq`)。切り詰めた結果が `some (some root)` なら、元の結果は
   `some (some old)` で `root ⪯ old`(`clipResult_some`)。
2. `activePrefix tree r` の結果は `r` の祖先(`activePrefix_preceq`)。grade 2 の候補は、cache の round `r` の frame の
   G2 の結果 `some (some b)` の祖先(`grade2Block_some` / `grade2BlockWith_some`)。
3. `alignRound` で回した cache のどの round の frame も、元の cache のその round の frame か未完了の frame
   (`cacheAtRound_alignRound`)。phase tick の後の cache の round `k` の frame は、回した cache の round `k` の frame に
   `completeFrame` と `clipFrame` を掛けたものか未完了の frame(`cacheAtRound_onPhaseTick`)。
4. `completeFrame` の G2 の結果は G2 の `completeOne` だけで決まり(`completeFrame_g2`)、それは元の結果のままか、
   tick の時刻が G2 の domain 時刻で `freezeRoot` の結果(`completeOne_g2_some`)。
5. 3 と 4 と 1 から、phase tick の後の cache の round `k` の G2 の結果 `some (some b)` は、tick の前の cache の round `k` の
   G2 の結果 `some (some b0)` か、この tick で凍結した `freezeRoot` の結果 `b0` で、`b ⪯ b0`(`onPhaseTick_g2_cases`)。
   2 と合わせて `grade2BlockWith_onPhaseTick_cases`。

手書きでは `JointHistoryProducers.lean` の `clip_preceq` / `clip_result_prefix` / `align_current` /
`complete_one_other` / `complete_frame_g2` と、`q2_capture_at_action_read` の本体の前半に当たる。手書きは action の読みの
cache(`preparedCache`)を直接扱い、凍結の出どころを run の帰納(`NamedCacheProvenance.completed_phase_origin`)で返す。
ここは 1 回の phase tick の段だけで、run の帰納はまだ置いていない(周回 188)。
-/

namespace Proofs.Consensus.Grade2Capture

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Parameters
open Model.Consensus.Protocol.Grades Model.Consensus.Protocol.ForkChoice.Goldfish
open Proofs.Consensus.Blocks

/-- `clipGrade g f` は `g` の祖先(`g` の親を遡る帰納法)。手書き `clip_preceq`。 -/
theorem clipGrade_preceq (g f : Block) : preceq (clipGrade g f) g = true := by
  induction g with
  | Genesis => exact preceq_self _
  | Node p s r v sup ats i ih =>
    rw [clipGrade]
    split_ifs
    · exact preceq_self _
    · exact preceq_trans ih (preceq_node p s r v sup ats i)

/-- 切り詰めた phase の結果が `some (some root)` で `P ⪯ root` なら、元の結果は `some (some old)` で `P ⪯ old`。
手書き `clip_result_prefix`。 -/
theorem clipResult_some {f P root : Block} {result : Option (Option Block)}
    (h : clipResult f result = some (some root)) (hP : preceq P root = true) :
    ∃ old, result = some (some old) ∧ preceq P old = true := by
  rcases result with _ | _ | old
  · simp [clipResult] at h
  · simp [clipResult] at h
  · simp only [clipResult, Option.map_some, Option.some.injEq] at h
    exact ⟨old, rfl, preceq_trans hP (by rw [← h]; exact clipGrade_preceq old f)⟩

/-- `activePrefix tree r` の結果は `r` の祖先。 -/
theorem activePrefix_preceq {tree : NaruStd.Set Block} {r b : Block} (h : activePrefix tree r = some b) :
    preceq b r = true := by
  unfold activePrefix at h
  exact ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp (Proofs.Consensus.Trees.deepest?_mem h)).2

/-- `grade2Block st fr = some q` なら、frame の G2 の結果は `some (some b)` で `q ⪯ b`。 -/
theorem grade2Block_some {st : FGStore} {fr : Frame} {q : Block} (h : grade2Block st fr = some q) :
    ∃ b, fr.g2 = some (some b) ∧ preceq q b = true := by
  unfold grade2Block at h
  split_ifs at h
  obtain ⟨b, hb, hap⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨x, hx, hxb⟩ := Option.bind_eq_some_iff.mp hb
  subst hxb
  exact ⟨b, hx, activePrefix_preceq hap⟩

/-- **grade 2 の候補は cache の G2 の結果の祖先**: `grade2BlockWith c e hc st r = some q` なら、cache の round `r` の frame
(切り詰める前)の G2 の結果は `some (some b)` で `q ⪯ b`(読みの切り詰め `clipFrame st.f` を `clipResult_some` で外す)。 -/
theorem grade2BlockWith_some {c : Cache} {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {q : Block}
    (h : Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith c e hc st r = some q) :
    ∃ b, (cacheAtRound c r).g2 = some (some b) ∧ preceq q b = true := by
  unfold Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith frameGradeRead at h
  dsimp only at h
  obtain ⟨b, hb, hqb⟩ := grade2Block_some h
  change clipResult st.f (cacheAtRound c r).g2 = some (some b) at hb
  exact clipResult_some hb hqb

/-- `alignRound` で回した cache の round `k` の frame は、元の cache の round `k` の frame か未完了の frame。
手書き `align_current` の一般の round の版。 -/
theorem cacheAtRound_alignRound (c : Cache) (s k : Nat) :
    cacheAtRound (alignRound c s) k = cacheAtRound c k ∨ cacheAtRound (alignRound c s) k = pendingFrame := by
  unfold alignRound
  by_cases h1 : s = c.round
  · left
    simp only [h1, beq_self_eq_true, ite_true]
  · by_cases h2 : s = c.round + 1
    · simp only [h2, beq_iff_eq, ite_true, cacheAtRound]
      by_cases hk1 : k = c.round + 1
      · left
        subst hk1
        simp
      · right
        have hk0 : ¬ k = c.round + 1 + 1 ∨ k = c.round + 1 + 1 := by omega
        rcases hk0 with hk0 | hk0 <;> simp [hk1, hk0]
    · right
      simp only [h1, h2, beq_iff_eq, ite_false, cacheAtRound]
      split_ifs <;> rfl

/-- phase tick の後の cache の round `k` の frame は、回した cache(`alignRound`)の round `k` の frame に `completeFrame` と
`clipFrame st.f` を掛けたものか、未完了の frame。 -/
theorem cacheAtRound_onPhaseTick (e : ProtocolEnv) (hc : HealConfig) (st : FGStore) (t : Int) (c : Cache) (k : Nat) :
    cacheAtRound (onPhaseTick e hc st t c) k =
        clipFrame st.f (completeFrame e hc st k t (cacheAtRound (alignRound c (roundOf hc (slotOf e t))) k)) ∨
      cacheAtRound (onPhaseTick e hc st t c) k = pendingFrame := by
  unfold onPhaseTick clipCache
  dsimp only
  generalize alignRound c (roundOf hc (slotOf e t)) = A
  unfold cacheAtRound
  dsimp only
  by_cases h1 : k = A.round
  · left
    subst h1
    simp
  · by_cases h2 : k = A.round + 1
    · left
      subst h2
      simp
    · right
      simp [h1, h2]

/-- G0 の `completeOne` は G2 の結果を変えない。 -/
theorem completeOne_G0_g2 (e : ProtocolEnv) (hc : HealConfig) (st : FGStore) (r : Nat) (t : Int) (fr : Frame) :
    (completeOne e hc st r t GradePhase.G0 fr).g2 = fr.g2 := by
  unfold completeOne
  split
  · rfl
  · split_ifs <;> rfl

/-- G1 の `completeOne` は G2 の結果を変えない。 -/
theorem completeOne_G1_g2 (e : ProtocolEnv) (hc : HealConfig) (st : FGStore) (r : Nat) (t : Int) (fr : Frame) :
    (completeOne e hc st r t GradePhase.G1 fr).g2 = fr.g2 := by
  unfold completeOne
  split
  · rfl
  · split_ifs <;> rfl

/-- `completeFrame` の G2 の結果は G2 の `completeOne` の結果(G0 / G1 の段は G2 の欄を変えない)。手書き
`complete_one_other` / `complete_frame_g2` に当たる。 -/
theorem completeFrame_g2 (e : ProtocolEnv) (hc : HealConfig) (st : FGStore) (r : Nat) (t : Int) (fr : Frame) :
    (completeFrame e hc st r t fr).g2 = (completeOne e hc st r t GradePhase.G2 fr).g2 := by
  unfold completeFrame
  rw [completeOne_G0_g2, completeOne_G1_g2]

/-- G2 の `completeOne` の後の G2 の結果が `some (some b)` なら、元の結果がそれか、tick の時刻が G2 の domain 時刻で
`freezeRoot` が `b` を返した。 -/
theorem completeOne_g2_some {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {t : Int} {fr : Frame}
    {b : Block} (h : (completeOne e hc st r t GradePhase.G2 fr).g2 = some (some b)) :
    fr.g2 = some (some b) ∨
      (t = domainTime e hc r GradePhase.G2 ∧
        freezeRoot e (gradeView st) st.f hc.etaSG r (earlyTime e hc r GradePhase.G2) (lateTime e hc r GradePhase.G2) =
          some b) := by
  unfold completeOne at h
  split at h
  · exact Or.inl h
  · split_ifs at h with ht
    · simp only [putPhase, Option.some.injEq] at h
      exact Or.inr ⟨by simpa only [beq_iff_eq] using ht, h⟩
    · exact Or.inl h

/-- **phase tick の G2 の結果の出どころ**: phase tick の後の cache の round `k` の G2 の結果が `some (some b)` なら、
`b ⪯ b0` の `b0` があり、tick の前の cache の round `k` の G2 の結果が `some (some b0)` か、tick の時刻が round `k` の
G2 の domain 時刻で、この tick の store で `freezeRoot` が `b0` を凍結した。 -/
theorem onPhaseTick_g2_cases {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {t : Int} {c : Cache} {k : Nat}
    {b : Block} (h : (cacheAtRound (onPhaseTick e hc st t c) k).g2 = some (some b)) :
    ∃ b0, preceq b b0 = true ∧
      ((cacheAtRound c k).g2 = some (some b0) ∨
        (t = domainTime e hc k GradePhase.G2 ∧
          freezeRoot e (gradeView st) st.f hc.etaSG k (earlyTime e hc k GradePhase.G2) (lateTime e hc k GradePhase.G2) =
            some b0)) := by
  rcases cacheAtRound_onPhaseTick e hc st t c k with hEq | hEq <;> rw [hEq] at h
  · change clipResult st.f (completeFrame e hc st k t _).g2 = some (some b) at h
    obtain ⟨b1, hb1, hbb1⟩ := clipResult_some h (preceq_self b)
    rw [completeFrame_g2] at hb1
    rcases completeOne_g2_some hb1 with hold | hfz
    · rcases cacheAtRound_alignRound c (roundOf hc (slotOf e t)) k with hA | hA <;> rw [hA] at hold
      · exact ⟨b1, hbb1, Or.inl hold⟩
      · simp [pendingFrame] at hold
    · exact ⟨b1, hbb1, Or.inr hfz⟩
  · simp [pendingFrame] at h

/-- **phase tick の後の cache の grade 2 の候補**: `grade2BlockWith (onPhaseTick e hc st t c) e hc st' k = some q` なら、
`q ⪯ b0` の `b0` があり、tick の前の cache の round `k` の G2 の結果が `some (some b0)` か、tick の時刻が round `k` の G2 の
domain 時刻でこの tick の store `st` が `b0` を凍結した(`grade2BlockWith_some` と `onPhaseTick_g2_cases`)。 -/
theorem grade2BlockWith_onPhaseTick_cases {e : ProtocolEnv} {hc : HealConfig} {st st' : FGStore} {t : Int} {c : Cache}
    {k : Nat} {q : Block}
    (h : Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith (onPhaseTick e hc st t c) e hc st' k = some q) :
    ∃ b0, preceq q b0 = true ∧
      ((cacheAtRound c k).g2 = some (some b0) ∨
        (t = domainTime e hc k GradePhase.G2 ∧
          freezeRoot e (gradeView st) st.f hc.etaSG k (earlyTime e hc k GradePhase.G2) (lateTime e hc k GradePhase.G2) =
            some b0)) := by
  obtain ⟨b, hb, hqb⟩ := grade2BlockWith_some h
  obtain ⟨b0, hbb0, hcases⟩ := onPhaseTick_g2_cases hb
  exact ⟨b0, preceq_trans hqb hbb0, hcases⟩

end Proofs.Consensus.Grade2Capture
