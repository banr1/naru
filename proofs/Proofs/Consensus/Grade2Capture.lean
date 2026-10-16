import Model.Consensus.Protocol.Duties.Inputs
import Proofs.Consensus.TreeInv
import Proofs.Consensus.Signing
import Mathlib.Tactic

/-!
# grade 2 の候補は、凍結した G2 の root の祖先(C71 の補題。1 回の phase tick の段と run の帰納)

生成 Model の grade 2 の候補 `grade2BlockWith c e hc st r`(`Duties/Inputs`)は、cache `c` の round `r` の frame を
`clipFrame st.f` で切り詰めた frame の G2 の結果 `some (some b)` を、filtered tree の `activePrefix` で `b` の祖先に写したもの。
G2 の結果は phase tick `onPhaseTick` が、tick の時刻がちょうど G2 の domain 時刻のときに `freezeRoot` で凍結し、
以後は再計算せず、切り詰め(`clipGrade`。結果は元の root の祖先)だけを受ける。ただし `alignRound` が round の飛びで
frame を未完了の frame(`pendingFrame`)に捨てることはある(捨てた frame の結果は `none` で、以後の候補にならない)。
1〜5 は 1 回の phase tick の段、6 は run の帰納。

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
6. run の帰納: `stateBefore i` の `w` の cache の round `k` の G2 の結果が `some (some b)` なら、添字 `j < i` の event
   `Tick w t`(`t` は round `k` の G2 の domain 時刻)があり、`stateBefore j` の `w` の store で `freezeRoot` が `b0` を凍結し、
   `b ⪯ b0`(`stateBefore_g2_origin`)。tick の cache は `onPhaseTick` の後に `clipCache` を掛けたもの(`nodeTick_cache`)、
   配送は `clipCache` だけ(`nodeProcess_cache`)。`clipCache` は frame ごとの `clipFrame`(`cacheAtRound_clipCache`)。
   初期の cache の G2 の結果は round 0 で `some none`、他の round で `none` なので `some (some b)` にならない
   (`initialCache_g2_ne`)。

手書きでは `JointHistoryProducers.lean` の `clip_preceq` / `clip_result_prefix` / `align_current` /
`complete_one_other` / `complete_frame_g2` と、`q2_capture_at_action_read` の本体の前半に当たる。手書きは action の読みの
cache(`preparedCache`)を直接扱い、凍結の出どころを run の帰納(`NamedCacheProvenance.completed_phase_origin`)で返す。
6 はその naru 版(周回 189)。手書きは凍結した root と結果の等式(`root = (freezeRoot …).map (clipGrade · F)`)を返すが、
ここは祖先の関係 `b ⪯ b0` に弱めた(grade 2 の候補を凍結した root の祖先に繋ぐにはこれで足りる)。
手書きの初期の枝 `r = 0 ∧ root = none` は、結果を `some (some b)` に限ったので現れない。
-/

namespace Proofs.Consensus.Grade2Capture

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Parameters Model.Consensus.Objects.Identifiers
open Model.Consensus.Protocol.Grades Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.Store
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
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
手書き `align_current` を弱めた版(手書きは目標の round で等式を出す。ここは任意の round で 2 択)。 -/
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

/-! ## run の帰納(周回 189) -/

/-- `clipCache f c` の round `k` の frame は、`c` の round `k` の frame を `clipFrame f` で切り詰めたもの
(未完了の frame の切り詰めは未完了の frame)。 -/
theorem cacheAtRound_clipCache (f : Block) (c : Cache) (k : Nat) :
    cacheAtRound (clipCache f c) k = clipFrame f (cacheAtRound c k) := by
  unfold clipCache cacheAtRound
  dsimp only
  split_ifs <;> rfl

/-- `clipCache f c` の round `k` の G2 の結果が `some (some b)` なら、`c` の round `k` の G2 の結果は `some (some b0)` で `b ⪯ b0`。 -/
theorem clipCache_g2_some {f : Block} {c : Cache} {k : Nat} {b : Block}
    (h : (cacheAtRound (clipCache f c) k).g2 = some (some b)) :
    ∃ b0, (cacheAtRound c k).g2 = some (some b0) ∧ preceq b b0 = true := by
  rw [cacheAtRound_clipCache] at h
  exact clipResult_some h (preceq_self b)

/-- 初期の cache の G2 の結果は `some (some b)` にならない(round 0 は `some none`、他の round は `none`)。 -/
theorem initialCache_g2_ne (k : Nat) (b : Block) : (cacheAtRound initialCache k).g2 ≠ some (some b) := by
  unfold initialCache cacheAtRound
  dsimp only
  split_ifs <;> simp [emptyFrame, pendingFrame]

/-- ノードの tick の後の cache は、tick の前の store で `onPhaseTick` を掛けた cache に `clipCache` を掛けたもの。 -/
theorem nodeTick_cache (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) :
    ∃ f, (nodeTick c p a nr s v n t).1.cache = clipCache f (onPhaseTick s.e s.hc (storeToHealing n.st.core) t n.cache) :=
  ⟨_, rfl⟩

/-- 配送の処理の後の cache は、処理の前の cache に `clipCache` を掛けたもの。 -/
theorem nodeProcess_cache (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : NamedObject) :
    ∃ f, (nodeProcess c p s n o).cache = clipCache f n.cache :=
  ⟨_, rfl⟩

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **完了した G2 の結果の出どころ**(前提なし): `stateBefore i` の `w` の cache の round `k` の G2 の結果が `some (some b)` なら、
添字 `j < i` の event `Tick w t` があり、`t` は round `k` の G2 の domain 時刻で、`stateBefore j` の `w` の store で `freezeRoot` が
`b0` を凍結し、`b ⪯ b0`。添字 `i` の帰納法で、tick は `onPhaseTick_g2_cases`(この tick の凍結か、tick の前の結果)、配送と
他のノードの event は tick の前の結果に戻す。手書き `NamedCacheProvenance.completed_phase_origin` の、結果を祖先の関係に
弱めた版(周回 189)。 -/
theorem stateBefore_g2_origin (i : Nat) (w : ValidatorId) (k : Nat) {b : Block}
    (h : (cacheAtRound (worldAt (stateBefore c p a nr s rho i) w).cache k).g2 = some (some b)) :
    ∃ (j : Nat) (t : Int) (b0 : Block), j < i ∧ rho.events[j]? = some (NamedEvent.Tick w t) ∧
      t = domainTime s.e s.hc k GradePhase.G2 ∧
      freezeRoot s.e (gradeView (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
          (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG k
          (earlyTime s.e s.hc k GradePhase.G2) (lateTime s.e s.hc k GradePhase.G2) = some b0 ∧
      preceq b b0 = true := by
  induction i generalizing b with
  | zero => exact absurd h (initialCache_g2_ne k b)
  | succ i ih =>
    have carry : ∀ {b1 : Block}, preceq b b1 = true →
        (cacheAtRound (worldAt (stateBefore c p a nr s rho i) w).cache k).g2 = some (some b1) →
        ∃ (j : Nat) (t : Int) (b0 : Block), j < i + 1 ∧ rho.events[j]? = some (NamedEvent.Tick w t) ∧
          t = domainTime s.e s.hc k GradePhase.G2 ∧
          freezeRoot s.e (gradeView (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
              (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG k
              (earlyTime s.e s.hc k GradePhase.G2) (lateTime s.e s.hc k GradePhase.G2) = some b0 ∧
          preceq b b0 = true := by
      intro b1 hbb1 h1
      obtain ⟨j, t, b0, hj, he, ht, hfz, hb10⟩ := ih h1
      exact ⟨j, t, b0, Nat.lt_succ_of_lt hj, he, ht, hfz, preceq_trans hbb1 hb10⟩
    cases hev : rho.events[i]? with
    | none =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_none c p a nr s rho hev] at h
      exact carry (preceq_self b) h
    | some ev =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at h
      cases ev with
      | Tick u t =>
        unfold worldStep at h
        dsimp only at h
        rcases Proofs.Consensus.Runs.worldAt_insert (stateBefore c p a nr s rho i) u
            (nodeTick c p a nr s u (worldAt (stateBefore c p a nr s rho i) u) t).1 w with ⟨rfl, hw⟩ | hw
        · rw [hw] at h
          obtain ⟨f, hf⟩ := nodeTick_cache c p a nr s u (worldAt (stateBefore c p a nr s rho i) u) t
          rw [hf] at h
          obtain ⟨b1, hb1, hbb1⟩ := clipCache_g2_some h
          obtain ⟨b0, hb10, hold | ⟨ht, hfz⟩⟩ := onPhaseTick_g2_cases hb1
          · exact carry (preceq_trans hbb1 hb10) hold
          · exact ⟨i, t, b0, Nat.lt_succ_self i, hev, ht, hfz, preceq_trans hbb1 hb10⟩
        · rw [hw] at h
          exact carry (preceq_self b) h
      | Deliver u o t =>
        unfold worldStep at h
        dsimp only at h
        rcases Proofs.Consensus.Runs.worldAt_insert (stateBefore c p a nr s rho i) u
            (nodeProcess c p s (worldAt (stateBefore c p a nr s rho i) u) o) w with ⟨rfl, hw⟩ | hw
        · rw [hw] at h
          obtain ⟨f, hf⟩ := nodeProcess_cache c p s (worldAt (stateBefore c p a nr s rho i) u) o
          rw [hf] at h
          obtain ⟨b1, hb1, hbb1⟩ := clipCache_g2_some h
          exact carry hbb1 hb1
        · rw [hw] at h
          exact carry (preceq_self b) h

end Run

end Proofs.Consensus.Grade2Capture
