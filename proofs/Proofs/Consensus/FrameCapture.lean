import Proofs.Consensus.Grade2Capture
import Proofs.Consensus.Stores
import Mathlib.Tactic

/-!
# 完了した phase の結果の値(C77 の補題。`Grade2Capture` の値の版)

`Grade2Capture` は G2 の結果 `some (some b)` の出どころを、凍結した root の祖先の関係 `b ⪯ b0` に弱めて返した。ここは任意の phase
`P` について、完了した結果(空を含む)の**値そのもの**を返す: 正の round `k` の結果が `some x` なら、`x` は round `k` の phase `P` の
domain 時刻の tick の前の store で凍結した `freezeRoot` を、いまの store の finalized で切り詰めたもの。

1. 切り詰めの合成: `f1 ⪯ f2` なら `clipGrade (clipGrade g f1) f2 = clipGrade g f2`(`clipGrade_clipGrade`)。`f2` と互換なブロックは
   `f1` とも互換(`compatible_of_preceq_right`)なので、`f2` で残る最も深い祖先は `f1` の切り詰めの下にある。
2. 1 回の phase tick の段: phase tick の後の cache の round `k` の phase `P` の結果が `some x` なら、tick の前の cache の結果 `some x0` を
   tick の store の finalized で切り詰めたものか、tick の時刻が round `k` の phase `P` の domain 時刻で、その tick の store の
   `freezeRoot` を切り詰めたもの(`onPhaseTick_phase_some`)。`completeFrame` の他の phase の段はこの欄を変えない(`completeOne_other`)。
3. run の帰納: `stateBefore n` の `w` の cache の正の round `k` の phase `P` の結果が `some x` なら、添字 `j < n` の event
   `Tick w (domainTime e hc k P)` があり、`x` は `stateBefore j` の `w` の store の `freezeRoot` を `stateBefore n` の `w` の finalized で
   切り詰めたもの(`stateBefore_phase_origin`)。ノードの tick と配送の後の cache は、新しい store の finalized で `clipCache` を掛けたもの
   (`nodeTick_cache_eq` / `nodeProcess_cache_eq`)で、finalized は縮まない(`Stores.nodeTick_f` / `Stores.nodeProcess_f`)ので 1 で
   切り詰めが 1 回にまとまる。初期の cache の正の round の結果は未完了(`initialCache_phase_none`)。
4. 欄が閉じていること: phase tick は、時計の round が `R` で、tick の前の cache の round が `R` で欄が閉じているか、tick の時刻が
   round `R` の domain 時刻なら、round `R` の欄を閉じたまま返す(`onPhaseTick_closed`。`completeOne` は閉じた欄を開かない)。
   run の帰納 `stateBefore_closed`: domain の tick の後、間の自分の tick の時計の round がどれも `R` なら、cache の round は `R` で欄は
   閉じている(配送の `clipCache` も欄を保つ)。手書き `FrameCompleted` の段 1・2(`phase_domain_cache` / `slot_some_index`。周回 244)。

手書き `NamedCacheProvenance.completed_phase_before_read` と、`FrameCompleted.frame_phase_completed_of_tick_in_round` の段 3
(値の読み戻し)に当たる。手書きは node の不変条件(cache は自分の finalized で切り詰め済み)と時刻の strict read を経由するが、
ここは run の添字の帰納で値を直接運ぶ(周回 243)。
-/

namespace Proofs.Consensus.FrameCapture

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Parameters Model.Consensus.Objects.Identifiers
open Model.Consensus.Protocol.Grades Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.Store
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Blocks Proofs.Consensus.Grade2Capture

/-! ## 切り詰めの合成 -/

/-- `f1 ⪯ f2` なら、`f2` と互換なブロックは `f1` とも互換。 -/
theorem compatible_of_preceq_right {x f1 f2 : Block} (h12 : preceq f1 f2 = true) (hx : compatible x f2 = true) :
    compatible x f1 = true := by
  unfold compatible at hx
  simp only [Bool.or_eq_true] at hx
  rcases hx with h | h
  · exact compatible_of_preceq_common h h12
  · unfold compatible
    simp [preceq_trans h12 h]

/-- **切り詰めの合成**: `f1 ⪯ f2` なら `clipGrade (clipGrade g f1) f2 = clipGrade g f2`。`g` の親を遡る帰納法で、`g` が `f1` と
互換なら内側は `g` のまま、そうでなければ `g` は `f2` とも互換でない(`compatible_of_preceq_right`)ので両辺とも親に進む。 -/
theorem clipGrade_clipGrade {f1 f2 : Block} (h12 : preceq f1 f2 = true) (g : Block) :
    clipGrade (clipGrade g f1) f2 = clipGrade g f2 := by
  induction g with
  | Genesis => simp only [clipGrade]
  | Node q sl r v sup ats i ih =>
    have e1 : ∀ f, clipGrade (Block.Node q sl r v sup ats i) f =
        if compatible (Block.Node q sl r v sup ats i) f = true then Block.Node q sl r v sup ats i else clipGrade q f := by
      intro f
      rw [clipGrade, dite_eq_ite]
    rw [e1 f1]
    split_ifs with hc
    · rfl
    · rw [ih, e1 f2]
      split_ifs with hc2
      · exact absurd (compatible_of_preceq_right h12 hc2) hc
      · rfl

/-- 切り詰めの合成を `Option` の結果に持ち上げたもの。 -/
theorem map_clip_clip {f1 f2 : Block} (h12 : preceq f1 f2 = true) (o : Option Block) :
    (o.map fun b => clipGrade b f1).map (fun b => clipGrade b f2) = o.map fun b => clipGrade b f2 := by
  cases o with
  | none => rfl
  | some g => simp only [Option.map_some, clipGrade_clipGrade h12]

/-! ## 1 回の phase tick の段 -/

theorem storeToHealing_f (st : Store) : (storeToHealing st).f = st.f := rfl

theorem phaseResult_clipFrame (f : Block) (fr : Frame) (P : GradePhase) :
    phaseResult (clipFrame f fr) P = clipResult f (phaseResult fr P) := by
  cases P <;> rfl

theorem phaseResult_pendingFrame (P : GradePhase) : phaseResult pendingFrame P = none := by
  cases P <;> rfl

/-- 読みの frame の phase の結果は、cache の結果を読みの store の finalized で切り詰めたもの。 -/
theorem phaseResult_readFrame (c : Cache) (st : FGStore) (r : Nat) (P : GradePhase) :
    phaseResult (readFrame c st r) P = clipResult st.f (phaseResult (cacheAtRound c r) P) := by
  cases P <;> rfl

/-- 切り詰めた結果が `some x` なら、元の結果は `some y` で `x` は `y` の切り詰め。 -/
theorem clipResult_eq_some {f : Block} {r : Option (Option Block)} {x : Option Block} (h : clipResult f r = some x) :
    ∃ y, r = some y ∧ x = y.map fun b => clipGrade b f := by
  rcases r with _ | y
  · simp [clipResult] at h
  · simp only [clipResult, Option.map_some, Option.some.injEq] at h
    exact ⟨y, rfl, h.symm⟩

/-- phase `P` の `completeOne` は他の phase `Q` の結果を変えない。手書き `complete_one_other`。 -/
theorem completeOne_other {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {t : Int} {P Q : GradePhase}
    (fr : Frame) (h : Q ≠ P) : phaseResult (completeOne e hc st r t P fr) Q = phaseResult fr Q := by
  unfold completeOne
  split
  · rfl
  · split_ifs
    · cases P <;> cases Q <;> first | exact absurd rfl h | rfl
    · rfl

/-- phase `P` の `completeOne` の後の結果が `some x` なら、元の結果がそれか、tick の時刻が domain 時刻で `x` は `freezeRoot` の結果。 -/
theorem completeOne_self_some {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {t : Int} {P : GradePhase}
    {fr : Frame} {x : Option Block} (h : phaseResult (completeOne e hc st r t P fr) P = some x) :
    phaseResult fr P = some x ∨
      (t = domainTime e hc r P ∧
        x = freezeRoot e (gradeView st) st.f hc.etaSG r (earlyTime e hc r P) (lateTime e hc r P)) := by
  unfold completeOne at h
  split at h
  · exact Or.inl h
  · split_ifs at h with ht
    · right
      refine ⟨by simpa only [beq_iff_eq] using ht, ?_⟩
      cases P <;> simpa only [putPhase, phaseResult, Option.some.injEq, eq_comm] using h
    · exact Or.inl h

/-- `completeFrame` の後の phase `P` の結果が `some x` なら、元の結果がそれか、tick の時刻が domain 時刻で `x` は `freezeRoot` の結果
(他の phase の段は `completeOne_other` で外す)。 -/
theorem completeFrame_some {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {t : Int} {P : GradePhase}
    {fr : Frame} {x : Option Block} (h : phaseResult (completeFrame e hc st r t fr) P = some x) :
    phaseResult fr P = some x ∨
      (t = domainTime e hc r P ∧
        x = freezeRoot e (gradeView st) st.f hc.etaSG r (earlyTime e hc r P) (lateTime e hc r P)) := by
  unfold completeFrame at h
  cases P with
  | G0 =>
    rcases completeOne_self_some h with h1 | h1
    · rw [completeOne_other (P := GradePhase.G1) (Q := GradePhase.G0) _ (by decide),
        completeOne_other (P := GradePhase.G2) (Q := GradePhase.G0) _ (by decide)] at h1
      exact Or.inl h1
    · exact Or.inr h1
  | G1 =>
    rw [completeOne_other (P := GradePhase.G0) (Q := GradePhase.G1) _ (by decide)] at h
    rcases completeOne_self_some h with h1 | h1
    · rw [completeOne_other (P := GradePhase.G2) (Q := GradePhase.G1) _ (by decide)] at h1
      exact Or.inl h1
    · exact Or.inr h1
  | G2 =>
    rw [completeOne_other (P := GradePhase.G0) (Q := GradePhase.G2) _ (by decide),
      completeOne_other (P := GradePhase.G1) (Q := GradePhase.G2) _ (by decide)] at h
    exact completeOne_self_some h

/-- **phase tick の結果の値**: phase tick の後の cache の round `k` の phase `P` の結果が `some x` なら、tick の前の cache の結果
`some x0` を tick の store の finalized で切り詰めたものか、tick の時刻が round `k` の phase `P` の domain 時刻で、tick の store の
`freezeRoot` を切り詰めたもの。`Grade2Capture.onPhaseTick_g2_cases` の値の版。 -/
theorem onPhaseTick_phase_some {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {t : Int} {c : Cache} {k : Nat}
    {P : GradePhase} {x : Option Block} (h : phaseResult (cacheAtRound (onPhaseTick e hc st t c) k) P = some x) :
    (∃ x0, phaseResult (cacheAtRound c k) P = some x0 ∧ x = x0.map fun b => clipGrade b st.f) ∨
      (t = domainTime e hc k P ∧
        x = (freezeRoot e (gradeView st) st.f hc.etaSG k (earlyTime e hc k P) (lateTime e hc k P)).map
          fun b => clipGrade b st.f) := by
  rcases cacheAtRound_onPhaseTick e hc st t c k with hEq | hEq <;> rw [hEq] at h
  · rw [phaseResult_clipFrame] at h
    obtain ⟨y, hy, rfl⟩ := clipResult_eq_some h
    rcases completeFrame_some hy with hold | ⟨ht, rfl⟩
    · rcases cacheAtRound_alignRound c (roundOf hc (slotOf e t)) k with hA | hA <;> rw [hA] at hold
      · exact Or.inl ⟨y, hold, rfl⟩
      · rw [phaseResult_pendingFrame] at hold
        exact absurd hold (by simp)
    · exact Or.inr ⟨ht, rfl⟩
  · rw [phaseResult_pendingFrame] at h
    exact absurd h (by simp)

/-- 初期の cache の正の round の結果は未完了。 -/
theorem initialCache_phase_none {k : Nat} (hk : 0 < k) (P : GradePhase) :
    phaseResult (cacheAtRound initialCache k) P = none := by
  unfold initialCache cacheAtRound
  dsimp only
  split_ifs with h1
  · simp only [beq_iff_eq] at h1
    omega
  all_goals exact phaseResult_pendingFrame P

/-- ノードの tick の後の cache は、tick の前の store で `onPhaseTick` を掛けた cache を、tick の後の store の finalized で
`clipCache` したもの(`Grade2Capture.nodeTick_cache` の、finalized を名指しする版)。 -/
theorem nodeTick_cache_eq (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) :
    (nodeTick c p a nr s v n t).1.cache =
      clipCache (nodeTick c p a nr s v n t).1.st.core.f (onPhaseTick s.e s.hc (storeToHealing n.st.core) t n.cache) :=
  rfl

/-- 配送の処理の後の cache は、処理の前の cache を処理の後の store の finalized で `clipCache` したもの。 -/
theorem nodeProcess_cache_eq (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : NamedObject) :
    (nodeProcess c p s n o).cache = clipCache (nodeProcess c p s n o).st.core.f n.cache :=
  rfl

/-! ## run の帰納 -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **完了した phase の結果の値**(前提なし): `stateBefore n` の `w` の cache の正の round `k` の phase `P` の結果が `some x` なら、
添字 `j < n` の event `Tick w (domainTime e hc k P)` があり、`x` は `stateBefore j` の `w` の store の `freezeRoot` を
`stateBefore n` の `w` の finalized で切り詰めたもの。添字 `n` の帰納法で、`w` の tick は `onPhaseTick_phase_some`(この tick の凍結か、
tick の前の結果)、`w` の配送は tick の前の結果を新しい finalized で切り詰めたもの、他の event は `w` を変えない。切り詰めは
`map_clip_clip` で 1 回にまとめる。手書き `NamedCacheProvenance.completed_phase_before_read` に当たる(周回 243)。 -/
theorem stateBefore_phase_origin (n : Nat) (w : ValidatorId) {k : Nat} (hk : 0 < k) (P : GradePhase) {x : Option Block}
    (h : phaseResult (cacheAtRound (worldAt (stateBefore c p a nr s rho n) w).cache k) P = some x) :
    ∃ j : Nat, j < n ∧ rho.events[j]? = some (NamedEvent.Tick w (domainTime s.e s.hc k P)) ∧
      x = (freezeRoot s.e (gradeView (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
          (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG k
          (earlyTime s.e s.hc k P) (lateTime s.e s.hc k P)).map
        fun b => clipGrade b (worldAt (stateBefore c p a nr s rho n) w).st.core.f := by
  induction n generalizing x with
  | zero => exact absurd ((initialCache_phase_none hk P).symm.trans h) (by simp)
  | succ i ih =>
    have keep : worldAt (stateBefore c p a nr s rho (i + 1)) w = worldAt (stateBefore c p a nr s rho i) w →
        ∃ j : Nat, j < i + 1 ∧ rho.events[j]? = some (NamedEvent.Tick w (domainTime s.e s.hc k P)) ∧
          x = (freezeRoot s.e (gradeView (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
              (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG k
              (earlyTime s.e s.hc k P) (lateTime s.e s.hc k P)).map
            fun b => clipGrade b (worldAt (stateBefore c p a nr s rho (i + 1)) w).st.core.f := by
      intro hw
      rw [hw] at h ⊢
      obtain ⟨j, hj, hev, hx⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hev, hx⟩
    cases hev : rho.events[i]? with
    | none =>
      exact keep (by rw [Proofs.Consensus.Signing.stateBefore_succ_of_none c p a nr s rho hev])
    | some ev =>
      have hsucc := Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev
      cases ev with
      | Tick u t =>
        rcases Proofs.Consensus.Runs.worldAt_insert (stateBefore c p a nr s rho i) u
            (nodeTick c p a nr s u (worldAt (stateBefore c p a nr s rho i) u) t).1 w with ⟨rfl, hw⟩ | hw
        · rw [hsucc] at h ⊢
          unfold worldStep at h ⊢
          dsimp only at h ⊢
          rw [hw] at h ⊢
          have hmono := Proofs.Consensus.Stores.nodeTick_f c p a nr s u (worldAt (stateBefore c p a nr s rho i) u) t
          rw [nodeTick_cache_eq, cacheAtRound_clipCache, phaseResult_clipFrame] at h
          obtain ⟨y, hy, rfl⟩ := clipResult_eq_some h
          rcases onPhaseTick_phase_some hy with ⟨x0, hx0, rfl⟩ | ⟨ht, rfl⟩
          · obtain ⟨j, hj, hevj, rfl⟩ := ih hx0
            exact ⟨j, Nat.lt_succ_of_lt hj, hevj, by simp only [storeToHealing_f]; rw [map_clip_clip (preceq_self _), map_clip_clip hmono]⟩
          · subst ht
            exact ⟨i, Nat.lt_succ_self i, hev, by simp only [storeToHealing_f]; rw [map_clip_clip hmono]⟩
        · exact keep (by
            rw [hsucc]
            unfold worldStep
            dsimp only
            exact hw)
      | Deliver u o t =>
        rcases Proofs.Consensus.Runs.worldAt_insert (stateBefore c p a nr s rho i) u
            (nodeProcess c p s (worldAt (stateBefore c p a nr s rho i) u) o) w with ⟨rfl, hw⟩ | hw
        · rw [hsucc] at h ⊢
          unfold worldStep at h ⊢
          dsimp only at h ⊢
          rw [hw] at h ⊢
          have hmono := Proofs.Consensus.Stores.nodeProcess_f c p s (worldAt (stateBefore c p a nr s rho i) u) o
          rw [nodeProcess_cache_eq, cacheAtRound_clipCache, phaseResult_clipFrame] at h
          obtain ⟨y, hy, rfl⟩ := clipResult_eq_some h
          obtain ⟨j, hj, hevj, rfl⟩ := ih hy
          exact ⟨j, Nat.lt_succ_of_lt hj, hevj, by rw [map_clip_clip hmono]⟩
        · exact keep (by
            rw [hsucc]
            unfold worldStep
            dsimp only
            exact hw)

end Run

/-! ## 欄が閉じていること -/

/-- `completeOne` は完了した欄を未完了に戻さない。 -/
theorem completeOne_ne_none {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {t : Int} {P Q : GradePhase}
    {fr : Frame} (h : phaseResult fr Q ≠ none) : phaseResult (completeOne e hc st r t P fr) Q ≠ none := by
  by_cases hQ : Q = P
  · subst hQ
    unfold completeOne
    split
    · exact h
    · next hn => exact absurd hn h
  · rw [completeOne_other fr hQ]
    exact h

/-- phase `P` の `completeOne` の後、`P` の欄は、元から閉じていたか tick の時刻が domain 時刻なら閉じている。 -/
theorem completeOne_closed {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {t : Int} {P : GradePhase}
    {fr : Frame} (h : phaseResult fr P ≠ none ∨ t = domainTime e hc r P) :
    phaseResult (completeOne e hc st r t P fr) P ≠ none := by
  rcases h with h | ht
  · exact completeOne_ne_none h
  · unfold completeOne
    split
    · next x hx => rw [hx]; simp
    · rw [ite_eq_left (by simp [ht])]
      cases P <;> simp [putPhase, phaseResult]

/-- `completeFrame` の後、phase `P` の欄は、元から閉じていたか tick の時刻が domain 時刻なら閉じている。 -/
theorem completeFrame_closed {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {r : Nat} {t : Int} {P : GradePhase}
    {fr : Frame} (h : phaseResult fr P ≠ none ∨ t = domainTime e hc r P) :
    phaseResult (completeFrame e hc st r t fr) P ≠ none := by
  unfold completeFrame
  cases P with
  | G0 =>
    refine completeOne_closed ?_
    rcases h with h | h
    · exact Or.inl (completeOne_ne_none (completeOne_ne_none h))
    · exact Or.inr h
  | G1 => exact completeOne_ne_none (completeOne_closed (h.imp_left completeOne_ne_none))
  | G2 => exact completeOne_ne_none (completeOne_ne_none (completeOne_closed h))

theorem clipResult_ne_none {f : Block} {r : Option (Option Block)} (h : r ≠ none) : clipResult f r ≠ none := by
  rcases r with _ | y
  · exact absurd rfl h
  · simp [clipResult]

theorem alignRound_round (c : Cache) (r : Nat) : (alignRound c r).round = r := by
  unfold alignRound
  split_ifs with h1
  · simp only [beq_iff_eq] at h1
    exact h1.symm
  all_goals rfl

theorem alignRound_self {c : Cache} {r : Nat} (h : c.round = r) : alignRound c r = c := by
  unfold alignRound
  rw [ite_eq_left (by simp [h])]

theorem cacheAtRound_self {c : Cache} {r : Nat} (h : c.round = r) : cacheAtRound c r = c.current := by
  unfold cacheAtRound
  rw [ite_eq_left (by simp [h])]

/-- **phase tick は round `R` の欄を閉じる**: tick の時計の round が `R` で、tick の前の cache の round が `R` でその phase `P` の欄が
閉じているか、tick の時刻が round `R` の phase `P` の domain 時刻なら、tick の後の cache の round は `R` で、`P` の欄は閉じている。
手書き `FrameCompleted` の `phase_domain_cache`(domain の tick が欄を閉じる)と `cacheAtRound_align`(同じ round の tick は frame を残す)。 -/
theorem onPhaseTick_closed {e : ProtocolEnv} {hc : HealConfig} {st : FGStore} {t : Int} {c : Cache} {R : Nat}
    {P : GradePhase} (hR : roundOf hc (slotOf e t) = R)
    (h : (c.round = R ∧ phaseResult c.current P ≠ none) ∨ t = domainTime e hc R P) :
    (onPhaseTick e hc st t c).round = R ∧ phaseResult (onPhaseTick e hc st t c).current P ≠ none := by
  have hround : (onPhaseTick e hc st t c).round = R := by
    show (alignRound c (roundOf hc (slotOf e t))).round = R
    rw [alignRound_round, hR]
  have hcur : (onPhaseTick e hc st t c).current =
      clipFrame st.f (completeFrame e hc st R t (alignRound c (roundOf hc (slotOf e t))).current) := by
    show clipFrame st.f (completeFrame e hc st (alignRound c (roundOf hc (slotOf e t))).round t _) = _
    rw [alignRound_round, hR]
  refine ⟨hround, ?_⟩
  rw [hcur, phaseResult_clipFrame]
  refine clipResult_ne_none (completeFrame_closed ?_)
  rcases h with ⟨hc0, hc1⟩ | ht
  · left
    rw [hR, alignRound_self hc0]
    exact hc1
  · exact Or.inr ht

theorem clipCache_round (f : Block) (c : Cache) : (clipCache f c).round = c.round := rfl

theorem clipCache_current_ne_none {f : Block} {c : Cache} {P : GradePhase} (h : phaseResult c.current P ≠ none) :
    phaseResult (clipCache f c).current P ≠ none := by
  show phaseResult (clipFrame f c.current) P ≠ none
  rw [phaseResult_clipFrame]
  exact clipResult_ne_none h

section Closed

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **閉じた欄は残る**(run の帰納): 添字 `j` の event が `w` の round `R` の phase `P` の domain 時刻の tick(その時刻の時計の
round は `R`)で、`j` と `n` の間の `w` の tick の時計の round がどれも `R` なら、`stateBefore n`(`j < n`)の `w` の cache の round は
`R` で、`P` の欄は閉じている。tick は `onPhaseTick_closed`、配送は `clipCache` で欄を保ち、他のノードの event は `w` を変えない。
手書き `FrameCompleted.frame_phase_completed_of_tick_in_round` の段 1・2(`phase_domain_cache` / `slot_some_index`)に当たる(周回 244)。 -/
theorem stateBefore_closed (w : ValidatorId) {R : Nat} {P : GradePhase} {j : Nat} {τ : Int}
    (hj : rho.events[j]? = some (NamedEvent.Tick w τ)) (hτR : roundOf s.hc (slotOf s.e τ) = R)
    (hτ : τ = domainTime s.e s.hc R P)
    {n : Nat} (hjn : j < n)
    (hmid : ∀ (m : Nat) (u : Int), j < m → m < n → rho.events[m]? = some (NamedEvent.Tick w u) →
      roundOf s.hc (slotOf s.e u) = R) :
    (worldAt (stateBefore c p a nr s rho n) w).cache.round = R ∧
      phaseResult (worldAt (stateBefore c p a nr s rho n) w).cache.current P ≠ none := by
  induction n, hjn using Nat.le_induction with
  | base =>
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hj]
    unfold worldStep
    dsimp only
    rw [Proofs.Consensus.Signing.worldAt_insert_self, nodeTick_cache_eq]
    obtain ⟨h1, h2⟩ := onPhaseTick_closed (st := storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core)
      (c := (worldAt (stateBefore c p a nr s rho j) w).cache) hτR (Or.inr hτ)
    exact ⟨h1, clipCache_current_ne_none h2⟩
  | succ n hjn ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun m u hjm hmn hm => hmid m u hjm (Nat.lt_succ_of_lt hmn) hm)
    cases hev : rho.events[n]? with
    | none =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_none c p a nr s rho hev]
      exact ⟨ih1, ih2⟩
    | some ev =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev]
      cases ev with
      | Tick u t =>
        unfold worldStep
        dsimp only
        by_cases huw : u = w
        · subst huw
          rw [Proofs.Consensus.Signing.worldAt_insert_self, nodeTick_cache_eq]
          obtain ⟨h1, h2⟩ := onPhaseTick_closed (st := storeToHealing (worldAt (stateBefore c p a nr s rho n) u).st.core)
            (c := (worldAt (stateBefore c p a nr s rho n) u).cache) (P := P)
            (hmid n t hjn (Nat.lt_succ_self n) hev) (Or.inl ⟨ih1, ih2⟩)
          exact ⟨h1, clipCache_current_ne_none h2⟩
        · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ huw]
          exact ⟨ih1, ih2⟩
      | Deliver u o t =>
        unfold worldStep
        dsimp only
        by_cases huw : u = w
        · subst huw
          rw [Proofs.Consensus.Signing.worldAt_insert_self, nodeProcess_cache_eq]
          exact ⟨ih1, clipCache_current_ne_none ih2⟩
        · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ huw]
          exact ⟨ih1, ih2⟩

end Closed

end Proofs.Consensus.FrameCapture
