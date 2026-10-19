import Proofs.Consensus.SgFrom
import Proofs.Consensus.RootWitness
import Proofs.Consensus.Carried
import Proofs.Consensus.Window
import Proofs.Consensus.Constants
import Proofs.Consensus.Liveness
import Proofs.Consensus.Available
import Mathlib.Tactic

/-!
# SG 票の受理の守りと honest な送り手の行の一意性(C77 の補題)

`onSgVote`(`Model/Consensus/Protocol/Handlers.lean`)は attestation `x` を、store の slot の round `r` について
`x.round < r - etaSG` か `r < x.round` なら退け、同じ round・同じ送り手の行の `confirmed` の集合 `roundVotes` が `x.confirmed` を
含むか大きさが 2 なら store を変えない。受理の窓を満たし、受理の後の行で送り手の `confirmed` が 1 通りなら、受理の後の行に送り手と
`confirmed` が `x` と同じ attestation がある(`mem_rows_onSgVote`。行の畳み込み `admitRows` の版は `admitRows_mem`)。

run では、honest な送り手の行の `confirmed` はどのノードの store でも 1 通り(`honest_rows_confirmed_eq`): 行の attestation は送り手が
出した行の消去(`SgFrom.sg_genuine`)で、行の時刻は round の action 時刻に決まり、同じ時刻の tick の行は 1 つ(`emits_attest_unique`)。
これで、honest な行を honest な読み手が扱った後の行に、送り手と `confirmed` の一致する attestation があることが閉じる
(`AvailableHoles.honestActionRow_handled_row`)。手書き `NamedSGArrival.honest_row_after_call`(`Protocol/Handlers/SGArrival.lean`)の
守りを通す段に当たる(周回 263)。
-/

namespace Proofs.Consensus.SgAdmit

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers
open Model.Consensus.Protocol.Grades Model.Consensus.Protocol.Duties.Proposals
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Sets Proofs.Consensus.Orders
open Proofs.Consensus.SgStamps (rows rows_insert)

/-- **受理の守りを通る SG 票は行に残る**: `onSgVote` の受理の窓(store の slot の round `r` について `r - etaSG ≤ x.round ≤ r`)を
満たし、受理の後の鍵 `x.round` の行で送り手 `x.valIndex` の attestation の `confirmed` がどれも `x.confirmed` なら、受理の後の行に
送り手と `confirmed` が `x` と同じ attestation がある。守りが退けるのは、同じ `confirmed` が既にある(それが求めるもの)か、
`roundVotes` の大きさが 2(一意性の下では `roundVotes` の要素はどれも `x.confirmed` なので、それを含まなければ空)のとき。 -/
theorem mem_rows_onSgVote (hc : HealConfig) (st : Store) (x : CombinedAttestation)
    (hlo : roundOf hc st.s - hc.etaSG ≤ x.round) (hhi : x.round ≤ roundOf hc st.s)
    (huniq : ∀ y ∈ rows (onSgVote hc st x) x.round, y.valIndex = x.valIndex → y.confirmed = x.confirmed) :
    ∃ y ∈ rows (onSgVote hc st x) x.round, y.valIndex = x.valIndex ∧ y.confirmed = x.confirmed := by
  have hcont : (roundVotes st x).contains x.confirmed = true →
      ∃ y ∈ rows st x.round, y.valIndex = x.valIndex ∧ y.confirmed = x.confirmed := fun h => by
    have hm := (contains_iff_mem (opt_compare_eq_iff bid_compare_eq_iff) _ _).mp h
    unfold roundVotes NaruStd.Set.map at hm
    obtain ⟨y, hy, hyc⟩ := List.mem_map.mp ((mem_of_iff (opt_compare_eq_iff bid_compare_eq_iff) _ _).mp hm)
    obtain ⟨hyp, hyv⟩ := List.mem_filter.mp hy
    unfold sgPool at hyp
    exact ⟨y, (mem_toSet_iff ca_compare_eq_iff _ _).mp hyp, beq_iff_eq.mp hyv, hyc⟩
  revert huniq
  unfold onSgVote
  dsimp only
  split_ifs with hg
  · intro huniq
    have h1 : decide (x.round < roundOf hc st.s - hc.etaSG) = false := decide_eq_false (by omega)
    have h2 : decide (roundOf hc st.s < x.round) = false := decide_eq_false (by omega)
    rw [h1, h2, Bool.false_or, Bool.false_or, Bool.or_eq_true] at hg
    by_cases hc' : (roundVotes st x).contains x.confirmed = true
    · exact hcont hc'
    · exfalso
      have hsize := hg.resolve_left hc'
      have hnil : (roundVotes st x).elems = [] := by
        rcases hl : (roundVotes st x).elems with _ | ⟨z, l⟩
        · rfl
        · exfalso
          have hz : z ∈ (roundVotes st x).elems := by rw [hl]; exact List.mem_cons_self ..
          apply hc'
          have hz' := hz
          unfold roundVotes NaruStd.Set.map at hz'
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ((mem_of_iff (opt_compare_eq_iff bid_compare_eq_iff) _ _).mp hz')
          obtain ⟨hyp, hyv⟩ := List.mem_filter.mp hy
          unfold sgPool at hyp
          have he := huniq y ((mem_toSet_iff ca_compare_eq_iff _ _).mp hyp) (beq_iff_eq.mp hyv)
          rw [← he]
          exact (contains_iff_mem (opt_compare_eq_iff bid_compare_eq_iff) _ _).mpr hz
      have h0 : (roundVotes st x).size = 0 := by unfold NaruStd.Set.size; rw [hnil]; rfl
      rw [h0] at hsize
      exact absurd hsize (by decide)
  · intro _
    refine ⟨x, ?_, rfl, rfl⟩
    change x ∈ NaruStd.Table.getOr (st.sgVotes.insert x.round _) x.round []
    rw [rows_insert]
    split_ifs with h
    · exact List.mem_append_right _ (List.mem_singleton_self x)
    · exact absurd rfl h

/-- `admitRow` の後の `core` は `onSgVote` の結果(名前付きの行 `sgRows` に足すかどうかに依らない)。 -/
theorem admitRow_core (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) :
    (admitRow hc st row).core = onSgVote hc st.core (eraseAttestation row) := by
  unfold admitRow
  dsimp only
  split_ifs <;> rfl

/-- 自分の行 `attestWith` の後の `core` は、その行の消去の `onSgVote` の結果。 -/
theorem attestWith_core (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    (attestWith cache e hc nd st rec).1.core =
      onSgVote hc st.core (eraseAttestation (attestWith cache e hc nd st rec).2.2) := by
  unfold attestWith
  exact admitRow_core hc st _

/-- **畳み込みの受理**: 行のリスト `L` の要素 `row` について、畳み込みの前の store が行の不変条件と受理の窓を満たし、
畳み込みの後の行で送り手 `row.valIndex` の attestation の `confirmed` がどれも `row.confirmed` なら、畳み込みの後の行に送り手と
`confirmed` が `row` と同じ attestation がある。途中の store の時計は元のまま(`SgStamps.admitRow_step` の `clock`)、`row` を
受理した後の行は残りの畳み込みで残る(`SgStamps.admitRows_step` の `keep`)。 -/
theorem admitRows_mem (hc : HealConfig) {row : NamedAttestation} :
    ∀ (L : List NamedAttestation) (st : NamedStore), row ∈ L → Proofs.Consensus.SgStamps.SgInv st.core →
      roundOf hc st.core.s - hc.etaSG ≤ row.round → row.round ≤ roundOf hc st.core.s →
      (∀ y ∈ rows (admitRows hc st L).core row.round, y.valIndex = row.valIndex → y.confirmed = row.confirmed) →
      ∃ y ∈ rows (admitRows hc st L).core row.round, y.valIndex = row.valIndex ∧ y.confirmed = row.confirmed
  | [], _, hm, _, _, _, _ => absurd hm List.not_mem_nil
  | r :: L, st, hm, hinv, hlo, hhi, huniq => by
    have hfold : admitRows hc st (r :: L) = admitRows hc (admitRow hc st r) L := by
      unfold admitRows
      rw [List.foldl_cons]
    rw [hfold] at huniq ⊢
    have hstep := Proofs.Consensus.SgStamps.admitRow_step hc st r
    have hrest := Proofs.Consensus.SgStamps.admitRows_step hc L (admitRow hc st r)
    rcases List.mem_cons.mp hm with rfl | hm
    · have hkeep := hrest.keep (hstep.inv hinv)
      rw [admitRow_core] at hkeep
      obtain ⟨y, hy, hyv, hyc⟩ := mem_rows_onSgVote hc st.core (eraseAttestation row) hlo hhi
        (fun y hy hyv => huniq y (hkeep _ y hy).1 hyv)
      exact ⟨y, (hkeep _ y hy).1, hyv, hyc⟩
    · have hs : (admitRow hc st r).core.s = st.core.s := hstep.clock.s
      exact admitRows_mem hc L (admitRow hc st r) hm (hstep.inv hinv) (by rw [hs]; exact hlo) (by rw [hs]; exact hhi)
        huniq

/-- 受理で名前付きのブロックが新しく bodies に入ったなら、運ぶ行の受理は `admitRows`。 -/
theorem admitCarried_of_new (adm : CarriedAdmission) (hc : HealConfig) {before after : NamedStore} {b : NamedBlock}
    (hnew : ¬ (before.bodies.contains b = true)) (hin : after.bodies.contains b = true) :
    admitCarried adm hc before after b = admitRows hc after (namedAttestations b) := by
  unfold admitCarried
  simp [hnew, hin]

/-- 自分の行の送り手は務めのノードの `valIndex`。 -/
theorem attestWith_valIndex (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    (attestWith cache e hc nd st rec).2.2.valIndex = nd.valIndex := rfl

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- round `k` の action 時刻は slot `k · R + 1` の提案の時刻の `2Δ` 後。 -/
theorem actionTime_eq_proposalTime (k : Nat) :
    actionTime s.hc s.e.delta k =
      Model.Consensus.Protocol.Schedule.proposalTime s.e (k * s.hc.r + 1) + 2 * s.e.delta := by
  rw [Proofs.Consensus.Clocks.proposalTime_eq]
  unfold actionTime Model.Consensus.Objects.Time.slotStart openingSlot
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- **発行した行の送り手は発行したノード**(`AttestationSource.tick_attest_dutyStore`)。 -/
theorem emits_attest_valIndex {u : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho u (NamedObject.Attest row) t) : row.valIndex = u := by
  obtain ⟨j, -, hrow⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho u _ t).mp hem
  rw [Proofs.Consensus.Signing.nodeTick_out] at hrow
  obtain ⟨-, -, hr⟩ := Proofs.Consensus.AttestationSource.tick_attest_dutyStore c p a nr _ s.hc _ _ _ t hrow
  rw [hr]
  rfl

/-- **同じ時刻に同じノードが出す行は 1 つ**(重複なし): 時刻 `t` の `Tick u t` の添字は 1 つ(`EventsNodup`)で、その tick の
行は務めの store の `attestWith` の行(`AttestationSource.tick_attest_dutyStore`)。 -/
theorem emits_attest_unique (hnd : EventsNodup rho) {u : ValidatorId} {row row2 : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho u (NamedObject.Attest row) t)
    (hem2 : Emits c p a nr s rho u (NamedObject.Attest row2) t) : row2 = row := by
  obtain ⟨j, hev, hrow⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho u _ t).mp hem
  obtain ⟨j2, hev2, hrow2⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho u _ t).mp hem2
  have hil : j2 < rho.events.length := (List.getElem?_eq_some_iff.mp hev2).1
  have : j2 = j := (List.Nodup.getElem?_inj hil
    (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd)).mp (hev2.trans hev.symm)
  subst this
  rw [Proofs.Consensus.Signing.nodeTick_out] at hrow hrow2
  obtain ⟨-, -, hr⟩ := Proofs.Consensus.AttestationSource.tick_attest_dutyStore c p a nr _ s.hc _ _ _ t hrow
  obtain ⟨-, -, hr2⟩ := Proofs.Consensus.AttestationSource.tick_attest_dutyStore c p a nr _ s.hc _ _ _ t hrow2
  rw [hr, hr2]

/-- **honest な送り手の行の `confirmed` は 1 通り**: `UnforgeableSignatures` と重複なしの下で、honest な `u` が行 `row` を出したなら、
どの添字・どのノードの store の鍵 `row.round` の行でも、送り手が `u` の attestation の `confirmed` は `row.confirmed`。行の
attestation は `u` が出した行の消去(`SgFrom.sg_genuine`)で、その round は鍵(`SgStamps.stateBefore_sgInv`)なので時刻は
`row.round` の action 時刻(`RootWitness.emits_attest_actionTime_round`)、同じ時刻の行は 1 つ(`emits_attest_unique`)。手書きでは
`onSgVote` の大きさ 2 の守りを honest な送り手について外す段(`NamedSGArrival.honest_row_after_call`)に当たる。 -/
theorem honest_rows_confirmed_eq (hunf : UnforgeableSignatures c p a nr s rho) (hnd : EventsNodup rho)
    {u : ValidatorId} (hu : rho.honest.contains u = true) {t : Int} {row : NamedAttestation}
    (hem : Emits c p a nr s rho u (NamedObject.Attest row) t) {i : Nat} {w : ValidatorId} {x : CombinedAttestation}
    (hx : x ∈ rows (worldAt (stateBefore c p a nr s rho i) w).st.core row.round) (hxu : x.valIndex = u) :
    x.confirmed = row.confirmed := by
  obtain ⟨row2, t2, hrow2, hem2⟩ :=
    Proofs.Consensus.SgFrom.sg_genuine c p a nr s rho hunf hx (by rw [hxu]; exact hu)
  rw [hxu] at hem2
  have hround : row2.round = row.round := by
    rw [← Proofs.Consensus.SgStamps.stateBefore_sgInv c p a nr s rho i w _ x hx, ← hrow2]
    rfl
  have ht : t2 = t := by
    rw [Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem2,
      Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem, hround]
  subst ht
  rw [← hrow2, emits_attest_unique c p a nr s rho hnd hem hem2]
  rfl

/-- **honest な行を honest な読み手が扱った後の行**(GST-zero の枝): honest な `u` が時刻 `t` に行 `row` を出し、honest な `w` が
時刻 `t2`(`t ≤ t2 < t + Δ`)に添字 `j` でその行を扱う(`HandlesAt`)なら、`j` の event の後の `w` の store の鍵 `row.round` の
行に、送り手が `u` で `confirmed` が `row.confirmed` の attestation がある。`t` は `row.round = k` の action 時刻
(slot `k · R + 1` の提案の時刻の `2Δ` 後)で、`t2` はその slot の中にある。`HandlesAt` の 3 つの経路:
- 自分の tick が行を出す: tick の後の store は務めの store の `attestWith` の後(`AttestationSource.tick_attest_dutyStore`)で、
  務めの store の slot の round は行の round。
- 配送: 受信の直前の slot は `k · R + 1`(`Window.slot_ge_of_deliver` / `slot_le_of_deliver`)で round は `k`(`Constants.roundOf_slot`)。
- 受理したブロックが運ぶ: 配送なら運ぶ行の畳み込み(`admitRows_mem`)で、窓は配送と同じ。自分の提案は提案の時刻にだけ起き
  (`Carried.nodeTick_block_time`)、`t2` は提案の時刻ではない(`Carried.ne_proposalTime_of_vote_window`)。
どの経路でも受理の後の行は `stateBefore (j + 1)` の行の部分で、そこで送り手 `u` の `confirmed` は 1 通り(`honest_rows_confirmed_eq`)。
手書き `NamedSGArrival.honest_row_after_call`(`Protocol/Handlers/SGArrival.lean` 758 行)に当たる(周回 263)。 -/
theorem handlesAt_honestRow_mem (hwf : SetupWellFormed c p s)
    (hsleep : Statements.Consensus.Spec.Regimes.SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems)
    {t : Int} {row : NamedAttestation} (hem : Emits c p a nr s rho u (NamedObject.Attest row) t) {w : ValidatorId}
    (hw : w ∈ rho.honest.elems) {j : Nat} {t2 : Int} (ht : t ≤ t2) (ht2 : t2 < t + s.e.delta)
    (hh : HandlesAt c p a nr s rho j w (NamedObject.Attest row) t2) :
    ∃ x ∈ rows (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core row.round,
      x.valIndex = u ∧ x.confirmed = row.confirmed := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hδ := hfacts.1
  have hR : 3 ≤ s.hc.r := hfacts.2.2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  obtain ⟨-, hnd⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hu' : rho.honest.contains u = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu
  have hw' : rho.honest.contains w = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw
  have hvi : row.valIndex = u := emits_attest_valIndex c p a nr s rho hem
  have huniq : ∀ y ∈ rows (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core (eraseAttestation row).round,
      y.valIndex = (eraseAttestation row).valIndex → y.confirmed = (eraseAttestation row).confirmed :=
    fun y hy hyv => honest_rows_confirmed_eq c p a nr s rho hunf hnd hu' hem hy (hyv.trans hvi)
  have hgoal : ∀ st : Store, (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core = onSgVote s.hc st (eraseAttestation row) →
      roundOf s.hc st.s - s.hc.etaSG ≤ row.round → row.round ≤ roundOf s.hc st.s →
      ∃ x ∈ rows (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core row.round,
        x.valIndex = u ∧ x.confirmed = row.confirmed := by
    intro st hst hlo hhi
    rw [hst] at huniq ⊢
    obtain ⟨y, hy, hyv, hyc⟩ := mem_rows_onSgVote s.hc st (eraseAttestation row) hlo hhi huniq
    exact ⟨y, hy, hyv.trans hvi, hyc⟩
  obtain ⟨ev, ⟨⟨hevj, hn⟩, hte⟩, hh⟩ := hh
  rcases hh with ⟨⟨t', hevt, hco⟩ | ⟨t', hevd⟩⟩ | ⟨b, k, before, hb⟩
  · -- 自分の tick が行を出す
    cases ev with
    | Deliver v' o t'' =>
      simp only [eventNode] at hevt
      exact absurd hevt (by simp)
    | Tick v' t'' =>
      simp only [eventNode, eventTime, NamedEvent.Tick.injEq, true_and] at hn hte hevt hco
      subst hn hte hevt
      have hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v' (worldAt (stateBefore c p a nr s rho j) v') t'').2 :=
        List.contains_iff_mem.mp hco
      rw [Proofs.Consensus.Signing.nodeTick_out] at hrow
      obtain ⟨h1, -, hr⟩ := Proofs.Consensus.AttestationSource.tick_attest_dutyStore c p a nr _ s.hc _ _ _ t'' hrow
      refine hgoal _ ?_ (by rw [hr]; exact Nat.sub_le _ _) (by rw [hr]; rfl)
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hevj]
      unfold Model.Consensus.Execution.Run.worldStep
      dsimp only
      rw [Proofs.Consensus.Signing.worldAt_insert_self]
      unfold Model.Consensus.Execution.Node.nodeTick Model.Consensus.Execution.Node.profileTick
      dsimp only
      rw [h1, attestWith_core, ← hr]
  · -- 配送
    cases ev with
    | Tick v' t'' =>
      simp only [eventNode] at hevd
      exact absurd hevd (by simp)
    | Deliver v' o t'' =>
      simp only [eventNode, eventTime] at hn hte hevd
      obtain ⟨-, rfl, -⟩ := hevd
      subst hn hte
      have hk : row.round * s.hc.r + 1 = (worldAt (stateBefore c p a nr s rho j) v').st.core.s := by
        have htA := Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem
        rw [actionTime_eq_proposalTime] at htA
        refine le_antisymm (Proofs.Consensus.Window.slot_ge_of_deliver c p a nr s rho hsch hδ hw' hevj ?_)
          (Proofs.Consensus.Window.slot_le_of_deliver c p a nr s rho hsch hδ hevj ?_)
        · linarith
        · rw [Proofs.Consensus.Window.proposalTime_succ]
          linarith
      refine hgoal (worldAt (stateBefore c p a nr s rho j) v').st.core ?_ ?_ ?_
      · rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hevj]
        unfold Model.Consensus.Execution.Run.worldStep
        dsimp only
        rw [Proofs.Consensus.Signing.worldAt_insert_self]
        exact admitRow_core s.hc _ row
      · rw [← hk, Proofs.Consensus.Constants.roundOf_slot s hR]
        exact Nat.sub_le _ _
      · rw [← hk, Proofs.Consensus.Constants.roundOf_slot s hR]
  · obtain ⟨⟨⟨hbc, hnew⟩, hin⟩, hkr⟩ := hb
    have hmem : row ∈ namedAttestations b := List.mem_of_getElem? hkr
    have htA := Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem
    rw [actionTime_eq_proposalTime] at htA
    rcases hbc with ⟨t', hevd, hbef⟩ | ⟨t', ⟨hevt, hcont⟩, -⟩
    · rw [hn] at hevd
      subst hevd hbef
      simp only [eventTime] at hte
      subst hte
      have hk : row.round * s.hc.r + 1 = (worldAt (stateBefore c p a nr s rho j) w).st.core.s := by
        refine le_antisymm (Proofs.Consensus.Window.slot_ge_of_deliver c p a nr s rho hsch hδ hw' hevj ?_)
          (Proofs.Consensus.Window.slot_le_of_deliver c p a nr s rho hsch hδ hevj ?_)
        · linarith
        · rw [Proofs.Consensus.Window.proposalTime_succ]
          linarith
      have hP := Proofs.Consensus.SgStamps.processBlockCore_step c p s.e s.hc s.cfg
        (worldAt (stateBefore c p a nr s rho j) w).st b
      have hPs : (processBlockCore c p s.e s.hc s.cfg (worldAt (stateBefore c p a nr s rho j) w).st b).core.s =
          (worldAt (stateBefore c p a nr s rho j) w).st.core.s := hP.clock.s
      have hst : (worldAt (stateBefore c p a nr s rho (j + 1)) w).st =
          admitRows s.hc (postCore c p s (worldAt (stateBefore c p a nr s rho j) w).st b) (namedAttestations b) := by
        rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hevj]
        unfold Model.Consensus.Execution.Run.worldStep
        dsimp only
        rw [Proofs.Consensus.Signing.worldAt_insert_self]
        exact admitCarried_of_new CarriedAdmission.AlsoCarried s.hc hnew hin
      have huniq' := huniq
      rw [hst] at huniq' ⊢
      obtain ⟨y, hy, hyv, hyc⟩ := admitRows_mem s.hc _ _ hmem
        (hP.inv (Proofs.Consensus.SgStamps.stateBefore_sgInv c p a nr s rho j w))
        (by rw [hPs, ← hk, Proofs.Consensus.Constants.roundOf_slot s hR]; exact Nat.sub_le _ _)
        (by rw [hPs, ← hk, Proofs.Consensus.Constants.roundOf_slot s hR]) huniq'
      exact ⟨y, hy, hyv.trans hvi, hyc⟩
    · exfalso
      rw [hn] at hevt hcont
      subst hevt
      simp only [eventTime] at hte
      subst hte
      unfold Model.Consensus.Spec.Execution.tickEmits at hcont
      rw [List.contains_iff_mem] at hcont
      have hpt := Proofs.Consensus.Carried.nodeTick_block_time c p a nr s w _ t' hcont
      refine Proofs.Consensus.Carried.ne_proposalTime_of_vote_window s hδ (k := row.round * s.hc.r + 1) ?_ ?_ hpt
      · rw [Proofs.Consensus.Window.voteTime_eq]
        linarith
      · rw [Proofs.Consensus.Window.proposalTime_succ]
        linarith

end Run

end Proofs.Consensus.SgAdmit
