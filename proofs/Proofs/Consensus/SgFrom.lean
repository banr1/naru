import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.SgStamps
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# SG 票の行の由来と honest な送り手の票の真正性(C77 の補題)

store の SG 票の表 `sgVotes` に attestation を足すのは `onSgVote` の受理の分岐だけで(`SgStamps.lean`)、`onSgVote` を呼ぶのは
`admitRow`(行 `row` の消去 `eraseAttestation row` を入れる)だけ。`admitRow` へ来る行は 3 通りしかない: 配送された行
(`receiptProcess` の行の腕)、受理したブロックが運ぶ行(`admitCarried` の `namedAttestations`)、自分の tick の出力(提案したブロックが
運ぶ行と自分の行 `attestWith`)。したがって run のどの添字の SG 票の行の attestation も、そのノードが処理した(`Processes`)行か、
処理したブロックが運ぶ行の消去である(`sg_from`)。`UnforgeableSignatures` の 2 つの連言と合わせると、行の honest な送り手の
attestation はその送り手が実際に出した行の消去(`sg_genuine`)。

`PoolFrom.lean`(goldfish vote の pool の由来)と同じ運びで tick → node → run の順に積み上げる。手書き
`NamedOutageClosure.honest_rawInput_is_own_round_vote`(`Protocol/Grades/RoundVoterTransport.lean`)の、生の入力を送り手の発行した行に戻す半分に当たる(周回 258)。
-/

namespace Proofs.Consensus.SgFrom

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Signing Proofs.Consensus.Carrier
open Proofs.Consensus.SgStamps (rows rows_insert)

/-! ## 由来の関係 -/

/-- `b` の行の attestation は、`a` の同じ行にあったか、性質 `S` を満たす。 -/
def From (S : CombinedAttestation → Prop) (a b : Store) : Prop :=
  ∀ k x, x ∈ rows b k → x ∈ rows a k ∨ S x

theorem From.refl (S : CombinedAttestation → Prop) (a : Store) : From S a a := fun _ _ h => Or.inl h

theorem From.trans {S : CombinedAttestation → Prop} {a b d : Store} (h1 : From S a b) (h2 : From S b d) :
    From S a d := fun k x hx => by
  rcases h2 k x hx with hx | hx
  · exact h1 k x hx
  · exact Or.inr hx

theorem From.mono {S T : CombinedAttestation → Prop} (hST : ∀ x, S x → T x) {a b : Store} (h : From S a b) :
    From T a b := fun k x hx => (h k x hx).imp_right (hST x)

/-- SG 票の表が等しい store の間は、どの性質についても由来の関係。 -/
theorem From.of_eq {S : CombinedAttestation → Prop} {a b : Store} (h : b.sgVotes = a.sgVotes) : From S a b :=
  fun k x hx => Or.inl (by unfold rows at hx ⊢; rw [← h]; exact hx)

/-! ## `Store` のハンドラ -/

theorem onSgVote_from (hc : HealConfig) (st : Store) (a : CombinedAttestation) :
    From (· = a) st (onSgVote hc st a) := by
  unfold onSgVote
  dsimp only
  split_ifs
  · exact From.refl _ st
  · intro k x hx
    change x ∈ NaruStd.Table.getOr (st.sgVotes.insert a.round _) k [] at hx
    rw [rows_insert] at hx
    split_ifs at hx with hk
    · subst hk
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (List.mem_singleton.mp hx)
    · exact Or.inl hx

theorem onGoldfishVoteChecked_sgVotes (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    (onGoldfishVoteChecked c st u).sgVotes = st.sgVotes := by
  unfold onGoldfishVoteChecked onGoldfishVote
  split_ifs <;> rfl

theorem foldl_onGoldfishVoteChecked_sgVotes (c : Nat → NaruStd.Set ValidatorId) :
    ∀ (l : List GoldfishVote) (st : Store),
      (List.foldl (fun acc u => onGoldfishVoteChecked c acc u) st l).sgVotes = st.sgVotes
  | [], _ => rfl
  | u :: l, st => by
    rw [List.foldl_cons, foldl_onGoldfishVoteChecked_sgVotes c l, onGoldfishVoteChecked_sgVotes]

theorem acceptBody_sgVotes (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    (acceptBody c st b post).sgVotes = st.sgVotes := by
  have hu : (unpackedOf c st b post).sgVotes = st.sgVotes := by
    unfold unpackedOf
    rw [foldl_onGoldfishVoteChecked_sgVotes]
    rfl
  unfold acceptBody updateFinality
  dsimp only
  split_ifs <;> exact hu

theorem onBlockUsing_sgVotes (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : (onBlockUsing c p st b build).sgVotes = st.sgVotes := by
  rcases onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h]
  · rw [h]; exact acceptBody_sgVotes c st b _

theorem goldfishVoteWith_sgVotes (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : Store) :
    (goldfishVoteWith c cache e hc nd st).1.sgVotes = st.sgVotes := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_sgVotes c st _
  · rfl

/-! ## `NamedStore` のハンドラ -/

theorem processBlockCore_sgVotes (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    (processBlockCore c p e hc cfg st b).core.sgVotes = st.core.sgVotes := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · rfl
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    rcases onBlockCheckedUsing_eq (fun cur => onBlockUsing c p cur (eraseBlock b) _) hc st.core (eraseBlock b) with h | h
    · rw [h]; exact onBlockUsing_sgVotes c p _ _ _
    · rw [h]

theorem admitRow_from (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) :
    From (· = eraseAttestation row) st.core (admitRow hc st row).core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_from hc st.core _

theorem admitRows_from (hc : HealConfig) :
    ∀ (rws : List NamedAttestation) (st : NamedStore),
      From (fun x => ∃ row ∈ rws, eraseAttestation row = x) st.core (admitRows hc st rws).core
  | [], _ => From.refl _ _
  | row :: rws, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_from hc rws (admitRow hc st row)
    unfold admitRows at ih
    refine From.trans ((admitRow_from hc st row).mono ?_) (ih.mono ?_)
    · rintro x rfl
      exact ⟨row, List.mem_cons_self .., rfl⟩
    · rintro x ⟨r, hr, rfl⟩
      exact ⟨r, List.mem_cons_of_mem _ hr, rfl⟩

theorem admitCarried_from (adm : CarriedAdmission) (hc : HealConfig) (before after : NamedStore) (b : NamedBlock) :
    From (fun x => ∃ row ∈ namedAttestations b, eraseAttestation row = x) after.core
      (admitCarried adm hc before after b).core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_from hc _ after
  · exact From.refl _ _

/-- 名前付きブロック `B` の処理の後の行の attestation は、元からあるか `B` が運ぶ行の消去。 -/
theorem onBlockWith_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    From (fun x => ∃ row ∈ namedAttestations b, eraseAttestation row = x) st.core
      (onBlockWith c p adm e hc cfg st b).core := by
  unfold onBlockWith
  exact From.trans (From.of_eq (processBlockCore_sgVotes c p e hc cfg st b)) (admitCarried_from adm hc st _ b)

/-- 受信した object の処理の後の行の attestation は、元からあるか、その行か、そのブロックが運ぶ行の消去。 -/
theorem receiptProcess_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (o : NamedObject) :
    From (fun x => ∃ row, (o = NamedObject.Attest row ∨ ∃ B, o = NamedObject.Block B ∧ row ∈ namedAttestations B) ∧
      eraseAttestation row = x) st.core (receiptProcess c p s st o).core := by
  cases o with
  | Block b =>
    refine (onBlockWith_from c p CarriedAdmission.AlsoCarried s.e s.hc s.cfg st b).mono ?_
    rintro x ⟨row, hrow, rfl⟩
    exact ⟨row, Or.inr ⟨b, rfl, hrow⟩, rfl⟩
  | GfVote u =>
    exact From.of_eq (onGoldfishVoteChecked_sgVotes c st.core u)
  | Attest row =>
    refine (admitRow_from s.hc st row).mono ?_
    rintro x rfl
    exact ⟨row, Or.inl rfl, rfl⟩

/-! ## tick の務め -/

/-- tick の出力 `out` が由来になる性質: `out` の行か、`out` のブロックが運ぶ行の消去。 -/
def OutRow (out : List NamedObject) (x : CombinedAttestation) : Prop :=
  ∃ row, (NamedObject.Attest row ∈ out ∨ ∃ B, NamedObject.Block B ∈ out ∧ row ∈ namedAttestations B) ∧
    eraseAttestation row = x

theorem proposeBlockWith_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) :
    From (fun x => ∃ B, (proposeBlockWith c p nr cache e hc cfg nd st).2 = some B ∧
      ∃ row ∈ namedAttestations B, eraseAttestation row = x) st.core (proposeBlockWith c p nr cache e hc cfg nd st).1.core := by
  unfold proposeBlockWith
  cases hm : proposalWith nr cache ProposalRowSource.PoolAndCarried e hc nd st with
  | none => exact From.refl _ _
  | some b =>
    refine (onBlockWith_from c p CarriedAdmission.AlsoCarried e hc cfg st b).mono ?_
    intro x hx
    exact ⟨b, rfl, hx⟩

theorem namedGoldfishVoteWith_sgVotes (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv)
    (hc : HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) :
    (namedGoldfishVoteWith c cache e hc nd st).1.core.sgVotes = st.core.sgVotes := by
  have h1 : (namedGoldfishVoteWith c cache e hc nd st).1.core = (goldfishVoteWith c cache e hc nd st.core).1 := by
    unfold namedGoldfishVoteWith; rfl
  rw [h1]
  exact goldfishVoteWith_sgVotes c cache e hc nd st.core

theorem attestWith_from (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    From (· = eraseAttestation (attestWith cache e hc nd st rec).2.2) st.core (attestWith cache e hc nd st rec).1.core := by
  unfold attestWith
  exact admitRow_from hc st _

/-- `NamedStore` の間の由来(`core` の `From`)を、tick の 16 経路を入れ子の形で閉じるための 1 段ずつの形。 -/
theorem proposeBlockWith_from' (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {S : CombinedAttestation → Prop} {s0 st : NamedStore}
    (h : From S s0.core st.core)
    (hS : ∀ B, (proposeBlockWith c p nr cache e hc cfg nd st).2 = some B →
      ∀ row ∈ namedAttestations B, S (eraseAttestation row)) :
    From S s0.core (proposeBlockWith c p nr cache e hc cfg nd st).1.core := by
  refine From.trans h ((proposeBlockWith_from c p nr cache e hc cfg nd st).mono ?_)
  rintro x ⟨B, hB, row, hrow, rfl⟩
  exact hS B hB row hrow

theorem namedGoldfishVoteWith_from' (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv)
    (hc : HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) {S : CombinedAttestation → Prop}
    {s0 st : NamedStore} (h : From S s0.core st.core) :
    From S s0.core (namedGoldfishVoteWith c cache e hc nd st).1.core :=
  From.trans h (From.of_eq (namedGoldfishVoteWith_sgVotes c cache e hc nd st))

theorem namedUpdateConfirmationWith_from' (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    {S : CombinedAttestation → Prop} {s0 st : NamedStore} (h : From S s0.core st.core) (k : Nat) :
    From S s0.core (namedUpdateConfirmationWith cache e hc st k).core :=
  From.trans h (From.of_eq rfl)

theorem attestWith_from' (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {S : CombinedAttestation → Prop} {s0 st : NamedStore}
    (h : From S s0.core st.core) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord)
    (hS : S (eraseAttestation (attestWith cache e hc nd st rec).2.2)) :
    From S s0.core (attestWith cache e hc nd st rec).1.core := by
  refine From.trans h ((attestWith_from cache e hc nd st rec).mono ?_)
  rintro x rfl
  exact hS

/-- 1 tick の後の行の attestation は、元からあるか、その tick が出力した行か、その tick が出力したブロックが運ぶ行の消去。 -/
theorem tick_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    From (OutRow (tick c p a nr cache e hc cfg nd st rec t).2.2) st.core (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  have h0 : ∀ S, From S st.core ({ st with core := { st.core with t := t, s := slotOf e t } } : NamedStore).core :=
    fun _ => From.of_eq rfl
  unfold tick
  dsimp only
  split_ifs
  all_goals dsimp only
  all_goals first
    | (with_reducible refine attestWith_from' cache e hc nd (namedUpdateConfirmationWith_from' cache e hc (namedGoldfishVoteWith_from' c cache e hc nd (proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_)) _) rec ?_
       · intro B hB row hrow
         exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩
       · exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine attestWith_from' cache e hc nd (namedUpdateConfirmationWith_from' cache e hc (namedGoldfishVoteWith_from' c cache e hc nd (h0 _)) _) rec ?_
       exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine attestWith_from' cache e hc nd (namedUpdateConfirmationWith_from' cache e hc (proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_) _) rec ?_
       · intro B hB row hrow
         exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩
       · exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine attestWith_from' cache e hc nd (namedUpdateConfirmationWith_from' cache e hc (h0 _) _) rec ?_
       exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine attestWith_from' cache e hc nd (namedGoldfishVoteWith_from' c cache e hc nd (proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_)) rec ?_
       · intro B hB row hrow
         exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩
       · exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine attestWith_from' cache e hc nd (namedGoldfishVoteWith_from' c cache e hc nd (h0 _)) rec ?_
       exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine attestWith_from' cache e hc nd (proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_) rec ?_
       · intro B hB row hrow
         exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩
       · exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine attestWith_from' cache e hc nd (h0 _) rec ?_
       exact ⟨_, Or.inl (by simp), rfl⟩)
    | (with_reducible refine namedUpdateConfirmationWith_from' cache e hc (namedGoldfishVoteWith_from' c cache e hc nd (proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_)) _
       intro B hB row hrow
       exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩)
    | with_reducible exact namedUpdateConfirmationWith_from' cache e hc (namedGoldfishVoteWith_from' c cache e hc nd (h0 _)) _
    | (with_reducible refine namedUpdateConfirmationWith_from' cache e hc (proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_) _
       intro B hB row hrow
       exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩)
    | with_reducible exact namedUpdateConfirmationWith_from' cache e hc (h0 _) _
    | (with_reducible refine namedGoldfishVoteWith_from' c cache e hc nd (proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_)
       intro B hB row hrow
       exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩)
    | with_reducible exact namedGoldfishVoteWith_from' c cache e hc nd (h0 _)
    | (with_reducible refine proposeBlockWith_from' c p nr cache e hc cfg nd (h0 _) ?_
       intro B hB row hrow
       exact ⟨row, Or.inr ⟨B, by simp [hB], hrow⟩, rfl⟩)
    | with_reducible exact h0 _

theorem nodeTick_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) (n : NamedNodeState)
    (t : Int) : From (OutRow (nodeTick c p a nr s v n t).2) n.st.core (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_from c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **SG 票の行の由来**: `stateBefore i` のノード `u` の行の attestation は、`u` がある時刻に処理した(`Processes`)行か、
`u` がある時刻に処理したブロックが運ぶ行の消去。 -/
theorem sg_from (u : ValidatorId) :
    ∀ (i k : Nat) (x : CombinedAttestation), x ∈ rows (worldAt (stateBefore c p a nr s rho i) u).st.core k →
      ∃ row, eraseAttestation row = x ∧ ((∃ t, Processes c p a nr s rho u (NamedObject.Attest row) t) ∨
        ∃ B t, Processes c p a nr s rho u (NamedObject.Block B) t ∧ row ∈ namedAttestations B)
  | 0, k, x, hx => by
    have h : rows (worldAt worldInit u).st.core k = [] := rfl
    unfold stateBefore at hx
    simp only [List.take_zero, List.foldl_nil] at hx
    rw [h] at hx
    exact absurd hx List.not_mem_nil
  | i + 1, k, x, hx => by
    cases hev : rho.events[i]? with
    | none =>
      rw [stateBefore_succ_of_none c p a nr s rho hev] at hx
      exact sg_from u i k x hx
    | some ev =>
      rw [stateBefore_succ_of_get c p a nr s rho hev] at hx
      cases ev with
      | Tick w t =>
        unfold worldStep at hx
        dsimp only at hx
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hx
          rcases nodeTick_from c p a nr s w _ t k x hx with h | ⟨row, hrow, rfl⟩
          · exact sg_from w i k x h
          · refine ⟨row, rfl, ?_⟩
            rcases hrow with h | ⟨B, hB, hrB⟩
            · exact Or.inl ⟨t, Or.inl ((emits_iff c p a nr s rho w _ t).mpr ⟨i, hev, h⟩)⟩
            · exact Or.inr ⟨B, t, Or.inl ((emits_iff c p a nr s rho w _ t).mpr ⟨i, hev, hB⟩), hrB⟩
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hx
          exact sg_from u i k x hx
      | Deliver w o t =>
        unfold worldStep at hx
        dsimp only at hx
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hx
          rcases receiptProcess_from c p s (worldAt (stateBefore c p a nr s rho i) w).st o k x hx with
            h | ⟨row, hrow, rfl⟩
          · exact sg_from w i k x h
          · refine ⟨row, rfl, ?_⟩
            rcases hrow with rfl | ⟨B, rfl, hrB⟩
            · exact Or.inl ⟨t, Or.inr ⟨i, hev⟩⟩
            · exact Or.inr ⟨B, t, Or.inr ⟨i, hev⟩, hrB⟩
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hx
          exact sg_from u i k x hx

/-- **行の honest な送り手の attestation は真正**: `UnforgeableSignatures` の下で、どのノードの SG 票の行の attestation も、
送り手が honest ならその送り手がある時刻に実際に出した行の消去。 -/
theorem sg_genuine (hunf : UnforgeableSignatures c p a nr s rho) {u : ValidatorId} {i k : Nat} {x : CombinedAttestation}
    (hx : x ∈ rows (worldAt (stateBefore c p a nr s rho i) u).st.core k) (hh : rho.honest.contains x.valIndex = true) :
    ∃ row t, eraseAttestation row = x ∧ Emits c p a nr s rho x.valIndex (NamedObject.Attest row) t := by
  obtain ⟨row, rfl, hproc⟩ := sg_from c p a nr s rho u i k x hx
  have hauth : author (NamedObject.Attest row) = some (eraseAttestation row).valIndex := rfl
  rcases hproc with ⟨t, hproc⟩ | ⟨B, t, hproc, hrB⟩
  · obtain ⟨t2, -, hem⟩ := hunf.1 u _ t hproc _ ⟨hh, hauth⟩
    exact ⟨row, t2, rfl, hem⟩
  · obtain ⟨t2, -, hem⟩ := hunf.2 u _ t hproc _ (Proofs.Consensus.Attribution.carries_attest hrB) _ ⟨hh, hauth⟩
    exact ⟨row, t2, rfl, hem⟩

end Run

end Proofs.Consensus.SgFrom
