import Model.Consensus.Execution.Run
import Statements.Consensus.Spec.Execution
import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.Votes
import Proofs.Consensus.Clocks
import Mathlib.Tactic

/-!
# honest な投票の発行(C71 の補題)

生成 Model の tick(`Model/Consensus/Protocol/Tick.lean`)で Goldfish の投票を出すのは投票の務め `namedGoldfishVoteWith` だけで、
務めが走るのは `voting`(`0 < s` かつ `t = voteTime e s`、`s = slotOf e t`)のときだけ。務めは提案の務めの後の store
(`voteStore`: 冒頭で時計を `(t, slotOf e t)` に合わせ、提案の時刻で自分が proposer なら `proposeBlockWith` を済ませたもの)を読み、
自分が `committee' s` の要素なら投票 `{ valIndex := 自分, slot := s, head := その store の fork choice の head の root }` を
ちょうど 1 つ出す(`Votes.goldfishVoteWith_some`)。したがって:
- tick が出す投票はその tick の投票の務めの出力で、投票者は自分、slot は `slotOf e t`、時刻はその slot の `voteTime`、
  投票者は committee の要素(`tick_gfVote_shape`)。1 つの tick が出す投票は 1 つ(`tick_gfVote_unique`)。
- 逆に、`voteTime` の tick で自分が committee の要素なら、tick は必ず投票を出す(`tick_gfVote_of_duty`)。
- run では `Emits v (GfVote u) t` は上の形で(`emits_gfVote_shape`)、どの投票者も slot ごとに発行する投票は 1 つ
  (`emits_gfVote_unique`。`ScheduleWellFormed` の event の重複なしから tick の添字が 1 つ)。
- `ScheduleWellFormed` は honest なノードの公開時刻(`PublicTime`: Δ の倍数)の tick を horizon まで run に入れるので、
  honest な committee の要素は `voteTime e k ≤ horizon` の slot `k > 0` でそれぞれ投票を発行する(`honest_emits_gfVote`)。
- 投票の時刻は提案の時刻と違う(Δ > 0。`voteTime_ne_proposalTime`)ので、投票の時刻の tick では提案の分岐は走らず、`voteStore` は
  時計を合わせただけの `clocked`(`voteStore_of_voteTime`)。したがって投票の head は tick の前の store に時計を合わせたものの
  fork choice の head `voteHead`(`tick_gfVote_head`)で、run では `Emits` の添字 `i` の `stateBefore i` の発行者の store と、
  `nodeTick` が `onPhaseTick` で進めた cache で読む(`emits_gfVote_head` / `honest_emits_gfVote_head`)。
これは `Majority.lean` の `HonestSupport.vote`(honest な committee の要素はみな支持の投票を持つ)を `SleepyRegime` から出すための
最初の層(発行と head)で、残りは発行した投票と head のブロックが `supportCutoff` までに honest な全ノードの pool に届くこと
(`PartialSynchrony`)と、head が honest な提案を延ばすこと。
手書き `gfVote_emitted_shape` / `gfVote_emitted_unique` / `emits_gfVote_shape` / `emits_gfVote_unique`
(`DecoupledConsensusProofs/Protocol/Schedule/Alignment.lean`)と `slotOf_vote_time`
(`DecoupledConsensusProofs/Protocol/Handlers/TickBridges.lean`)に当たる。
-/

namespace Proofs.Consensus.Voting

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Time Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Clocks

/-! ## 投票の時刻 -/

/-- 投票の時刻はその slot を指す(Δ > 0)。手書き `slotOf_vote_time`。 -/
theorem slotOf_voteTime (e : ProtocolEnv) (hδ : 0 < e.delta) (k : Nat) : slotOf e (voteTime e k) = k := by
  unfold slotOf voteTime slotTime slotOfTime slotStart
  have hb : (0 : Int) < e.delta * 4 := by linarith
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb.le]
  have h1 : e.delta * 4 * Int.ofNat k + e.delta = e.delta + Int.ofNat k * (e.delta * 4) := by ring
  rw [h1, Int.add_mul_ediv_right _ _ hb.ne', Int.ediv_eq_zero_of_lt hδ.le (by linarith)]
  simp

/-- 投票の時刻は公開時刻(Δ の `4k + 1` 倍)。 -/
theorem publicTime_voteTime (e : ProtocolEnv) (k : Nat) : PublicTime e (voteTime e k) := by
  refine ⟨4 * k + 1, ?_⟩
  unfold voteTime slotTime slotStart
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- 投票の時刻は非負(Δ ≥ 0)。 -/
theorem voteTime_nonneg (e : ProtocolEnv) (hδ : 0 ≤ e.delta) (k : Nat) : 0 ≤ voteTime e k := by
  unfold voteTime slotTime slotStart
  have : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg k
  positivity

/-- 投票の時刻は提案の時刻と違う(Δ > 0)。手書き `vote_time_ne_proposal_time`。 -/
theorem voteTime_ne_proposalTime (e : ProtocolEnv) (hδ : 0 < e.delta) (k : Nat) : voteTime e k ≠ proposalTime e k := by
  unfold voteTime proposalTime
  intro h
  linarith

/-! ## 投票の務め -/

/-- tick の冒頭で時計を `(t, slotOf e t)` に合わせた store(tree・pool・記録は元のまま)。 -/
def clocked (e : ProtocolEnv) (st : NamedStore) (t : Int) : NamedStore :=
  { st with core := { st.core with t := t, s := slotOf e t } }

/-- store `st` の投票の務めが出す投票の head: `st.s` の voter view の fork choice の head の root(`goldfishVoteWith` と同じ式)。 -/
def voteHead (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) : BlockId :=
  root (getHeadInTreeWith cache e hc st (voterFilteredBlockTree e st st.s)
    (Model.Consensus.Protocol.ForkChoice.Views.voterView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (storeToHealing st)) st.s)
    (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (storeToHealing st)) st.s)
    (st.s - 1))

/-- `voteHead` の root を取る前のブロック(手書き `voterHeadAt` の本体と同じ式)。 -/
def voteHeadBlock (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) : Block :=
  getHeadInTreeWith cache e hc st (voterFilteredBlockTree e st st.s)
    (Model.Consensus.Protocol.ForkChoice.Views.voterView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (storeToHealing st)) st.s)
    (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (storeToHealing st)) st.s)
    (st.s - 1)

theorem voteHead_eq_root (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) :
    voteHead cache e hc st = root (voteHeadBlock cache e hc st) := rfl

/-- tick の投票の務めが読む store: 冒頭で時計を `(t, slotOf e t)` に合わせ、提案の時刻で自分が proposer なら提案の務めを済ませたもの。 -/
def voteStore (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Node) (st : NamedStore) (t : Int) : NamedStore :=
  if (decide (0 < slotOf e t) && t == proposalTime e (slotOf e t)) && (p (slotOf e t) == nd.valIndex) then
    (proposeBlockWith c p nr cache e hc cfg nd { st with core := { st.core with t := t, s := slotOf e t } }).1
  else
    { st with core := { st.core with t := t, s := slotOf e t } }

/-- 投票の務めの store の時計は `(t, slotOf e t)`(提案の務めは時計を変えない)。 -/
theorem voteStore_clockIs (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Node) (st : NamedStore) (t : Int) : ClockIs (voteStore c p nr cache e hc cfg nd st t) t (slotOf e t) := by
  have h0 : ClockIs { st with core := { st.core with t := t, s := slotOf e t } } t (slotOf e t) := ⟨rfl, rfl⟩
  unfold voteStore
  split_ifs
  · exact proposeBlockWith_clockIs c p nr cache hc nd h0
  · exact h0

theorem namedGoldfishVoteWith_out (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) (st : NamedStore) :
    (namedGoldfishVoteWith c cache e hc nd st).2 = (goldfishVoteWith c cache e hc nd st.core).2 := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  rw [hm]

/-- 自分が committee の要素なら投票の務めは投票を出す。 -/
theorem goldfishVoteWith_isSome (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) (st : Store) (hm : (c st.s).contains nd.valIndex = true) :
    ∃ u, (goldfishVoteWith c cache e hc nd st).2 = some u := by
  unfold goldfishVoteWith
  dsimp only
  simp only [hm, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem namedVote_ne_none (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) {st : NamedStore} {t : Int} {sl : Nat} (hX : ClockIs st t sl) (hm : (c sl).contains nd.valIndex = true) :
    (namedGoldfishVoteWith c cache e hc nd st).2 ≠ none := by
  rw [namedGoldfishVoteWith_out]
  rw [← hX.2] at hm
  obtain ⟨u, hu⟩ := goldfishVoteWith_isSome c cache e hc nd st.core hm
  rw [hu]
  simp

/-- 投票の務めの出力の形: 投票者は自分、slot は store の時計の slot、投票者は committee の要素。 -/
theorem namedVote_fields (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) {st : NamedStore} {t : Int} {sl : Nat} (hX : ClockIs st t sl) {u : GoldfishVote}
    (h : (namedGoldfishVoteWith c cache e hc nd st).2 = some u) :
    u.valIndex = nd.valIndex ∧ u.slot = sl ∧ (c sl).contains nd.valIndex = true := by
  rw [namedGoldfishVoteWith_out] at h
  obtain ⟨h1, h2, -, h4, -⟩ := Proofs.Consensus.Votes.goldfishVoteWith_some c cache e hc nd st.core h
  rw [hX.2] at h2 h4
  exact ⟨h1, h2, h4⟩

/-! ## tick -/

section Tick

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
  (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Node) (st : NamedStore)
  (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int)

/-- **tick が出す投票の形**: 投票の時刻の tick(`0 < slotOf e t`、`t = voteTime e (slotOf e t)`)で、投票の務めが `voteStore` を
読んで出したもの。手書き `gfVote_emitted_shape`。 -/
theorem tick_gfVote_shape {u : GoldfishVote} (h : NamedObject.GfVote u ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    0 < slotOf e t ∧ t = voteTime e (slotOf e t) ∧
      (goldfishVoteWith c cache e hc nd (voteStore c p nr cache e hc cfg nd st t).core).2 = some u := by
  unfold tick at h
  dsimp only at h
  split_ifs at h
  all_goals simp only [List.mem_append] at h
  all_goals repeat' (obtain h | h := (h : _ ∨ _))
  all_goals first
    | (simp at h)
    | ((revert h; split <;> intro h <;> simp at h) <;> done)
    | (revert h; split <;> intro h
       · simp at h
       · rename_i v hv
         simp only [List.mem_singleton, NamedObject.GfVote.injEq] at h
         subst h
         have hv' : (decide (0 < slotOf e t) && t == voteTime e (slotOf e t)) = true := by assumption
         simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv'
         refine ⟨hv'.1, hv'.2, ?_⟩
         rw [← namedGoldfishVoteWith_out]
         unfold voteStore
         split_ifs
         all_goals exact hv)

/-- tick が出す投票の投票者は自分、slot は `slotOf e t`、投票者は committee の要素。 -/
theorem tick_gfVote_fields {u : GoldfishVote} (h : NamedObject.GfVote u ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    0 < slotOf e t ∧ t = voteTime e (slotOf e t) ∧ u.valIndex = nd.valIndex ∧ u.slot = slotOf e t ∧
      (c (slotOf e t)).contains nd.valIndex = true := by
  obtain ⟨h1, h2, h3⟩ := tick_gfVote_shape c p a nr cache e hc cfg nd st rec t h
  rw [← namedGoldfishVoteWith_out] at h3
  obtain ⟨h4, h5, h6⟩ := namedVote_fields c cache e hc nd (voteStore_clockIs c p nr cache e hc cfg nd st t) h3
  exact ⟨h1, h2, h4, h5, h6⟩

/-- 1 つの tick が出す投票は 1 つ。手書き `gfVote_emitted_unique`。 -/
theorem tick_gfVote_unique {u₁ u₂ : GoldfishVote}
    (h₁ : NamedObject.GfVote u₁ ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2)
    (h₂ : NamedObject.GfVote u₂ ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) : u₁ = u₂ := by
  obtain ⟨-, -, hd₁⟩ := tick_gfVote_shape c p a nr cache e hc cfg nd st rec t h₁
  obtain ⟨-, -, hd₂⟩ := tick_gfVote_shape c p a nr cache e hc cfg nd st rec t h₂
  rw [hd₁] at hd₂
  exact Option.some_inj.mp hd₂

/-- **投票の時刻の tick で committee の要素なら tick は投票を出す**(投票の務めは `awake'` を見ない)。 -/
theorem tick_gfVote_of_duty (hs : 0 < slotOf e t) (ht : t = voteTime e (slotOf e t))
    (hm : (c (slotOf e t)).contains nd.valIndex = true) :
    ∃ u, NamedObject.GfVote u ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2 ∧
      u.valIndex = nd.valIndex ∧ u.slot = slotOf e t := by
  have h0 : ClockIs { st with core := { st.core with t := t, s := slotOf e t } } t (slotOf e t) := ⟨rfl, rfl⟩
  -- `split_ifs` はこの仮定で投票しない分岐を閉じる
  have _hvt : (decide (0 < slotOf e t) && t == voteTime e (slotOf e t)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hs, ht⟩
  unfold tick
  dsimp only
  split_ifs
  all_goals (repeat' split)
  all_goals first
    | (rename_i hv
       exact absurd hv (namedVote_ne_none c cache e hc nd
         (by first | exact proposeBlockWith_clockIs c p nr cache hc nd h0 | exact h0) hm))
    | (rename_i v hv
       obtain ⟨h1, h2, -⟩ := namedVote_fields c cache e hc nd
         (by first | exact proposeBlockWith_clockIs c p nr cache hc nd h0 | exact h0) hv
       exact ⟨v, by simp, h1, h2⟩)

/-! ### 投票の head -/

/-- 投票の時刻の tick では提案の分岐は走らず、投票の務めが読む store は時計を合わせただけのもの(Δ > 0)。 -/
theorem voteStore_of_voteTime (hδ : 0 < e.delta) (ht : t = voteTime e (slotOf e t)) :
    voteStore c p nr cache e hc cfg nd st t = clocked e st t := by
  have hne : t ≠ proposalTime e (slotOf e t) :=
    fun h => voteTime_ne_proposalTime e hδ (slotOf e t) (ht.symm.trans h)
  unfold voteStore clocked
  simp [hne]

/-- **tick が出す投票の head**: tick の前の store に時計を合わせたものの fork choice の head(Δ > 0)。
手書き `gfVote_emitted_shape` の head の欄。 -/
theorem tick_gfVote_head (hδ : 0 < e.delta) {u : GoldfishVote}
    (h : NamedObject.GfVote u ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    0 < slotOf e t ∧ t = voteTime e (slotOf e t) ∧ u.valIndex = nd.valIndex ∧ u.slot = slotOf e t ∧
      u.head = voteHead cache e hc (clocked e st t).core := by
  obtain ⟨h1, h2, h3⟩ := tick_gfVote_shape c p a nr cache e hc cfg nd st rec t h
  rw [voteStore_of_voteTime c p nr cache e hc cfg nd st t hδ h2] at h3
  obtain ⟨h4, h5, h6, -, -⟩ := Proofs.Consensus.Votes.goldfishVoteWith_some c cache e hc nd _ h3
  exact ⟨h1, h2, h4, h5, h6⟩

end Tick

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

theorem nodeTick_gfVote_fields (v : ValidatorId) (n : NamedNodeState) (t : Int) {u : GoldfishVote}
    (h : NamedObject.GfVote u ∈ (nodeTick c p a nr s v n t).2) :
    0 < slotOf s.e t ∧ t = voteTime s.e (slotOf s.e t) ∧ u.valIndex = v ∧ u.slot = slotOf s.e t ∧
      (c (slotOf s.e t)).contains v = true := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at h
  exact tick_gfVote_fields c p a nr _ s.e s.hc s.cfg _ n.st n.signing t h

/-- **発行された投票は発行者自身の、その slot の投票の時刻の投票**で、発行者は committee の要素。手書き `emits_gfVote_shape`。 -/
theorem emits_gfVote_shape {v : ValidatorId} {u : GoldfishVote} {t : Int}
    (h : Emits c p a nr s rho v (NamedObject.GfVote u) t) :
    0 < slotOf s.e t ∧ t = voteTime s.e (slotOf s.e t) ∧ u.valIndex = v ∧ u.slot = slotOf s.e t ∧
      (c u.slot).contains v = true := by
  obtain ⟨i, -, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp h
  obtain ⟨h1, h2, h3, h4, h5⟩ := nodeTick_gfVote_fields c p a nr s v _ t ho
  exact ⟨h1, h2, h3, h4, by rw [h4]; exact h5⟩

/-- **どの投票者も slot ごとに発行する投票は 1 つ**: 2 つの発行はどちらもその slot の投票の時刻の tick で、event の重複なし
(`ScheduleWellFormed`)からその tick の添字は 1 つ、1 つの tick が出す投票は 1 つ。手書き `emits_gfVote_unique`。 -/
theorem emits_gfVote_unique (hsch : ScheduleWellFormed s rho) {v : ValidatorId} {u₁ u₂ : GoldfishVote} {t₁ t₂ : Int}
    (h₁ : Emits c p a nr s rho v (NamedObject.GfVote u₁) t₁) (h₂ : Emits c p a nr s rho v (NamedObject.GfVote u₂) t₂)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨-, ht₁, -, hu₁, -⟩ := emits_gfVote_shape c p a nr s rho h₁
  obtain ⟨-, ht₂, -, hu₂, -⟩ := emits_gfVote_shape c p a nr s rho h₂
  have hteq : t₁ = t₂ := by rw [ht₁, ht₂, ← hu₁, ← hu₂, hslot]
  subst hteq
  obtain ⟨i₁, hi₁, ho₁⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t₁).mp h₁
  obtain ⟨i₂, hi₂, ho₂⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t₁).mp h₂
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := hsch
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup (rho := rho) hnd
  obtain ⟨hb₁, he₁⟩ := List.getElem?_eq_some_iff.mp hi₁
  obtain ⟨hb₂, he₂⟩ := List.getElem?_eq_some_iff.mp hi₂
  have hidx : i₁ = i₂ := (List.Nodup.getElem_inj_iff hnd').mp (by rw [he₁, he₂])
  subst hidx
  rw [Proofs.Consensus.Signing.nodeTick_out] at ho₁ ho₂
  exact tick_gfVote_unique c p a nr _ s.e s.hc s.cfg _ _ _ t₁ ho₁ ho₂

/-- **発行された投票の head は、その tick の前の発行者の store に時計を合わせたものの fork choice の head**(Δ > 0)。
`Emits` の添字 `i` の event は発行者のその時刻の tick で、tick は `stateBefore i` の発行者の状態を読む。cache は tick の前に
`onPhaseTick` で進めたもの(`nodeTick`)。 -/
theorem emits_gfVote_head (hδ : 0 < s.e.delta) {v : ValidatorId} {u : GoldfishVote} {t : Int}
    (h : Emits c p a nr s rho v (NamedObject.GfVote u) t) :
    ∃ i, rho.events[i]? = some (NamedEvent.Tick v t) ∧
      0 < slotOf s.e t ∧ t = voteTime s.e (slotOf s.e t) ∧ u.valIndex = v ∧ u.slot = slotOf s.e t ∧
      u.head = voteHead
        (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) t
          (worldAt (stateBefore c p a nr s rho i) v).cache)
        s.e s.hc (clocked s.e (worldAt (stateBefore c p a nr s rho i) v).st t).core := by
  obtain ⟨i, hi, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp h
  rw [Proofs.Consensus.Signing.nodeTick_out] at ho
  obtain ⟨h1, h2, h3, h4, h5⟩ := tick_gfVote_head c p a nr _ s.e s.hc s.cfg _ _ _ t hδ ho
  exact ⟨i, hi, h1, h2, h3, h4, h5⟩

/-- **honest な committee の要素は各 slot の投票の時刻に投票を発行する**: `ScheduleWellFormed` は honest なノードの公開時刻の tick を
horizon まで run に入れ、投票の時刻は公開時刻で、その tick の投票の務めは committee の要素に投票を出させる。 -/
theorem honest_emits_gfVote (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {v : ValidatorId}
    (hv : rho.honest.contains v = true) {k : Nat} (hk : 0 < k) (hm : (c k).contains v = true)
    (hhor : voteTime s.e k ≤ rho.horizon) :
    ∃ u, Emits c p a nr s rho v (NamedObject.GfVote u) (voteTime s.e k) ∧ u.valIndex = v ∧ u.slot = k := by
  obtain ⟨-, hticks⟩ := hsch
  have hin := hticks v (voteTime s.e k)
    ⟨⟨⟨hv, publicTime_voteTime s.e k⟩, voteTime_nonneg s.e hδ.le k⟩, hhor⟩
  rw [List.contains_iff_mem] at hin
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hin
  have hsl := slotOf_voteTime s.e hδ k
  obtain ⟨u, hu, hval, hslot⟩ := tick_gfVote_of_duty c p a nr _ s.e s.hc s.cfg
    (Model.Consensus.Execution.Setup.setupNode v) (worldAt (stateBefore c p a nr s rho i) v).st
    (worldAt (stateBefore c p a nr s rho i) v).signing (voteTime s.e k)
    (by rw [hsl]; exact hk) (by rw [hsl]) (by rw [hsl]; exact hm)
  refine ⟨u, (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ _).mpr ⟨i, hi, ?_⟩, hval, hslot.trans hsl⟩
  rw [Proofs.Consensus.Signing.nodeTick_out]
  exact hu

/-- honest な committee の要素が slot `k` の投票の時刻に発行する投票と、その head(`emits_gfVote_head` の形)。 -/
theorem honest_emits_gfVote_head (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {v : ValidatorId}
    (hv : rho.honest.contains v = true) {k : Nat} (hk : 0 < k) (hm : (c k).contains v = true)
    (hhor : voteTime s.e k ≤ rho.horizon) :
    ∃ u i, Emits c p a nr s rho v (NamedObject.GfVote u) (voteTime s.e k) ∧ u.valIndex = v ∧ u.slot = k ∧
      rho.events[i]? = some (NamedEvent.Tick v (voteTime s.e k)) ∧
      u.head = voteHead
        (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) (voteTime s.e k)
          (worldAt (stateBefore c p a nr s rho i) v).cache)
        s.e s.hc (clocked s.e (worldAt (stateBefore c p a nr s rho i) v).st (voteTime s.e k)).core := by
  obtain ⟨u, he, hval, hslot⟩ := honest_emits_gfVote c p a nr s rho hsch hδ hv hk hm hhor
  obtain ⟨i, hi, -, -, -, -, hhead⟩ := emits_gfVote_head c p a nr s rho hδ he
  exact ⟨u, i, he, hval, hslot, hi, hhead⟩

end Run

end Proofs.Consensus.Voting
