import Proofs.Consensus.GradeSupporter
import Mathlib.Tactic

/-!
# grade の持ち越し(C77 の補題)

同じ block `b` の `gradeBool` を、2 つの grade view(同じノードの 2 つの tick の store)の間で持ち越す抽象的な段。
手書き `NamedOutageClosure.q10_gradeBool_transport`(`DecoupledConsensusProofs/Protocol/Grades/Q10Frame.lean` の §1・§2・§8)を
生成 Model の定義に対して示す(周回 238)。store・run・phase には触れない。

1. **token の代数**(`supports_iff` / `opposes_iff` で Bool を開いた形): 支持は、元の早い token のうち `b` を覆うものが
   先の早い集合に残り、先の早い・遅い集合が元の遅い集合に、先の raw が元の raw に含まれれば持ち越す(`supports_transport`。
   手書き `q10_supports_transport`)。先の早い集合が元の早い集合に含まれれば反対は戻る(`opposes_transport`)。早い集合が
   空でなく遅い集合に含まれれば、反対でないなら支持(`supports_of_not_opposes`)、遅い集合が raw に含まれれば、支持なら反対でない
   (`not_opposes_of_supports`)。
2. **cutoff の単調性**: `rawInputs` / `rawView` は cutoff について単調で(`rawInputs_mono` / `rawView_mono`)、`readyView` は
   `rawView` に含まれる(`readyView_sub_rawView`)。
3. **grade の持ち越し**(`gradeBool_transport`): 支持は持ち越し、反対は戻る(先の早い集合が空なら `opposes_transport`、
   空でなければ元で支持なので先でも支持で、先で反対にはならない)。重みは `支持(元) ≤ 支持(先)`・`反対(先) ≤ 反対(元)`。
-/

namespace Proofs.Consensus.GradeTransport

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Parameters
open Model.Consensus.Objects.Time Model.Consensus.Objects.Weights
open Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.Grades
open Proofs.Consensus.Sets Proofs.Consensus.Weights Proofs.Consensus.Orders Proofs.Consensus.GradeSupporter

/-! ## token の代数 -/

/-- `supports` を開いた形: 早い token `u` で、round が早い集合の中で最大、`u` の key が `b` を覆い、raw が `u` の round から
clean(同じ round の token の key は等しい)、`u` より後の遅い token はみな `b` を覆う。手書き `Supports`。 -/
theorem supports_iff (covers : Option BlockId → Block → Bool) (early late raw : NaruStd.Set Token) (b : Block) :
    supports covers early late raw b = true ↔
      ∃ u ∈ early.elems, (∀ x ∈ early.elems, x.round ≤ u.round) ∧ covers u.key b = true ∧
        (∀ x ∈ raw.elems, ∀ y ∈ raw.elems, u.round ≤ x.round → x.round = y.round → x.key = y.key) ∧
        (∀ x ∈ late.elems, u.round < x.round → covers x.key b = true) := by
  unfold supports cleanFrom NaruStd.Set.any NaruStd.Set.all
  simp only [List.any_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨⟨⟨hmax, hcov⟩, hclean⟩, hsweep⟩
    refine ⟨hmax, hcov, fun x hx y hy hux hxy => ?_, fun x hx hlt => ?_⟩
    · rcases hclean x hx y hy with (h | h) | h
      · exact absurd hux h
      · exact absurd hxy h
      · exact h
    · rcases hsweep x hx with h | h
      · exact absurd hlt h
      · exact h
  · rintro ⟨hmax, hcov, hclean, hsweep⟩
    refine ⟨⟨⟨hmax, hcov⟩, fun x hx y hy => ?_⟩, fun x hx => ?_⟩
    · by_cases hux : u.round ≤ x.round
      · by_cases hxy : x.round = y.round
        · exact Or.inr (hclean x hx y hy hux hxy)
        · exact Or.inl (Or.inr hxy)
      · exact Or.inl (Or.inl hux)
    · by_cases hlt : u.round < x.round
      · exact Or.inr (hsweep x hx hlt)
      · exact Or.inl hlt

/-- `opposes` を開いた形: 早い token の round がみな `x.round` 以下の遅い token `x` が `b` を覆わないか、早い token の round が
みな `x.round` 以下の raw の 2 つの token `x` / `y` が同じ round で key が違う。手書き `Opposes`。 -/
theorem opposes_iff (covers : Option BlockId → Block → Bool) (early late raw : NaruStd.Set Token) (b : Block) :
    opposes covers early late raw b = true ↔
      (∃ x ∈ late.elems, (∀ u ∈ early.elems, u.round ≤ x.round) ∧ covers x.key b = false) ∨
        (∃ x ∈ raw.elems, ∃ y ∈ raw.elems, (∀ u ∈ early.elems, u.round ≤ x.round) ∧ x.round = y.round ∧
          x.key ≠ y.key) := by
  unfold opposes NaruStd.Set.any NaruStd.Set.all
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq, and_assoc]

/-- **支持の持ち越し**: 元の早い token のうち `b` を覆うものが先の早い集合に残り(`hkeep`)、先の早い・遅い集合が元の遅い集合に、
先の raw が元の raw に、元・先の早い集合が元の raw に含まれ、元で覆う key は先でも覆うなら、元の支持は先の支持。
手書き `q10_supports_transport`。 -/
theorem supports_transport (c₁ c₂ : Option BlockId → Block → Bool) {ea eb la lb rawa rawb : NaruStd.Set Token}
    {b : Block}
    (hkeep : ∀ u ∈ ea.elems, c₁ u.key b = true → u ∈ eb.elems)
    (heb_la : ∀ x ∈ eb.elems, x ∈ la.elems) (hlb_la : ∀ x ∈ lb.elems, x ∈ la.elems)
    (hrawb : ∀ x ∈ rawb.elems, x ∈ rawa.elems)
    (hea_rawa : ∀ x ∈ ea.elems, x ∈ rawa.elems) (heb_rawa : ∀ x ∈ eb.elems, x ∈ rawa.elems)
    (hc : ∀ k, c₁ k b = true → c₂ k b = true)
    (hS : supports c₁ ea la rawa b = true) : supports c₂ eb lb rawb b = true := by
  rw [supports_iff] at hS ⊢
  obtain ⟨u, hu, -, hcov, hclean, hsweep⟩ := hS
  have hub : u ∈ eb.elems := hkeep u hu hcov
  obtain ⟨u', hu', hmax'⟩ : ∃ u' ∈ eb.elems, ∀ x ∈ eb.elems, x.round ≤ u'.round := by
    obtain ⟨u', hu', hmax'⟩ := Finset.exists_max_image eb.elems.toFinset (fun t => t.round)
      ⟨u, List.mem_toFinset.mpr hub⟩
    exact ⟨u', List.mem_toFinset.mp hu', fun x hx => hmax' x (List.mem_toFinset.mpr hx)⟩
  have hle : u.round ≤ u'.round := hmax' u hub
  refine ⟨u', hu', hmax', ?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact hc _ (hsweep u' (heb_la u' hu') hlt)
    · have hkey : u'.key = u.key := hclean u' (heb_rawa u' hu') u (hea_rawa u hu) hle heq.symm
      rw [hkey]
      exact hc _ hcov
  · intro x hx y hy hkx hxy
    exact hclean x (hrawb x hx) y (hrawb y hy) (le_trans hle hkx) hxy
  · intro x hx hlt
    exact hc _ (hsweep x (hlb_la x hx) (lt_of_le_of_lt hle hlt))

/-- **反対は戻る**: 先の早い集合が元の早い集合を含み、先の遅い集合・raw が元のものに含まれ、先で覆う key は元でも覆うなら、
元(早い `eb`)の反対は先(早い `ea`)の反対。手書き `q10_opposes_transport`(使うのは早い集合が空のときだけ)。 -/
theorem opposes_transport (c₁ c₂ : Option BlockId → Block → Bool) {ea eb la lb rawa rawb : NaruStd.Set Token}
    {b : Block}
    (he : ∀ x ∈ ea.elems, x ∈ eb.elems) (hl : ∀ x ∈ lb.elems, x ∈ la.elems) (hraw : ∀ x ∈ rawb.elems, x ∈ rawa.elems)
    (hc : ∀ k, c₂ k b = true → c₁ k b = true)
    (hO : opposes c₁ eb lb rawb b = true) : opposes c₂ ea la rawa b = true := by
  rw [opposes_iff] at hO ⊢
  rcases hO with ⟨x, hx, hguard, hnot⟩ | ⟨x, hx, y, hy, hguard, hround, hkey⟩
  · refine Or.inl ⟨x, hl x hx, fun u hu => hguard u (he u hu), ?_⟩
    cases h : c₂ x.key b
    · rfl
    · rw [hc _ h] at hnot
      exact absurd hnot (by decide)
  · exact Or.inr ⟨x, hraw x hx, y, hraw y hy, fun u hu => hguard u (he u hu), hround, hkey⟩

/-- **反対でなければ支持**: 早い集合が空でなく遅い集合に含まれれば、反対でない validator は支持する。手書き
`q10_supports_of_not_opposes`。 -/
theorem supports_of_not_opposes (c : Option BlockId → Block → Bool) {e l raw : NaruStd.Set Token} {b : Block}
    (hel : ∀ x ∈ e.elems, x ∈ l.elems) (hne : e.elems ≠ []) (hO : opposes c e l raw b = false) :
    supports c e l raw b = true := by
  rcases supports_or_opposes c e l raw b hne hel with h | h
  · exact h
  · rw [hO] at h
    exact absurd h (by decide)

/-- **支持なら反対でない**: 早い集合が遅い集合に、遅い集合が raw に含まれれば、支持する validator は同じ block に反対しない。
手書き `q10_not_opposes_of_supports`。 -/
theorem not_opposes_of_supports (c : Option BlockId → Block → Bool) {e l raw : NaruStd.Set Token} {b : Block}
    (hel : ∀ x ∈ e.elems, x ∈ l.elems) (hlr : ∀ x ∈ l.elems, x ∈ raw.elems)
    (hS : supports c e l raw b = true) : opposes c e l raw b = false := by
  rw [supports_iff] at hS
  obtain ⟨u, hu, -, hcov, hclean, hsweep⟩ := hS
  cases hO : opposes c e l raw b
  · rfl
  · rw [opposes_iff] at hO
    exfalso
    rcases hO with ⟨x, hx, hguard, hnot⟩ | ⟨x, hx, y, hy, hguard, hround, hkey⟩
    · rcases Nat.lt_or_ge u.round x.round with hlt | hge
      · rw [hsweep x hx hlt] at hnot
        exact absurd hnot (by decide)
      · have heq : u.round = x.round := Nat.le_antisymm (hguard u hu) hge
        have hk : u.key = x.key := hclean u (hlr u (hel u hu)) x (hlr x hx) le_rfl heq
        rw [← hk, hcov] at hnot
        exact absurd hnot (by decide)
    · exact hkey (hclean x hx y hy (hguard u hu) hround)

/-! ## cutoff の単調性 -/

/-- `rawInputs` は cutoff について単調。手書き `q10_rawInputs_cut`(`GradeCutoffMono.rawInputs_mono`)。 -/
theorem rawInputs_mono {gv : GradeView} {eta r : Nat} {c c' : Int} (hc : c ≤ c') {v : ValidatorId} {y : SGVote}
    (h : y ∈ (rawInputs gv eta r c v).elems) : y ∈ (rawInputs gv eta r c' v).elems := by
  rw [mem_rawInputs_iff] at h ⊢
  exact ⟨h.1, h.2.1, occurrenceBefore_mono h.2.2 hc⟩

/-- `rawView` の所属: 生の入力の token。 -/
theorem mem_rawView_iff (gv : GradeView) (eta r : Nat) (cutoff : Int) (v : ValidatorId) (x : Token) :
    x ∈ (rawView gv eta r cutoff v).elems ↔ ∃ y ∈ (rawInputs gv eta r cutoff v).elems, token y = x := by
  unfold rawView NaruStd.Set.map
  rw [mem_of_iff token_compare_eq_iff, List.mem_map]

/-- `rawView` は cutoff について単調。手書き `q10_rawView_cut`。 -/
theorem rawView_mono {gv : GradeView} {eta r : Nat} {c c' : Int} (hc : c ≤ c') (v : ValidatorId) :
    ∀ x ∈ (rawView gv eta r c v).elems, x ∈ (rawView gv eta r c' v).elems := by
  intro x hx
  rw [mem_rawView_iff] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, rawInputs_mono hc hy, rfl⟩

/-- `readyView` は同じ cutoff の `rawView` に含まれる。手書き `q10_ready_subset_raw`。 -/
theorem readyView_sub_rawView (gv : GradeView) (f : Block) (eta r : Nat) (c : Int) (v : ValidatorId) :
    ∀ x ∈ (readyView gv f eta r c v).elems, x ∈ (rawView gv eta r c v).elems := by
  intro x hx
  rw [mem_readyView_iff] at hx
  rw [mem_rawView_iff]
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, ((mem_interpretedInputs_iff gv f eta r c v y).mp hy).1, rfl⟩

/-! ## grade の持ち越し -/

/-- **grade の持ち越し**: 2 つの grade view `gva`(元)・`gvb`(先)と cutoff `ea ≤ la`・`eb ≤ lb` について、先の早い・遅い
ready が元の遅い ready に、先の遅い raw が元の遅い raw に含まれ、元の早い ready の token のうち `b` を覆うものが先の早い ready に
残り(`hkeep`)、元で `b` を覆う key は先でも覆うなら、元の `gradeBool` は先の `gradeBool`。支持は持ち越し、反対は戻る
(先の早い ready が空なら `opposes_transport`、空でなければ元で支持なので `supports_transport` で先でも支持)。
手書き `q10_gradeBool_transport`(`Protocol/Grades/Q10Frame.lean`)。 -/
theorem gradeBool_transport (e : ProtocolEnv) (hv : Sorted (validators e.electorate)) (gva gvb : GradeView)
    (fa fb : Block) (eta r : Nat) {ea la eb lb : Int} (hea_la : ea ≤ la) (heb_lb : eb ≤ lb) (b : Block)
    (heb_la : ∀ w, ∀ x ∈ (readyView gvb fb eta r eb w).elems, x ∈ (readyView gva fa eta r la w).elems)
    (hlb_la : ∀ w, ∀ x ∈ (readyView gvb fb eta r lb w).elems, x ∈ (readyView gva fa eta r la w).elems)
    (hrb_ra : ∀ w, ∀ x ∈ (rawView gvb eta r lb w).elems, x ∈ (rawView gva eta r la w).elems)
    (hkeep : ∀ w, ∀ u ∈ (readyView gva fa eta r ea w).elems,
      localCovers gva u.key b = true → u ∈ (readyView gvb fb eta r eb w).elems)
    (hcov : ∀ k, localCovers gva k b = true → localCovers gvb k b = true)
    (hgrade : gradeBool e gva fa eta r ea la b = true) :
    gradeBool e gvb fb eta r eb lb b = true := by
  have hla_ra := readyView_sub_rawView gva fa eta r la
  have hea_ra : ∀ w, ∀ x ∈ (readyView gva fa eta r ea w).elems, x ∈ (rawView gva eta r la w).elems :=
    fun w x hx => hla_ra w x (readyView_mono hea_la w x hx)
  have heb_ra : ∀ w, ∀ x ∈ (readyView gvb fb eta r eb w).elems, x ∈ (rawView gva eta r la w).elems :=
    fun w x hx => hla_ra w x (heb_la w x hx)
  have hpos : ∀ w, positive gva fa eta r ea la w b = true → positive gvb fb eta r eb lb w b = true := by
    intro w h
    exact supports_transport _ _ (hkeep w) (heb_la w) (hlb_la w) (hrb_ra w) (hea_ra w) (heb_ra w) hcov h
  have hopp : ∀ w, opposing gvb fb eta r eb lb w b = true → opposing gva fa eta r ea la w b = true := by
    intro w h1
    cases hno : opposing gva fa eta r ea la w b
    · exfalso
      by_cases hemp : (readyView gva fa eta r ea w).elems = []
      · have := opposes_transport (fun k x => localCovers gvb k x) (fun k x => localCovers gva k x)
          (ea := readyView gva fa eta r ea w) (fun x hx => by rw [hemp] at hx; simp at hx) (hlb_la w) (hrb_ra w)
          hcov h1
        change opposing gva fa eta r ea la w b = true at this
        rw [hno] at this
        exact absurd this (by decide)
      · have hsa : positive gva fa eta r ea la w b = true :=
          supports_of_not_opposes _ (readyView_mono hea_la w) hemp hno
        have hsb := hpos w hsa
        have := not_opposes_of_supports _ (readyView_mono heb_lb w)
          (readyView_sub_rawView gvb fb eta r lb w) hsb
        change opposing gvb fb eta r eb lb w b = false at this
        rw [h1] at this
        exact absurd this (by decide)
    · rfl
  have hsub1 : weightOf e.electorate ((validators e.electorate).filter (fun w => opposing gvb fb eta r eb lb w b)) ≤
      weightOf e.electorate ((validators e.electorate).filter (fun w => opposing gva fa eta r ea la w b)) := by
    apply Proofs.Consensus.JustificationCertificate.weightOf_le_of_sub (hv.filter _) (hv.filter _)
    intro z hz
    have hz' : z ∈ (validators e.electorate).elems.filter _ := hz
    rw [List.mem_filter] at hz'
    show z ∈ (validators e.electorate).elems.filter _
    rw [List.mem_filter]
    exact ⟨hz'.1, hopp z hz'.2⟩
  have hsub2 : weightOf e.electorate ((validators e.electorate).filter (fun w => positive gva fa eta r ea la w b)) ≤
      weightOf e.electorate ((validators e.electorate).filter (fun w => positive gvb fb eta r eb lb w b)) := by
    apply Proofs.Consensus.JustificationCertificate.weightOf_le_of_sub (hv.filter _) (hv.filter _)
    intro z hz
    have hz' : z ∈ (validators e.electorate).elems.filter _ := hz
    rw [List.mem_filter] at hz'
    show z ∈ (validators e.electorate).elems.filter _
    rw [List.mem_filter]
    exact ⟨hz'.1, hpos z hz'.2⟩
  unfold gradeBool at hgrade ⊢
  rw [decide_eq_true_iff] at hgrade ⊢
  omega

end Proofs.Consensus.GradeTransport
