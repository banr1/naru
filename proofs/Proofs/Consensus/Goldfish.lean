import Model.Consensus.Protocol.Handlers
import Proofs.Consensus.TreeInv
import Mathlib.Tactic

/-!
# Goldfish の fork choice と確認の候補(C71 の liveness 系 claim の足場)

claim `available` に残る事実 — `SleepyRegime` の下での確認の記録 `latestConfirmed` の honest な 2 ノード間の一致と
finalized との交差の互換、honest な提案の期限内の包含 `IncludedFrom` ×2、GST-zero の枝の finalized の一致 — はどれも、
`updateConfirmationWith`(`Model/Consensus/Protocol/Handlers.lean`)が確認の記録に書く候補が「Goldfish の投票の過半の支持を
受けた、fork choice `ghost` の結果」であることから始まる(手書き `GSTZeroSixFieldBypassNamed.lean` の「記録は後の honest な
投票者の head の接頭辞」の筋)。このモジュールはその最初の層を生成 Model の定義に対して示す:
- fork choice `ghost anchor tree score eligible`(`Model/Consensus/Protocol/ForkChoice/Goldfish.lean`)は anchor から適格な子
  (`ghostChildren`: tree の要素で親が現在の head、`eligible` が真)のうち得点最大の一意なもの(`argmax?` = `findUnique?`)へ
  降りる燃料つきの歩み `ghostWalk`。結果は anchor を延ばし(`ghost_preceq`)、anchor そのものか適格な tree の要素
  (`ghost_eligible`)。降下補題 `ghost_reaches`: anchor から `target` までの途中のブロックがすべて tree にあり、各ブロックで
  歩みの次の一歩が `target` の祖先で、`target` に適格な子が無ければ、結果は `target`(燃料 `size tree` が足りることは
  `path_card`: 途中のブロックは深さが相異なる tree の要素なので `size tree` 個以下)。手書き `Walk.lean` の `ghost_step_child` /
  `ghost_walk_preceq` / `ghost_preceq` / `ghost_walk_eligible` / `ghost_eligible` / `ghost_walk_reaches` / `ghost_reaches`。
  親について閉じた tree では結果に適格な子は無い(`ghost_terminal`: 燃料を使い切ると深さ `depth anchor + size tree` の
  tree の要素に達し、その祖先 `size tree + 1` 個が tree にあって矛盾)。
- Goldfish の得点 `goldfishScore`(`rawEquivocators` の個数 + `rawSupporters` の個数。支持者は slot `s` の投票が `b` 以下の
  ブロックを指す非 equivocator の投票者)は祖先ほど大きく(`goldfishScore_mono`)、支持者は投票の参加者(`rawSupporters_size_le`)。
  手書き `Confirmation.lean` の `supporters_mono` / `supporters_subset_participants`。
- `updateConfirmationWith` の `let` 束縛を名前つきの定義(`earlyVotes` / `lateVotes` / `supportVotes` / `lateCount` / `score` /
  `eligible` / `sgRoot` / `head` / `live` / `stableRec` / `candidate`)に開いて `updateConfirmationWith_eq`(`rfl`)で結び、
  新しい確認の記録は 元の記録 / stable の記録 / fork choice の head(過半の支持 `lateCount < 2 · score`、`sgRoot ⪯ head`)/
  grade の候補 `frameSgCandidate` のどれか(`latestConfirmed_shape`)。
残るのは、`SleepyRegime` の下で過半の支持に honest な投票者が含まれ、その head が honest な投票者の head の接頭辞であること
(正準性。stable の記録と grade の候補 `frameSgCandidate` の分岐についても同じ正準性)と、honest な提案が適格な子の一意な最大になって
`ghost_reaches` で選ばれること(包含)で、それはまだ証明していない。
-/

namespace Proofs.Consensus.Goldfish

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Parameters
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Schedule
open Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.ForkChoice.Head Model.Consensus.Protocol.Grades
open Proofs.Consensus.Blocks Proofs.Consensus.Sets Proofs.Consensus.Trees

/-! ## 深さと親 -/

/-- 子は親より 1 だけ深い。手書き `depth_of_parent?`。 -/
theorem depth_of_parent? {c h : Block} (hp : parent? c = some h) : depth c = depth h + 1 := by
  cases c with
  | Genesis => simp [parent?] at hp
  | Node p s r v sup ats i =>
    simp only [parent?, Option.some.injEq] at hp
    subst hp
    rfl

/-- 親は子の接頭辞。手書き `preceq_of_parent?`。 -/
theorem preceq_of_parent? {c h : Block} (hp : parent? c = some h) : preceq h c = true := by
  cases c with
  | Genesis => simp [parent?] at hp
  | Node p s r v sup ats i =>
    simp only [parent?, Option.some.injEq] at hp
    subst hp
    exact preceq_node _ _ _ _ _ _ _

/-- `parent b` は `b` の接頭辞(genesis の親は genesis)。 -/
theorem preceq_parent (b : Block) : preceq (parent b) b = true := by
  cases b with
  | Genesis => exact preceq_self _
  | Node p s r v sup ats i => exact preceq_node _ _ _ _ _ _ _

/-- `parent b` の深さは `depth b - 1`。 -/
theorem depth_parent (b : Block) : depth (parent b) = depth b - 1 := by
  cases b with
  | Genesis => rfl
  | Node p s r v sup ats i => show depth p = depth p + 1 - 1; omega

/-- genesis でなければ親は真に浅い。 -/
theorem depth_parent_lt {b : Block} (hb : 0 < depth b) : depth (parent b) < depth b := by
  rw [depth_parent]
  omega

/-- 接頭辞は深さが小さい(`b` の親を遡る帰納法)。手書き `Block.preceq_depth_le`。 -/
theorem preceq_depth_le {a b : Block} (h : preceq a b = true) : depth a ≤ depth b := by
  induction b with
  | Genesis =>
    simp only [preceq, beq_iff_eq] at h
    subst h
    exact le_refl _
  | Node p s r v sup ats i ih =>
    simp only [preceq, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact le_refl _
    · show depth a ≤ depth p + 1
      exact Nat.le_succ_of_le (ih h)

/-- 深さが減らない接頭辞は同じブロック。手書き `Block.preceq_eq_of_depth_le`。 -/
theorem preceq_eq_of_depth_le {a b : Block} (h : preceq a b = true) (hd : depth b ≤ depth a) : a = b := by
  induction b with
  | Genesis =>
    simp only [preceq, beq_iff_eq] at h
    exact h
  | Node p s r v sup ats i _ =>
    simp only [preceq, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rfl
    · have h1 := preceq_depth_le h
      have hd' : depth p + 1 ≤ depth a := hd
      omega

/-- 子は親の接頭辞ではない。手書き `preceq_parent_false`。 -/
theorem preceq_parent_false {c h : Block} (hp : parent? c = some h) : preceq c h = false := by
  rw [← Bool.not_eq_true]
  intro hpre
  have h1 := preceq_depth_le hpre
  rw [depth_of_parent? hp] at h1
  omega

/-- 同じブロック `target` の 2 つの祖先のうち深い方は浅い方を延ばす。 -/
theorem preceq_of_deeper {anchor C target : Block} (ha : preceq anchor target = true) (hc : preceq C target = true)
    (hd : depth anchor < depth C) : preceq anchor C = true := by
  rcases preceq_linear ha hc with h | h
  · exact h
  · have := preceq_depth_le h
    omega

/-! ## fork choice の一歩 -/

theorem mem_ghostChildren_iff (tree : NaruStd.Set Block) (el : Block → Bool) (h c : Block) :
    c ∈ (ghostChildren tree el h).elems ↔ c ∈ tree.elems ∧ parent? c = some h ∧ el c = true := by
  unfold ghostChildren
  rw [mem_filter_iff, Bool.and_eq_true, beq_iff_eq]

/-- 一歩の結果は tree の要素で、現在の head の子、適格、子の中で得点最大(`isBestIn`)。手書き `ghost_step_child`。 -/
theorem ghostStep_child {tree : NaruStd.Set Block} {score : Block → Nat} {el : Block → Bool} {h c : Block}
    (hc : ghostStep tree score el h = some c) :
    c ∈ tree.elems ∧ parent? c = some h ∧ el c = true ∧ isBestIn score (ghostChildren tree el h) c = true := by
  unfold ghostStep argmax? at hc
  obtain ⟨hmem, hbest⟩ := findUnique?_mem hc
  rw [mem_ghostChildren_iff] at hmem
  exact ⟨hmem.1, hmem.2.1, hmem.2.2, hbest⟩

theorem ghostStep_preceq {tree : NaruStd.Set Block} {score : Block → Nat} {el : Block → Bool} {h c : Block}
    (hc : ghostStep tree score el h = some c) : preceq h c = true :=
  preceq_of_parent? (ghostStep_child hc).2.1

theorem ghostStep_depth {tree : NaruStd.Set Block} {score : Block → Nat} {el : Block → Bool} {h c : Block}
    (hc : ghostStep tree score el h = some c) : depth c = depth h + 1 :=
  depth_of_parent? (ghostStep_child hc).2.1

/-- 適格な子が無ければ歩みは止まる。手書き `ghost_step_none`。 -/
theorem ghostStep_none {tree : NaruStd.Set Block} (score : Block → Nat) {el : Block → Bool} {h : Block}
    (hno : ∀ c ∈ tree.elems, parent? c = some h → el c = false) : ghostStep tree score el h = none := by
  have hnil : (ghostChildren tree el h).elems = [] := by
    unfold ghostChildren
    apply List.filter_eq_nil_iff.mpr
    intro c hc
    rw [Bool.and_eq_true, beq_iff_eq]
    rintro ⟨hp, hel⟩
    rw [hno c hc hp] at hel
    exact Bool.false_ne_true hel
  unfold ghostStep argmax? NaruStd.Set.findUnique?
  rw [hnil]
  rfl

/-! ## 歩みは anchor を延ばし、結果は適格 -/

/-- 歩みの結果は出発点を延ばす(燃料の帰納法)。手書き `ghost_walk_preceq`。 -/
theorem ghostWalk_preceq (tree : NaruStd.Set Block) (score : Block → Nat) (el : Block → Bool) :
    ∀ (fuel : Nat) (h : Block), preceq h (ghostWalk tree score el fuel h) = true
  | 0, h => by
    rw [ghostWalk]
    split
    · exact preceq_self h
    · rename_i hz
      simp at hz
  | n + 1, h => by
    rw [ghostWalk]
    split
    · rename_i hz
      simp at hz
    cases hstep : ghostStep tree score el h with
    | none =>
      dsimp only
      exact preceq_self h
    | some c =>
      dsimp only
      rw [Nat.add_sub_cancel]
      exact preceq_trans (ghostStep_preceq hstep) (ghostWalk_preceq tree score el n c)

/-- fork choice の結果は anchor を延ばす。手書き `ghost_preceq`。 -/
theorem ghost_preceq (anchor : Block) (tree : NaruStd.Set Block) (score : Block → Nat) (el : Block → Bool) :
    preceq anchor (ghost anchor tree score el) = true :=
  ghostWalk_preceq tree score el _ anchor

/-- 歩みの結果は出発点そのものか、適格な tree の要素。手書き `ghost_walk_eligible`。 -/
theorem ghostWalk_eligible (tree : NaruStd.Set Block) (score : Block → Nat) (el : Block → Bool) :
    ∀ (fuel : Nat) (h : Block), ghostWalk tree score el fuel h = h ∨
      (ghostWalk tree score el fuel h ∈ tree.elems ∧ el (ghostWalk tree score el fuel h) = true)
  | 0, h => by
    rw [ghostWalk]
    split
    · exact Or.inl rfl
    · rename_i hz
      simp at hz
  | n + 1, h => by
    rw [ghostWalk]
    split
    · rename_i hz
      simp at hz
    cases hstep : ghostStep tree score el h with
    | none =>
      dsimp only
      exact Or.inl rfl
    | some c =>
      dsimp only
      rw [Nat.add_sub_cancel]
      rcases ghostWalk_eligible tree score el n c with heq | hel
      · rw [heq]
        exact Or.inr ⟨(ghostStep_child hstep).1, (ghostStep_child hstep).2.2.1⟩
      · exact Or.inr hel

/-- fork choice の結果は anchor そのものか、適格な tree の要素。手書き `ghost_eligible`。 -/
theorem ghost_eligible (anchor : Block) (tree : NaruStd.Set Block) (score : Block → Nat) (el : Block → Bool) :
    ghost anchor tree score el = anchor ∨
      (ghost anchor tree score el ∈ tree.elems ∧ el (ghost anchor tree score el) = true) :=
  ghostWalk_eligible tree score el _ anchor

/-- 歩みは止まるか、燃料をすべて使って燃料の分だけ深くなる。 -/
theorem ghostWalk_stop_or_depth (tree : NaruStd.Set Block) (score : Block → Nat) (el : Block → Bool) :
    ∀ (fuel : Nat) (h : Block), ghostStep tree score el (ghostWalk tree score el fuel h) = none ∨
      depth (ghostWalk tree score el fuel h) = depth h + fuel
  | 0, h => by
    rw [ghostWalk]
    split
    · exact Or.inr rfl
    · rename_i hz
      simp at hz
  | n + 1, h => by
    rw [ghostWalk]
    split
    · rename_i hz
      simp at hz
    cases hstep : ghostStep tree score el h with
    | none =>
      dsimp only
      exact Or.inl hstep
    | some c =>
      dsimp only
      rw [Nat.add_sub_cancel]
      rcases ghostWalk_stop_or_depth tree score el n c with hstop | hd
      · exact Or.inl hstop
      · right
        rw [hd, ghostStep_depth hstep]
        omega

/-! ## 祖先の列と燃料 -/

/-- `b` から親を遡る長さ `n` の列(`b` を含む)。 -/
def chainUpTo : Nat → Block → List Block
  | 0, _ => []
  | n + 1, b => b :: chainUpTo n (parent b)

theorem chainUpTo_length : ∀ (n : Nat) (b : Block), (chainUpTo n b).length = n
  | 0, _ => rfl
  | n + 1, b => by
    simp only [chainUpTo, List.length_cons]
    rw [chainUpTo_length n (parent b)]

/-- 列の要素は `b` の祖先で、深さは `depth b - n` より大きい。 -/
theorem mem_chainUpTo : ∀ (n : Nat) (b C : Block), C ∈ chainUpTo n b →
    preceq C b = true ∧ depth b < depth C + n
  | 0, _, _, h => by simp [chainUpTo] at h
  | n + 1, b, C, h => by
    simp only [chainUpTo, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨preceq_self _, by omega⟩
    · obtain ⟨hp, hd⟩ := mem_chainUpTo n (parent b) C h
      refine ⟨preceq_trans hp (preceq_parent b), ?_⟩
      rw [depth_parent] at hd
      omega

theorem chainUpTo_pos {n : Nat} {b C : Block} (h : C ∈ chainUpTo n b) : 0 < n := by
  cases n with
  | zero => simp [chainUpTo] at h
  | succ n => exact Nat.succ_pos n

/-- genesis を越えて遡らなければ(`n ≤ depth b + 1`)、列の深さは狭義に減る。 -/
theorem pairwise_chainUpTo : ∀ (n : Nat) (b : Block), n ≤ depth b + 1 →
    (chainUpTo n b).Pairwise (fun x y => depth y < depth x)
  | 0, _, _ => List.Pairwise.nil
  | n + 1, b, hn => by
    simp only [chainUpTo]
    rw [List.pairwise_cons]
    refine ⟨fun C hC => ?_, ?_⟩
    · have hpos := chainUpTo_pos hC
      have hle := preceq_depth_le (mem_chainUpTo n (parent b) C hC).1
      have hlt := depth_parent_lt (b := b) (by omega)
      omega
    · apply pairwise_chainUpTo n (parent b)
      rw [depth_parent]
      omega

theorem nodup_chainUpTo {n : Nat} {b : Block} (hn : n ≤ depth b + 1) : (chainUpTo n b).Nodup :=
  (pairwise_chainUpTo n b hn).imp (fun h heq => by rw [heq] at h; exact Nat.lt_irrefl _ h)

/-- genesis を越えない祖先の列が tree に含まれれば、その長さは tree の大きさ以下(深さが相異なるので重複なし)。 -/
theorem chainUpTo_le_size {tree : NaruStd.Set Block} {n : Nat} {b : Block} (hn : n ≤ depth b + 1)
    (hsub : ∀ C ∈ chainUpTo n b, C ∈ tree.elems) : n ≤ tree.size := by
  have h := List.Subperm.length_le (List.subperm_of_subset (nodup_chainUpTo hn) hsub)
  rw [chainUpTo_length] at h
  exact h

/-- anchor から `target` までの途中のブロック(anchor を除く)がすべて tree にあれば、`target` の深さは
`depth anchor + size tree` 以下 — 燃料 `size tree` で届く。手書き `path_card`。 -/
theorem path_card {tree : NaruStd.Set Block} {anchor target : Block} (hpre : preceq anchor target = true)
    (hpath : ∀ C, preceq anchor C = true → C ≠ anchor → preceq C target = true → C ∈ tree.elems) :
    depth target ≤ depth anchor + tree.size := by
  have hda := preceq_depth_le hpre
  have hn : depth target - depth anchor ≤ tree.size := by
    apply chainUpTo_le_size (b := target) (by omega)
    intro C hC
    obtain ⟨hCt, hdC⟩ := mem_chainUpTo _ target C hC
    have hlt : depth anchor < depth C := by omega
    refine hpath C (preceq_of_deeper hpre hCt hlt) (fun h => ?_) hCt
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  omega

/-! ## 降下補題 -/

/-- 燃料つきの歩みは、途中の各ブロックで次の一歩が `target` の祖先で、`target` に適格な子が無く、燃料が深さの差以上なら
`target` に着く。手書き `ghost_walk_reaches`。 -/
theorem ghostWalk_reaches {tree : NaruStd.Set Block} {score : Block → Nat} {el : Block → Bool} {anchor target : Block}
    (hstop : ghostStep tree score el target = none)
    (hstep : ∀ H, preceq anchor H = true → preceq H target = true → H ≠ target →
      ∃ C, ghostStep tree score el H = some C ∧ preceq C target = true) :
    ∀ (fuel : Nat) (H : Block), preceq anchor H = true → preceq H target = true →
      depth target ≤ depth H + fuel → ghostWalk tree score el fuel H = target
  | 0, H, _, hpre, hd => by
    have hH : H = target := preceq_eq_of_depth_le hpre (by omega)
    rw [ghostWalk]
    split
    · exact hH
    · rename_i hz
      simp at hz
  | n + 1, H, hanch, hpre, hd => by
    rw [ghostWalk]
    split
    · rename_i hz
      simp at hz
    by_cases hHt : H = target
    · subst hHt
      rw [hstop]
    · obtain ⟨C, hCs, hCp⟩ := hstep H hanch hpre hHt
      have hdepth := ghostStep_depth hCs
      rw [hCs]
      dsimp only
      rw [Nat.add_sub_cancel]
      exact ghostWalk_reaches hstop hstep n C (preceq_trans hanch (ghostStep_preceq hCs)) hCp (by omega)

/-- **降下補題**: anchor から `target` までの途中のブロック(anchor を除き `target` を含む)がすべて tree にあり、各ブロックで歩みの
次の一歩が `target` の祖先で、`target` に適格な子が無ければ、fork choice の結果は `target`。手書き `ghost_reaches`(前提も同じ形。
`hpath` は `hstep` の一歩が tree の要素であることから導けるが、手書きに合わせて前提のまま置く)。 -/
theorem ghost_reaches {tree : NaruStd.Set Block} {score : Block → Nat} {el : Block → Bool} {anchor target : Block}
    (hpre : preceq anchor target = true)
    (hpath : ∀ C, preceq anchor C = true → C ≠ anchor → preceq C target = true → C ∈ tree.elems)
    (hstop : ghostStep tree score el target = none)
    (hstep : ∀ H, preceq anchor H = true → preceq H target = true → H ≠ target →
      ∃ C, ghostStep tree score el H = some C ∧ preceq C target = true) :
    ghost anchor tree score el = target := by
  unfold ghost
  exact ghostWalk_reaches hstop hstep tree.size anchor (preceq_self _) hpre (path_card hpre hpath)

/-- 親について閉じた tree では、fork choice の結果に適格な子は無い(歩みは適格な部分木の葉まで降りる)。
燃料を使い切ったなら結果は深さ `depth anchor + size tree` の tree の要素で、anchor 以上の深さの祖先 `size tree + 1` 個が
tree にあることになり矛盾。 -/
theorem ghost_terminal {tree : NaruStd.Set Block} (hclosed : ∀ x, x ∈ tree.elems → parent x ∈ tree.elems)
    (anchor : Block) (score : Block → Nat) (el : Block → Bool) :
    ghostStep tree score el (ghost anchor tree score el) = none := by
  cases hstep : ghostStep tree score el (ghost anchor tree score el) with
  | none => rfl
  | some c =>
    exfalso
    rcases ghostWalk_stop_or_depth tree score el tree.size anchor with hstop | hd
    · -- 歩みが止まっていたなら一歩は無い
      have hstop' : ghostStep tree score el (ghost anchor tree score el) = none := hstop
      rw [hstop'] at hstep
      exact absurd hstep (by simp)
    · -- 燃料を使い切って一歩でも進んだなら結果は tree の要素。進んでいなければ tree は空で一歩も踏めない
      have hdR : depth (ghost anchor tree score el) = depth anchor + tree.size := hd
      have hc := (ghostStep_child hstep).1
      have hRmem : ghost anchor tree score el ∈ tree.elems := by
        rcases ghost_cases anchor tree score el with heq | hmem
        · have hsz : tree.size = 0 := by
            rw [heq] at hdR
            omega
          have hnil : tree.elems = [] := List.length_eq_zero_iff.mp hsz
          rw [hnil] at hc
          simp at hc
        · exact hmem
      have hn : tree.size + 1 ≤ tree.size := by
        apply chainUpTo_le_size (b := ghost anchor tree score el) (by omega)
        intro C hC
        obtain ⟨hCR, -⟩ := mem_chainUpTo _ _ C hC
        exact ancestor_mem_tree hclosed hCR hRmem
      omega

/-! ## Goldfish の投票者・支持者・得点 -/

theorem mem_votesBy_iff (votes : NaruStd.Set GoldfishVote) (v : ValidatorId) (u : GoldfishVote) :
    u ∈ (votesBy votes v).elems ↔ u ∈ votes.elems ∧ u.valIndex = v := by
  unfold votesBy
  rw [mem_filter_iff, beq_iff_eq]

/-- 投票者の集合の所属。 -/
theorem mem_voters_iff (votes : NaruStd.Set GoldfishVote) (v : ValidatorId) :
    v ∈ (voters votes).elems ↔ ∃ u ∈ votes.elems, u.valIndex = v := by
  unfold voters NaruStd.Set.map
  rw [mem_of_iff vid_eq, List.mem_map]

/-- 投票を持つ validator は参加者。 -/
theorem participates_of_mem {votes : NaruStd.Set GoldfishVote} {v : ValidatorId} {u : GoldfishVote}
    (hu : u ∈ votes.elems) (hv : u.valIndex = v) : participates votes v = true := by
  unfold participates
  rw [decide_eq_true_eq]
  show 0 < (votesBy votes v).elems.length
  exact List.length_pos_iff_exists_mem.mpr ⟨u, (mem_votesBy_iff votes v u).mpr ⟨hu, hv⟩⟩

/-- 投票 `u` が `b` 以下を指す(`targetsUnder`): head の root が tree に一意にあり、その slot は投票の slot 以下で、`b` の子孫。 -/
theorem targetsUnder_iff (tree : NaruStd.Set Block) (b : Block) (u : GoldfishVote) :
    targetsUnder tree b u = true ↔
      ∃ c, findRoot? tree u.head = some c ∧ slot c ≤ u.slot ∧ preceq b c = true := by
  unfold targetsUnder
  cases h : findRoot? tree u.head with
  | none => simp
  | some c =>
    constructor
    · intro h'
      rw [Bool.and_eq_true, decide_eq_true_eq] at h'
      exact ⟨c, rfl, h'.1, h'.2⟩
    · rintro ⟨c', hc', hs, hp⟩
      rw [Option.some.injEq] at hc'
      subst hc'
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hs, hp⟩

/-- 子孫を指す投票は祖先も指す。 -/
theorem targetsUnder_mono {tree : NaruStd.Set Block} {b b' : Block} {u : GoldfishVote} (hbb : preceq b b' = true)
    (h : targetsUnder tree b' u = true) : targetsUnder tree b u = true := by
  rw [targetsUnder_iff] at h ⊢
  obtain ⟨c, hc, hs, hp⟩ := h
  exact ⟨c, hc, hs, preceq_trans hbb hp⟩

/-- 支持者の所属: `supportVotes` の投票者で、`votes` で equivocate せず、slot `s` の `b` 以下を指す投票を持つ。
手書き `mem_supporters_iff`。 -/
theorem mem_rawSupporters_iff (tree : NaruStd.Set Block) (votes sv : NaruStd.Set GoldfishVote) (s : Nat) (b : Block)
    (v : ValidatorId) :
    v ∈ (rawSupporters tree votes sv s b).elems ↔
      v ∈ (voters sv).elems ∧ equivocates votes v = false ∧
        ∃ u ∈ sv.elems, u.valIndex = v ∧ u.slot = s ∧ targetsUnder tree b u = true := by
  unfold rawSupporters
  rw [mem_filter_iff, Bool.and_eq_true, Bool.not_eq_true', NaruStd.Set.any, List.any_eq_true]
  constructor
  · rintro ⟨hv, hne, u, hu, hp⟩
    rw [mem_votesBy_iff] at hu
    rw [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨hv, hne, u, hu.1, hu.2, hp.1, hp.2⟩
  · rintro ⟨hv, hne, u, hu, hvi, hs, ht⟩
    refine ⟨hv, hne, u, (mem_votesBy_iff _ _ _).mpr ⟨hu, hvi⟩, ?_⟩
    rw [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hs, ht⟩

/-- 支持は祖先に継承される。手書き `supporters_mono`。 -/
theorem rawSupporters_mono {tree : NaruStd.Set Block} {votes sv : NaruStd.Set GoldfishVote} {s : Nat} {b b' : Block}
    (hbb : preceq b b' = true) :
    ∀ v ∈ (rawSupporters tree votes sv s b').elems, v ∈ (rawSupporters tree votes sv s b).elems := by
  intro v hv
  rw [mem_rawSupporters_iff] at hv ⊢
  obtain ⟨hv, hne, u, hu, hvi, hs, ht⟩ := hv
  exact ⟨hv, hne, u, hu, hvi, hs, targetsUnder_mono hbb ht⟩

/-- 支持者は投票の参加者。手書き `supporters_subset_participants`。 -/
theorem rawSupporters_sub_participants (tree : NaruStd.Set Block) (votes sv : NaruStd.Set GoldfishVote) (s : Nat)
    (b : Block) : ∀ v ∈ (rawSupporters tree votes sv s b).elems, v ∈ (rawParticipants sv).elems := by
  intro v hv
  rw [mem_rawSupporters_iff] at hv
  obtain ⟨hvo, -, u, hu, hvi, -, -⟩ := hv
  unfold rawParticipants
  rw [mem_filter_iff]
  exact ⟨hvo, participates_of_mem hu hvi⟩

/-- 同じ集合の 2 つの `filter` の大きさは述語の含意で比較できる。 -/
theorem size_filter_le {α : Type} [Ord α] (s : NaruStd.Set α) {p q : α → Bool}
    (h : ∀ x ∈ s.elems, p x = true → q x = true) : (s.filter p).size ≤ (s.filter q).size := by
  show (s.elems.filter p).length ≤ (s.elems.filter q).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left h

theorem rawSupporters_size_mono {tree : NaruStd.Set Block} {votes sv : NaruStd.Set GoldfishVote} {s : Nat} {b b' : Block}
    (hbb : preceq b b' = true) :
    (rawSupporters tree votes sv s b').size ≤ (rawSupporters tree votes sv s b).size := by
  unfold rawSupporters
  apply size_filter_le
  intro v hv hp
  have hm : v ∈ (rawSupporters tree votes sv s b').elems := by
    unfold rawSupporters
    exact (mem_filter_iff _ _ _).mpr ⟨hv, hp⟩
  have := rawSupporters_mono hbb v hm
  unfold rawSupporters at this
  exact ((mem_filter_iff _ _ _).mp this).2

/-- 支持者の数は参加者の数(`rawVotersCount`)以下。 -/
theorem rawSupporters_size_le (tree : NaruStd.Set Block) (votes sv : NaruStd.Set GoldfishVote) (s : Nat) (b : Block) :
    (rawSupporters tree votes sv s b).size ≤ rawVotersCount sv := by
  unfold rawSupporters rawVotersCount rawParticipants
  apply size_filter_le
  intro v hv hp
  have hm : v ∈ (rawSupporters tree votes sv s b).elems := by
    unfold rawSupporters
    exact (mem_filter_iff _ _ _).mpr ⟨hv, hp⟩
  have := rawSupporters_sub_participants tree votes sv s b v hm
  unfold rawParticipants at this
  exact ((mem_filter_iff _ _ _).mp this).2

/-- 得点は祖先ほど大きい(equivocator の項は共通)。 -/
theorem rawGoldfishScore_mono {tree : NaruStd.Set Block} {votes sv : NaruStd.Set GoldfishVote} {s : Nat} {b b' : Block}
    (hbb : preceq b b' = true) : rawGoldfishScore tree votes sv s b' ≤ rawGoldfishScore tree votes sv s b := by
  unfold rawGoldfishScore
  exact Nat.add_le_add_left (rawSupporters_size_mono hbb) _

theorem goldfishScore_mono (e : ProtocolEnv) {tree : NaruStd.Set Block} {votes sv : NaruStd.Set GoldfishVote} {s : Nat}
    {b b' : Block} (hbb : preceq b b' = true) :
    goldfishScore e tree votes sv s b' ≤ goldfishScore e tree votes sv s b :=
  rawGoldfishScore_mono hbb

/-- 支持者が 1 人でもいれば、その投票は slot `s` で `b` 以下を指す。 -/
theorem exists_supporter_of_pos {tree : NaruStd.Set Block} {votes sv : NaruStd.Set GoldfishVote} {s : Nat} {b : Block}
    (h : 0 < (rawSupporters tree votes sv s b).size) :
    ∃ v u, u ∈ sv.elems ∧ u.valIndex = v ∧ equivocates votes v = false ∧ u.slot = s ∧ targetsUnder tree b u = true := by
  obtain ⟨v, hv⟩ := List.length_pos_iff_exists_mem.mp h
  rw [mem_rawSupporters_iff] at hv
  obtain ⟨-, hne, u, hu, hvi, hs, ht⟩ := hv
  exact ⟨v, u, hu, hvi, hne, hs, ht⟩

/-! ## `updateConfirmationWith` の候補 -/

/-- `supportCutoff` までに解決した slot `s` の投票(`updateConfirmationWith` の `earlyVotes`)。 -/
def earlyVotes (e : ProtocolEnv) (st : Store) (s : Nat) : NaruStd.Set GoldfishVote :=
  NaruStd.Set.filter (storePool st s) (fun u => Model.Consensus.Objects.Time.occurrenceBefore (storeTau st u) (supportCutoff e s))

/-- `confirmationTime` までに届いた slot `s` の投票(`lateVotes`)。 -/
def lateVotes (e : ProtocolEnv) (st : Store) (s : Nat) : NaruStd.Set GoldfishVote :=
  NaruStd.Set.filter (storePool st s)
    (fun u => Model.Consensus.Objects.Time.occurrenceBefore (NaruStd.Table.get? st.timestampVote u) (confirmationTime e s))

/-- 早い投票のうち、遅い投票に同じ投票者の別の投票が無いもの(`supportVotes`)。 -/
def supportVotes (e : ProtocolEnv) (st : Store) (s : Nat) : NaruStd.Set GoldfishVote :=
  NaruStd.Set.filter (earlyVotes e st s) (fun u => noSecondVoteIn (lateVotes e st s) u)

/-- 遅い投票の参加者の数(`lateCount`)。 -/
def lateCount (e : ProtocolEnv) (st : Store) (s : Nat) : Nat := votersCount e (lateVotes e st s) s

/-- 確認の得点(`score`): 支持の投票による Goldfish の得点。 -/
def score (e : ProtocolEnv) (st : Store) (s : Nat) (b : Block) : Nat :=
  goldfishScore e st.tree (supportVotes e st s) (supportVotes e st s) s b

/-- 適格(`eligible`): 得点の 2 倍が遅い投票の参加者の数を超える(過半の支持)。 -/
def eligible (e : ProtocolEnv) (st : Store) (s : Nat) (b : Block) : Bool :=
  decide (lateCount e st s < 2 * score e st s b)

/-- fork choice の anchor(`sgRoot`): grade の読みの SG root。 -/
def sgRoot (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) : Block :=
  getSgRootWith c e hc (storeToHealing st) (roundOf hc st.s)

/-- fork choice の結果(`h`)。 -/
def head (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) : Block :=
  ghost (sgRoot c e hc st) (getFilteredBlockTree (storeToHealing st)) (score e st s) (eligible e st s)

/-- `liveConfirmed` に書く値(`live`)。 -/
def live (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) : Block :=
  if eligible e st s (head c e hc st s) then head c e hc st s else getFgRoot (storeToHealing st)

/-- `latestStable` に書く値(`stable`)。 -/
def stableRec (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) : Block :=
  match frameStableRoot c e hc (storeToHealing st) (roundOf hc st.s) with
  | some g => advanceConfirmed st.latestStable g
  | none => st.latestStable

/-- 確認の候補(`candidate`): 適格な head か、grade の候補か、元の記録。 -/
def candidate (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) : Block :=
  if eligible e st s (head c e hc st s) then advanceConfirmed st.latestConfirmed (head c e hc st s)
  else
    match frameSgCandidate c e hc (storeToHealing st) s with
    | some cand => advanceConfirmed st.latestConfirmed cand
    | none => st.latestConfirmed

/-- `updateConfirmationWith` は上の名前つきの値で書ける(`let` を開いただけ。定義的に等しい)。 -/
theorem updateConfirmationWith_eq (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) :
    updateConfirmationWith c e hc st s =
      { st with liveConfirmed := live c e hc st s,
                latestConfirmed := floorOnStable (stableRec c e hc st) (candidate c e hc st s) st.latestConfirmed,
                latestStable := stableRec c e hc st } := rfl

theorem eligible_iff (e : ProtocolEnv) (st : Store) (s : Nat) (b : Block) :
    eligible e st s b = true ↔ lateCount e st s < 2 * score e st s b := by
  unfold eligible
  exact decide_eq_true_iff

/-- fork choice の head は SG root を延ばす。手書き `live_confirmed_preceq_root` の genuine-confirmation の半分。 -/
theorem sgRoot_preceq_head (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) :
    preceq (sgRoot c e hc st) (head c e hc st s) = true :=
  ghost_preceq _ _ _ _

/-- head は SG root そのものか、filtered tree の適格な要素。 -/
theorem head_cases (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) :
    head c e hc st s = sgRoot c e hc st ∨
      (head c e hc st s ∈ (getFilteredBlockTree (storeToHealing st)).elems ∧
        lateCount e st s < 2 * score e st s (head c e hc st s)) := by
  rcases ghost_eligible (sgRoot c e hc st) (getFilteredBlockTree (storeToHealing st)) (score e st s) (eligible e st s)
    with h | ⟨hmem, hel⟩
  · exact Or.inl h
  · exact Or.inr ⟨hmem, (eligible_iff e st s _).mp hel⟩

theorem advanceConfirmed_cases (old cand : Block) :
    (preceq cand old = true ∧ advanceConfirmed old cand = old) ∨
      (¬ preceq cand old = true ∧ advanceConfirmed old cand = cand) := by
  unfold advanceConfirmed
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

theorem floorOnStable_cases (stable cand old : Block) :
    floorOnStable stable cand old = cand ∨ floorOnStable stable cand old = old ∨ floorOnStable stable cand old = stable := by
  unfold floorOnStable
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- 確認の候補は、元の記録か、適格な head(元の記録を延ばさないときに限り選ばれる)か、grade の候補。 -/
theorem candidate_cases (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) :
    candidate c e hc st s = st.latestConfirmed ∨
      (lateCount e st s < 2 * score e st s (head c e hc st s) ∧ candidate c e hc st s = head c e hc st s) ∨
      (∃ g, frameSgCandidate c e hc (storeToHealing st) s = some g ∧ candidate c e hc st s = g) := by
  unfold candidate
  split_ifs with hel
  · rcases advanceConfirmed_cases st.latestConfirmed (head c e hc st s) with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨(eligible_iff e st s _).mp hel, h⟩)
  · cases hg : frameSgCandidate c e hc (storeToHealing st) s with
    | none => exact Or.inl rfl
    | some g =>
      dsimp only
      rcases advanceConfirmed_cases st.latestConfirmed g with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨g, rfl, h⟩)

/-- 新しい確認の記録は、候補か、元の記録か、stable の記録。 -/
theorem latestConfirmed_cases (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) :
    (updateConfirmationWith c e hc st s).latestConfirmed = candidate c e hc st s ∨
      (updateConfirmationWith c e hc st s).latestConfirmed = st.latestConfirmed ∨
      (updateConfirmationWith c e hc st s).latestConfirmed = stableRec c e hc st := by
  rw [updateConfirmationWith_eq]
  exact floorOnStable_cases _ _ _

/-- **確認の記録の形**: `updateConfirmationWith` の後の `latestConfirmed` は、元の記録か、stable の記録か、
過半の支持(`lateCount < 2 · score`)を持ち SG root を延ばす fork choice の head か、grade の候補 `frameSgCandidate` のどれか。 -/
theorem latestConfirmed_shape (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (s : Nat) :
    (updateConfirmationWith c e hc st s).latestConfirmed = st.latestConfirmed ∨
      (updateConfirmationWith c e hc st s).latestConfirmed = stableRec c e hc st ∨
      ((updateConfirmationWith c e hc st s).latestConfirmed = head c e hc st s ∧
        lateCount e st s < 2 * score e st s (head c e hc st s) ∧
        preceq (sgRoot c e hc st) (head c e hc st s) = true) ∨
      (∃ g, frameSgCandidate c e hc (storeToHealing st) s = some g ∧
        (updateConfirmationWith c e hc st s).latestConfirmed = g) := by
  rcases latestConfirmed_cases c e hc st s with hcand | hold | hstable
  · rcases candidate_cases c e hc st s with h | ⟨hmaj, h⟩ | ⟨g, hg, h⟩
    · exact Or.inl (hcand.trans h)
    · exact Or.inr (Or.inr (Or.inl ⟨hcand.trans h, hmaj, sgRoot_preceq_head c e hc st s⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨g, hg, hcand.trans h⟩))
  · exact Or.inl hold
  · exact Or.inr (Or.inl hstable)

/-- `latestStable` に書く値は元の記録か grade の stable root。 -/
theorem stableRec_cases (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) :
    stableRec c e hc st = st.latestStable ∨
      (∃ g, frameStableRoot c e hc (storeToHealing st) (roundOf hc st.s) = some g ∧ stableRec c e hc st = g) := by
  unfold stableRec
  cases hg : frameStableRoot c e hc (storeToHealing st) (roundOf hc st.s) with
  | none => exact Or.inl rfl
  | some g =>
    dsimp only
    rcases advanceConfirmed_cases st.latestStable g with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨g, rfl, h⟩

end Proofs.Consensus.Goldfish
