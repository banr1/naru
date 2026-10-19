import Model.Consensus.Protocol.Handlers
import Model.Consensus.Protocol.Grades
import Model.Consensus.Spec.Interface
import Proofs.Consensus.Carrier
import Proofs.Consensus.Derivation
import Mathlib.Tactic

/-!
# 出力のブロックは tree にある(C71 の補題)

生成 Model の store(`Model/Consensus/Protocol/Store.lean`)の 4 つの欄 — finalized `f`、justified `j`、`latestConfirmed`、
`latestStable` — と、確認の更新が書く `liveConfirmed`(attestation の務めの FG source の起点)は常にブロック木 `tree` の要素である(`TreeInv`)。3 つの出力 `getConfirmed` / `getStable` / `f`
(`Model/Consensus/Spec/Interface.lean` の `outputAt`)はこの 4 つの欄のどれかなので、どの読みも tree の要素(`outputAt_mem`)。
- 書くのは 2 か所だけ: `updateFinality`(ブロックの受理で `f` / `j` を導出した chain 状態 `σ` の値にする。`σ = deriveNamed B` の
  `f` / `j` は受理したブロック `eraseBlock B` の祖先(`Derivation.lean` の `Inv.f_preceq` / `j_preceq`)で、tree は親について閉じている
  (`Carrier.lean` の `named` / `closed`)ので tree の要素)と `updateConfirmationWith`(`latestStable` / `latestConfirmed` を、
  grade の読み(`frameStableRoot` / `frameSgCandidate`: `activePrefix` = filtered tree の `deepest?`)か fork choice `ghost`(anchor か
  tree の子を辿る)か `getFgRoot`(`j` / `f`)か元の値にする。`liveConfirmed` は `ghost` の head か `getFgRoot`)。
- 他のハンドラは 4 つの欄と `liveConfirmed` と tree を変えない(`SameOut`)。初期 store は `{Genesis}` と `Genesis` で成立する。
`NamedStore` → `nodeTick` / `nodeProcess` → world → `readAt` の順に積み上げる(`Carrier.lean` と同じ運び。受理の経路で `StoreInv` が要る)。
手書き `NamedRuntime.readAt_invariants`(`F ∈ T`、`latest_confirmed ∈ T`、`latest_stable ∈ T`。
`DecoupledConsensusProofs/Execution/Runtime.lean`)に当たる。
-/

namespace Proofs.Consensus.Trees

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.ForkChoice.Head Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Tables Proofs.Consensus.NamedBlocks Proofs.Consensus.Blocks
open Proofs.Consensus.Carrier Proofs.Consensus.Derivation Proofs.Consensus.Runs

/-! ## stdlib `Set` の `filter` / `findUnique?` の所属 -/

theorem mem_filter_iff {α : Type} [Ord α] (s : NaruStd.Set α) (p : α → Bool) (z : α) :
    z ∈ (s.filter p).elems ↔ z ∈ s.elems ∧ p z = true :=
  List.mem_filter

/-- `findUnique?` が返す要素は集合の要素で条件を満たす。 -/
theorem findUnique?_mem {α : Type} [Ord α] {s : NaruStd.Set α} {p : α → Bool} {x : α}
    (h : s.findUnique? p = some x) : x ∈ s.elems ∧ p x = true := by
  unfold NaruStd.Set.findUnique? at h
  cases hf : s.elems.filter p with
  | nil =>
    rw [hf] at h
    simp at h
  | cons y ys =>
    cases ys with
    | nil =>
      rw [hf] at h
      simp only [Option.some.injEq] at h
      subst h
      have hmem : y ∈ s.elems.filter p := by
        rw [hf]
        exact List.mem_singleton_self y
      exact List.mem_filter.mp hmem
    | cons z zs =>
      rw [hf] at h
      simp at h

/-! ## fork choice と grade の読みが返すブロック -/

theorem deepest?_mem {t : NaruStd.Set Block} {b : Block} (h : deepest? t = some b) : b ∈ t.elems :=
  (findUnique?_mem h).1

theorem activePrefix_mem {tree : NaruStd.Set Block} {r b : Block} (h : activePrefix tree r = some b) :
    b ∈ tree.elems := by
  unfold activePrefix at h
  exact ((mem_filter_iff _ _ _).mp (deepest?_mem h)).1

theorem viableTree_sub {sigma : NaruStd.Table Block ChainState} {f : Block} {hMax : Nat} {tree : NaruStd.Set Block}
    {b : Block} (h : b ∈ (viableTree sigma f hMax tree).elems) : b ∈ tree.elems := by
  unfold viableTree finalizedDescendants at h
  exact ((mem_filter_iff _ _ _).mp ((mem_filter_iff _ _ _).mp h).1).1

theorem getFilteredBlockTreeFrom_sub {hs : FGStore} {blocks : NaruStd.Set Block} {b : Block}
    (h : b ∈ (getFilteredBlockTreeFrom hs blocks).elems) : b ∈ blocks.elems := by
  unfold getFilteredBlockTreeFrom at h
  exact viableTree_sub ((mem_filter_iff _ _ _).mp h).1

theorem getFilteredBlockTree_sub {hs : FGStore} {b : Block} (h : b ∈ (getFilteredBlockTree hs).elems) :
    b ∈ hs.tree.elems :=
  getFilteredBlockTreeFrom_sub h

theorem ghostStep_mem {tree : NaruStd.Set Block} {score : Block → Nat} {el : Block → Bool} {h c : Block}
    (hc : ghostStep tree score el h = some c) : c ∈ tree.elems := by
  unfold ghostStep argmax? at hc
  exact ((mem_filter_iff _ _ _).mp (findUnique?_mem hc).1).1

/-- `ghostWalk` は出発点を返すか、tree の要素を返す(燃料の帰納法)。 -/
theorem ghostWalk_cases (tree : NaruStd.Set Block) (score : Block → Nat) (el : Block → Bool) :
    ∀ (fuel : Nat) (h : Block), ghostWalk tree score el fuel h = h ∨ ghostWalk tree score el fuel h ∈ tree.elems
  | 0, h => by
    rw [ghostWalk]
    simp
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
      rcases ghostWalk_cases tree score el n c with heq | hmem
      · rw [heq]
        exact Or.inr (ghostStep_mem hstep)
      · exact Or.inr hmem

theorem ghost_cases (anchor : Block) (tree : NaruStd.Set Block) (score : Block → Nat) (el : Block → Bool) :
    ghost anchor tree score el = anchor ∨ ghost anchor tree score el ∈ tree.elems :=
  ghostWalk_cases tree score el _ anchor

theorem getFgRoot_cases (hs : FGStore) : getFgRoot hs = hs.j ∨ getFgRoot hs = hs.f := by
  unfold getFgRoot
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem anchor_cases (e : ProtocolEnv) (hc : HealConfig) (hs : FGStore) (r : Nat) (g1 : Option (Option Block)) :
    Model.Consensus.Protocol.Grades.anchor e hc hs r g1 ∈ hs.tree.elems ∨
      Model.Consensus.Protocol.Grades.anchor e hc hs r g1 = hs.j ∨
      Model.Consensus.Protocol.Grades.anchor e hc hs r g1 = hs.f := by
  unfold Model.Consensus.Protocol.Grades.anchor
  cases g1 with
  | none => exact Or.inr (getFgRoot_cases hs)
  | some g =>
    cases g with
    | none => exact Or.inr (getFgRoot_cases hs)
    | some r' =>
      dsimp only
      cases hap : activePrefix (getFilteredBlockTree hs) r' with
      | some b =>
        simp only [Option.getD_some]
        exact Or.inl (getFilteredBlockTree_sub (activePrefix_mem hap))
      | none =>
        simp only [Option.getD_none]
        exact Or.inr (getFgRoot_cases hs)

theorem getSgRootWith_cases (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (hs : FGStore) (r : Nat) :
    getSgRootWith c e hc hs r ∈ hs.tree.elems ∨ getSgRootWith c e hc hs r = hs.j ∨ getSgRootWith c e hc hs r = hs.f :=
  anchor_cases e hc hs r _

/-- fork choice `ghost`(anchor は grade の読み)の結果は tree の要素(`j` / `f` が tree にあれば)。 -/
theorem ghost_mem {hs : FGStore} (hj : hs.j ∈ hs.tree.elems) (hf : hs.f ∈ hs.tree.elems) (c : Cache) (e : ProtocolEnv)
    (hc : HealConfig) (r : Nat) (score : Block → Nat) (el : Block → Bool) :
    ghost (getSgRootWith c e hc hs r) (getFilteredBlockTree hs) score el ∈ hs.tree.elems := by
  rcases ghost_cases (getSgRootWith c e hc hs r) (getFilteredBlockTree hs) score el with heq | hmem
  · rw [heq]
    rcases getSgRootWith_cases c e hc hs r with h | h | h
    · exact h
    · rw [h]; exact hj
    · rw [h]; exact hf
  · exact getFilteredBlockTree_sub hmem

theorem frameStableRoot_cases {c : Cache} {e : ProtocolEnv} {hc : HealConfig} {hs : FGStore} {r : Nat} {g : Block}
    (h : frameStableRoot c e hc hs r = some g) : g ∈ hs.tree.elems ∨ g = hs.j ∨ g = hs.f := by
  unfold frameStableRoot at h
  split at h
  · rename_i g' hg'
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r', -, hap⟩ := Option.bind_eq_some_iff.mp hg'
    exact Or.inl (getFilteredBlockTree_sub (activePrefix_mem hap))
  · simp only [Option.some.injEq] at h
    subst h
    exact Or.inr (getFgRoot_cases hs)

theorem frameSgCandidate_mem {c : Cache} {e : ProtocolEnv} {hc : HealConfig} {hs : FGStore} {k : Nat} {g : Block}
    (h : frameSgCandidate c e hc hs k = some g) : g ∈ hs.tree.elems := by
  unfold frameSgCandidate at h
  obtain ⟨r, -, hap⟩ := Option.bind_eq_some_iff.mp h
  exact getFilteredBlockTree_sub (activePrefix_mem hap)

theorem advanceConfirmed_mem {T : NaruStd.Set Block} {old cand : Block} (ho : old ∈ T.elems) (hc : cand ∈ T.elems) :
    advanceConfirmed old cand ∈ T.elems := by
  unfold advanceConfirmed
  split_ifs <;> assumption

theorem floorOnStable_mem {T : NaruStd.Set Block} {stable cand old : Block} (hs : stable ∈ T.elems)
    (hc : cand ∈ T.elems) (ho : old ∈ T.elems) : floorOnStable stable cand old ∈ T.elems := by
  unfold floorOnStable
  split_ifs <;> assumption

theorem ite_mem {T : NaruStd.Set Block} {E : Prop} [Decidable E] {A B : Block} (hA : A ∈ T.elems) (hB : B ∈ T.elems) :
    (if E then A else B) ∈ T.elems := by
  split_ifs <;> assumption

/-! ## 祖先について閉じた tree -/

/-- 親について閉じた集合は祖先について閉じている(`b` の構造帰納法)。 -/
theorem ancestor_mem_tree {T : NaruStd.Set Block} (hclosed : ∀ x, x ∈ T.elems → parent x ∈ T.elems) {a : Block} :
    ∀ {b : Block}, preceq a b = true → b ∈ T.elems → a ∈ T.elems
  | Block.Genesis, hab, hb => by
    simp only [preceq, beq_iff_eq] at hab
    subst hab
    exact hb
  | Block.Node p s r v sup ats i, hab, hb => by
    simp only [preceq, Bool.or_eq_true, beq_iff_eq] at hab
    rcases hab with rfl | hab
    · exact hb
    · exact ancestor_mem_tree hclosed hab (hclosed _ hb)

/-- store の不変条件(`Carrier.lean`)から、tree は親について閉じている。 -/
theorem tree_closed {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st) :
    ∀ x, x ∈ st.core.tree.elems → parent x ∈ st.core.tree.elems := by
  intro x hx
  obtain ⟨D, hD, rfl⟩ := h.named x hx
  rw [parent_eraseBlock]
  exact h.tree _ (h.closed D hD)

/-- 重複のないリストに、含まれない要素を `insertSorted` で入れても重複は無い(並びの昇順は使わない)。 -/
theorem nodup_insertSorted {α : Type} [Ord α] (heq : ∀ a b : α, compare a b = .eq ↔ a = b) (x : α) :
    ∀ {l : List α}, l.Nodup → x ∉ l → (NaruStd.Set.insertSorted x l).Nodup
  | [], _, _ => List.nodup_singleton x
  | y :: ys, hnd, hx => by
    obtain ⟨hy, hys⟩ := List.nodup_cons.mp hnd
    cases hc : compare x y with
    | lt =>
      simp only [NaruStd.Set.insertSorted, hc]
      exact List.nodup_cons.mpr ⟨hx, hnd⟩
    | eq =>
      simp only [NaruStd.Set.insertSorted, hc]
      exact hnd
    | gt =>
      simp only [NaruStd.Set.insertSorted, hc]
      refine List.nodup_cons.mpr ⟨?_, nodup_insertSorted heq x hys fun h => hx (List.mem_cons_of_mem y h)⟩
      rw [mem_insertSorted heq]
      rintro (rfl | h)
      · exact hx (List.mem_cons_self ..)
      · exact hy h

/-! ## 不変条件 -/

/-- 出力の元になる 4 つの欄と `liveConfirmed` は tree の要素。 -/
structure TreeInv (st : Store) : Prop where
  f : st.f ∈ st.tree.elems
  j : st.j ∈ st.tree.elems
  confirmed : st.latestConfirmed ∈ st.tree.elems
  stable : st.latestStable ∈ st.tree.elems
  /-- `liveConfirmed`(確認の更新が書く fork choice の読み。grade の読みと attestation の務めの FG source の `deepestClear` の起点)も tree の要素。 -/
  live : st.liveConfirmed ∈ st.tree.elems
  /-- tree の表現のリストに重複は無い(`activePrefix` は `findUnique?` で読むので要る。周回 233)。 -/
  nodup : st.tree.elems.Nodup

/-- tree と 4 つの欄と `liveConfirmed` が等しい。 -/
structure SameOut (a b : Store) : Prop where
  tree : a.tree = b.tree
  f : a.f = b.f
  j : a.j = b.j
  confirmed : a.latestConfirmed = b.latestConfirmed
  stable : a.latestStable = b.latestStable
  live : a.liveConfirmed = b.liveConfirmed

theorem SameOut.refl (a : Store) : SameOut a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameOut.trans {a b c : Store} (h1 : SameOut a b) (h2 : SameOut b c) : SameOut a c :=
  ⟨h1.tree.trans h2.tree, h1.f.trans h2.f, h1.j.trans h2.j, h1.confirmed.trans h2.confirmed, h1.stable.trans h2.stable,
   h1.live.trans h2.live⟩

theorem TreeInv.congr {st : Store} (h : TreeInv st) {st' : Store} (hs : SameOut st' st) : TreeInv st' :=
  ⟨by rw [hs.f, hs.tree]; exact h.f, by rw [hs.j, hs.tree]; exact h.j,
   by rw [hs.confirmed, hs.tree]; exact h.confirmed, by rw [hs.stable, hs.tree]; exact h.stable,
   by rw [hs.live, hs.tree]; exact h.live, by rw [hs.tree]; exact h.nodup⟩

theorem initial_treeInv : TreeInv initStore :=
  ⟨(mem_singleton_iff _ _).mpr rfl, (mem_singleton_iff _ _).mpr rfl, (mem_singleton_iff _ _).mpr rfl,
   (mem_singleton_iff _ _).mpr rfl, (mem_singleton_iff _ _).mpr rfl, List.nodup_singleton _⟩

/-! ## `Store` のハンドラ -/

theorem onGoldfishVote_out (st : Store) (u : GoldfishVote) : SameOut (onGoldfishVote st u) st := by
  unfold onGoldfishVote
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem onGoldfishVoteChecked_out (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    SameOut (onGoldfishVoteChecked c st u) st := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact SameOut.refl _
  · exact onGoldfishVote_out st u

theorem foldl_out {β : Type} (g : Store → β → Store) (hg : ∀ s x, SameOut (g s x) s) :
    ∀ (l : List β) (s : Store), SameOut (List.foldl g s l) s
  | [], _ => SameOut.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (foldl_out g hg l _).trans (hg s x)

theorem onSgVote_out (hc : HealConfig) (st : Store) (a : CombinedAttestation) : SameOut (onSgVote hc st a) st := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem goldfishVoteWith_out (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : Store) : SameOut (goldfishVoteWith c cache e hc nd st).1 st := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_out c st _
  · exact SameOut.refl _

/-- `updateFinality` は tree / latestConfirmed / latestStable を変えず、`f` / `j` は元のままか `σ` の値。 -/
theorem updateFinality_out (st : Store) (σ : ChainState) :
    (updateFinality st σ).tree = st.tree ∧
      ((updateFinality st σ).f = st.f ∨ (updateFinality st σ).f = σ.f) ∧
      ((updateFinality st σ).j = st.j ∨ (updateFinality st σ).j = σ.j) ∧
      (updateFinality st σ).latestConfirmed = st.latestConfirmed ∧
      (updateFinality st σ).latestStable = st.latestStable := by
  unfold updateFinality
  dsimp only
  split_ifs <;>
    exact ⟨rfl, by first | exact Or.inl rfl | exact Or.inr rfl, by first | exact Or.inl rfl | exact Or.inr rfl, rfl, rfl⟩

theorem storedOf_out (st : Store) (b : Block) (post : ChainState) :
    (storedOf st b post).f = st.f ∧ (storedOf st b post).j = st.j ∧
      (storedOf st b post).latestConfirmed = st.latestConfirmed ∧ (storedOf st b post).latestStable = st.latestStable :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem unpackedOf_out (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    SameOut (unpackedOf c st b post) (storedOf st b post) :=
  foldl_out _ (fun s u => onGoldfishVoteChecked_out c s u) _ _

theorem updateFinality_live (st : Store) (σ : ChainState) : (updateFinality st σ).liveConfirmed = st.liveConfirmed := by
  unfold updateFinality
  dsimp only
  split_ifs <;> rfl

/-- 受理の分岐は `liveConfirmed` を変えない。 -/
theorem acceptBody_live (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    (acceptBody c st b post).liveConfirmed = st.liveConfirmed :=
  (updateFinality_live _ _).trans (unpackedOf_out c st b post).live

/-- 受理の分岐の結果: tree に `b` が入り、`f` / `j` は元のままか `post` の値、latestConfirmed / latestStable は不変。 -/
theorem acceptBody_out (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    (acceptBody c st b post).tree = st.tree.insert b ∧
      ((acceptBody c st b post).f = st.f ∨ (acceptBody c st b post).f = post.f) ∧
      ((acceptBody c st b post).j = st.j ∨ (acceptBody c st b post).j = post.j) ∧
      (acceptBody c st b post).latestConfirmed = st.latestConfirmed ∧
      (acceptBody c st b post).latestStable = st.latestStable := by
  have hσ : chainStateOf (unpackedOf c st b post).sigma b = post := by
    unfold chainStateOf
    rw [(unpackedOf_same c st b post).sigma]
    show NaruStd.Table.getOr (st.sigma.insert b post) b initialChainState = post
    rw [getOr_insert_self block_compare_eq_iff]
  obtain ⟨htree, hf, hj, hc, hs⟩ := updateFinality_out (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)
  have hu := unpackedOf_out c st b post
  obtain ⟨sf, sj, sc, ss⟩ := storedOf_out st b post
  refine ⟨acceptBody_tree c st b post, ?_, ?_, ?_, ?_⟩
  · show (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).f = st.f ∨
      (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).f = post.f
    rcases hf with hf | hf
    · exact Or.inl (hf.trans (hu.f.trans sf))
    · exact Or.inr (hf.trans (congrArg ChainState.f hσ))
  · show (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).j = st.j ∨
      (updateFinality (unpackedOf c st b post) (chainStateOf (unpackedOf c st b post).sigma b)).j = post.j
    rcases hj with hj | hj
    · exact Or.inl (hj.trans (hu.j.trans sj))
    · exact Or.inr (hj.trans (congrArg ChainState.j hσ))
  · exact hc.trans (hu.confirmed.trans sc)
  · exact hs.trans (hu.stable.trans ss)

/-- 受理の分岐は不変条件を保つ(`b` がまだ tree に無く、受理後の tree が親について閉じていて、`post` の `f` / `j` が `b` の祖先なら)。 -/
theorem acceptBody_treeInv (c : Nat → NaruStd.Set ValidatorId) {st : Store} (h : TreeInv st) {b : Block} {post : ChainState}
    (hnotin : b ∉ st.tree.elems) (hclosed : ∀ x, x ∈ (st.tree.insert b).elems → parent x ∈ (st.tree.insert b).elems)
    (hf : preceq post.f b = true) (hj : preceq post.j b = true) : TreeInv (acceptBody c st b post) := by
  obtain ⟨htree, hf', hj', hc', hs'⟩ := acceptBody_out c st b post
  have hsub : ∀ x, x ∈ st.tree.elems → x ∈ (acceptBody c st b post).tree.elems := fun x hx => by
    rw [htree, mem_insert_iff block_compare_eq_iff]
    exact Or.inr hx
  have hb : b ∈ (acceptBody c st b post).tree.elems := by
    rw [htree, mem_insert_iff block_compare_eq_iff]
    exact Or.inl rfl
  have hclosed' : ∀ x, x ∈ (acceptBody c st b post).tree.elems → parent x ∈ (acceptBody c st b post).tree.elems := by
    rw [htree]
    exact hclosed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hf' with hf' | hf'
    · rw [hf']; exact hsub _ h.f
    · rw [hf']; exact ancestor_mem_tree hclosed' hf hb
  · rcases hj' with hj' | hj'
    · rw [hj']; exact hsub _ h.j
    · rw [hj']; exact ancestor_mem_tree hclosed' hj hb
  · rw [hc']; exact hsub _ h.confirmed
  · rw [hs']; exact hsub _ h.stable
  · rw [acceptBody_live]; exact hsub _ h.live
  · rw [htree]
    exact nodup_insertSorted block_compare_eq_iff b h.nodup hnotin

/-- 確認の更新は 4 つの欄と `liveConfirmed` を tree の要素に保つ(`frameStableRoot` / `frameSgCandidate` / `ghost` / `getFgRoot` の結果の分類)。 -/
theorem updateConfirmationWith_treeInv (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) {st : Store} (h : TreeInv st)
    (k : Nat) : TreeInv (updateConfirmationWith cache e hc st k) := by
  have hstable : (match frameStableRoot cache e hc (storeToHealing st) (roundOf hc st.s) with
      | some g => advanceConfirmed st.latestStable g
      | none => st.latestStable) ∈ st.tree.elems := by
    cases hfs : frameStableRoot cache e hc (storeToHealing st) (roundOf hc st.s) with
    | some g =>
      dsimp only
      refine advanceConfirmed_mem h.stable ?_
      rcases frameStableRoot_cases hfs with hg | hg | hg
      · exact hg
      · rw [hg]; exact h.j
      · rw [hg]; exact h.f
    | none =>
      dsimp only
      exact h.stable
  unfold updateConfirmationWith
  dsimp only
  refine ⟨h.f, h.j, ?_, hstable, ?_, h.nodup⟩
  swap
  · apply ite_mem (ghost_mem h.j h.f cache e hc (roundOf hc st.s) _ _)
    rcases getFgRoot_cases (storeToHealing st) with hr | hr
    · rw [hr]; exact h.j
    · rw [hr]; exact h.f
  apply floorOnStable_mem hstable _ h.confirmed
  apply ite_mem
  · exact advanceConfirmed_mem h.confirmed (ghost_mem h.j h.f cache e hc (roundOf hc st.s) _ _)
  · cases hcand : frameSgCandidate cache e hc (storeToHealing st) k with
    | some cand =>
      dsimp only
      exact advanceConfirmed_mem h.confirmed (frameSgCandidate_mem hcand)
    | none =>
      dsimp only
      exact h.confirmed

/-! ## `NamedStore` のハンドラ -/

/-- `processBlockCore` は不変条件を保つ(受理の経路で `StoreInv` を使う。`Carrier.processBlockCore_inv` と同じ場合分け)。 -/
theorem processBlockCore_treeInv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (hc : HealConfig) {st : NamedStore} (hinv : StoreInv e cfg st) (h : TreeInv st.core)
    (B : NamedBlock) : TreeInv (processBlockCore c p e hc cfg st B).core := by
  have hinv' := processBlockCore_inv c p hc hinv B
  have hclosed := tree_closed hinv'
  revert hclosed
  unfold processBlockCore
  split_ifs with hpar
  · intro _
    exact h
  · have hparent : namedParent B ∈ st.bodies.elems := by
      rw [← contains_iff_mem nb_compare_eq_iff]
      cases hcp : st.bodies.contains (namedParent B) with
      | true => rfl
      | false => exact absurd (by simp [hcp]) hpar
    dsimp only
    rcases onBlockCheckedUsing_eq (fun cur => onBlockUsing c p cur (eraseBlock B)
        (fun ps => namedTransition e cfg ps B)) hc st.core (eraseBlock B) with hafter | hafter
    · rw [hafter]
      rcases onBlockUsing_eq c p st.core (eraseBlock B) (fun ps => namedTransition e cfg ps B)
          with hb | ⟨hnb, _, hb⟩
      · rw [hb, commitBlock_self]
        intro _
        exact h
      · rw [hb]
        have hpost : namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B =
            deriveNamed e cfg B := by
          rw [parent_eraseBlock, hinv.sigma _ hparent]
          cases B with
          | Genesis => exact absurd (hinv.tree _ hparent) hnb
          | Node p s r v sup rows i => rfl
        show (∀ x, x ∈ (commitBlock st (acceptBody c st.core (eraseBlock B)
            (namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B)) B).core.tree.elems →
            parent x ∈ (commitBlock st (acceptBody c st.core (eraseBlock B)
            (namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B)) B).core.tree.elems) →
          TreeInv (commitBlock st (acceptBody c st.core (eraseBlock B)
            (namedTransition e cfg (chainStateOf st.core.sigma (parent (eraseBlock B))) B)) B).core
        rw [hpost]
        have hnotin : st.core.tree.contains (eraseBlock B) = false := by
          cases hx : st.core.tree.contains (eraseBlock B) with
          | false => rfl
          | true => exact absurd ((contains_iff_mem block_compare_eq_iff _ _).mp hx) hnb
        have hin : (acceptBody c st.core (eraseBlock B) (deriveNamed e cfg B)).tree.contains (eraseBlock B) = true := by
          rw [contains_iff_mem block_compare_eq_iff, acceptBody_tree, mem_insert_iff block_compare_eq_iff]
          exact Or.inl rfl
        rw [commitBlock_accept hnotin hin]
        intro hclosed
        have hclosed' : ∀ x, x ∈ (st.core.tree.insert (eraseBlock B)).elems →
            parent x ∈ (st.core.tree.insert (eraseBlock B)).elems := by
          have hc' := hclosed
          simp only [acceptBody_tree] at hc'
          exact hc'
        exact acceptBody_treeInv c h hnb hclosed' (deriveNamed_inv e cfg B).f_preceq (deriveNamed_inv e cfg B).j_preceq
    · rw [hafter, commitBlock_self]
      intro _
      exact h

theorem admitRow_treeInv (hc : HealConfig) {st : NamedStore} (h : TreeInv st.core) (row : NamedAttestation) :
    TreeInv (admitRow hc st row).core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact h.congr (onSgVote_out hc st.core _)

theorem admitRows_treeInv (hc : HealConfig) :
    ∀ (rows : List NamedAttestation) {st : NamedStore}, TreeInv st.core → TreeInv (admitRows hc st rows).core
  | [], _, h => h
  | row :: rows, st, h => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_treeInv hc rows (admitRow_treeInv hc h row)
    unfold admitRows at ih
    exact ih

theorem admitCarried_treeInv (adm : CarriedAdmission) (hc : HealConfig) (before : NamedStore) {after : NamedStore}
    (h : TreeInv after.core) (b : NamedBlock) : TreeInv (admitCarried adm hc before after b).core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_treeInv hc _ h
  · exact h

theorem onBlockWith_treeInv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (adm : CarriedAdmission) (hc : HealConfig) {st : NamedStore} (hinv : StoreInv e cfg st)
    (h : TreeInv st.core) (b : NamedBlock) : TreeInv (onBlockWith c p adm e hc cfg st b).core := by
  unfold onBlockWith
  exact admitCarried_treeInv adm hc st (processBlockCore_treeInv c p hc hinv h b) b

theorem receiptProcess_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} (hinv : StoreInv s.e s.cfg st) (h : TreeInv st.core)
    (o : Model.Consensus.Execution.Objects.NamedObject) : TreeInv (receiptProcess c p s st o).core := by
  cases o with
  | Block b => exact onBlockWith_treeInv c p _ _ hinv h b
  | GfVote u =>
    show TreeInv { st with core := onGoldfishVoteChecked c st.core u }.core
    exact h.congr (onGoldfishVoteChecked_out c st.core u)
  | Attest a =>
    show TreeInv (admitRow s.hc st a).core
    exact admitRow_treeInv s.hc h a

theorem nodeProcess_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (hinv : StoreInv s.e s.cfg n.st)
    (h : TreeInv n.st.core) (o : Model.Consensus.Execution.Objects.NamedObject) :
    TreeInv (nodeProcess c p s n o).st.core :=
  receiptProcess_treeInv c p s hinv h o

/-! ## Tick の務め -/

theorem proposeBlockWith_treeInv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId) (cache : Cache) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (hinv : StoreInv e cfg st) (h : TreeInv st.core) :
    TreeInv (proposeBlockWith c p nr cache e hc cfg nd st).1.core := by
  unfold proposeBlockWith
  split
  · exact h
  · rename_i b _
    exact onBlockWith_treeInv c p CarriedAdmission.AlsoCarried hc hinv h b

theorem namedGoldfishVoteWith_treeInv (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {e : ProtocolEnv} {st : NamedStore} (h : TreeInv st.core) :
    TreeInv (namedGoldfishVoteWith c cache e hc nd st).1.core := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show TreeInv { st with core := core }.core
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  refine h.congr ?_
  show SameOut core st.core
  rw [h1]
  exact goldfishVoteWith_out c cache e hc nd st.core

theorem namedUpdateConfirmationWith_treeInv (cache : Cache) (hc : HealConfig) {e : ProtocolEnv} {st : NamedStore}
    (h : TreeInv st.core) (k : Nat) : TreeInv (namedUpdateConfirmationWith cache e hc st k).core :=
  updateConfirmationWith_treeInv cache e hc h k

theorem attestWith_treeInv (cache : Cache) (hc : HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {e : ProtocolEnv} {st : NamedStore} (h : TreeInv st.core) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    TreeInv (attestWith cache e hc nd st rec).1.core := by
  unfold attestWith
  split
  exact admitRow_treeInv hc h _

/-- 1 tick の務めは不変条件を保つ(`Carrier.tick_inv` と同じ 16 経路)。 -/
theorem tick_treeInv {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (cache : Cache) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (hinv : StoreInv e cfg st) (h : TreeInv st.core)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    TreeInv (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  have hinv0 : StoreInv e cfg { st with core := { st.core with t := t, s := slotOf e t } } :=
    hinv.congr rfl ⟨rfl, rfl, rfl⟩
  have h0 : TreeInv { st with core := { st.core with t := t, s := slotOf e t } }.core :=
    h.congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact attestWith_treeInv cache hc nd (namedUpdateConfirmationWith_treeInv cache hc (namedGoldfishVoteWith_treeInv c cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0)) _) _
    | with_reducible exact attestWith_treeInv cache hc nd (namedUpdateConfirmationWith_treeInv cache hc (namedGoldfishVoteWith_treeInv c cache hc nd h0) _) _
    | with_reducible exact attestWith_treeInv cache hc nd (namedUpdateConfirmationWith_treeInv cache hc (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0) _) _
    | with_reducible exact attestWith_treeInv cache hc nd (namedUpdateConfirmationWith_treeInv cache hc h0 _) _
    | with_reducible exact attestWith_treeInv cache hc nd (namedGoldfishVoteWith_treeInv c cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0)) _
    | with_reducible exact attestWith_treeInv cache hc nd (namedGoldfishVoteWith_treeInv c cache hc nd h0) _
    | with_reducible exact attestWith_treeInv cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0) _
    | with_reducible exact attestWith_treeInv cache hc nd h0 _
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc (namedGoldfishVoteWith_treeInv c cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0)) _
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc (namedGoldfishVoteWith_treeInv c cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0) _
    | with_reducible exact namedUpdateConfirmationWith_treeInv cache hc h0 _
    | with_reducible exact namedGoldfishVoteWith_treeInv c cache hc nd (proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0)
    | with_reducible exact namedGoldfishVoteWith_treeInv c cache hc nd h0
    | with_reducible exact proposeBlockWith_treeInv c p nr cache hc nd hinv0 h0
    | with_reducible exact h0

theorem nodeTick_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    {n : NamedNodeState} (hinv : StoreInv s.e s.cfg n.st) (h : TreeInv n.st.core) (t : Int) :
    TreeInv (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_treeInv c p a nr _ s.hc _ hinv h n.signing t

/-! ## world -/

/-- world のどのノードの store も 4 つの欄と `liveConfirmed` が tree にある。 -/
def WorldTreeInv (w : NamedWorld) : Prop := ∀ v, TreeInv (worldAt w v).st.core

theorem worldInit_treeInv : WorldTreeInv worldInit := fun _ => initial_treeInv

theorem worldStep_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) {w : NamedWorld}
    (hinv : WorldInv s.e s.cfg w) (h : WorldTreeInv w) (ev : NamedEvent) : WorldTreeInv (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_treeInv c p a nr s u (hinv u) (h u) t
    · rw [hw]
      exact h v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_treeInv c p s (hinv u) (h u) o
    · rw [hw]
      exact h v

theorem foldl_worldStep_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, WorldInv s.e s.cfg w → WorldTreeInv w →
      WorldTreeInv (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, _, h => h
  | ev :: l, _, hinv, h => by
    rw [List.foldl_cons]
    exact foldl_worldStep_treeInv c p a nr s l (worldStep_inv c p a nr s hinv ev) (worldStep_treeInv c p a nr s hinv h ev)

/-- 時刻 `t` の読みのどのノードでも 4 つの欄と `liveConfirmed` は tree にある。 -/
theorem readAt_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t : Int) :
    WorldTreeInv (readAt c p a nr s rho t) := by
  unfold readAt
  exact foldl_worldStep_treeInv c p a nr s _ (worldInit_inv s.e s.cfg) worldInit_treeInv

/-- 添字 `i` の直前の world のどのノードでも 4 つの欄と `liveConfirmed` は tree にある。 -/
theorem stateBefore_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (i : Nat) :
    WorldTreeInv (stateBefore c p a nr s rho i) := by
  unfold stateBefore
  exact foldl_worldStep_treeInv c p a nr s _ (worldInit_inv s.e s.cfg) worldInit_treeInv

/-- 時刻 `t` より前の event を畳んだ world のどのノードでも 4 つの欄と `liveConfirmed` は tree にあり、tree に重複は無い
(event の整列を要らない。周回 279)。 -/
theorem stateBeforeTime_treeInv (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t : Int) :
    WorldTreeInv (stateBeforeTime c p a nr s rho t) := by
  unfold stateBeforeTime
  exact foldl_worldStep_treeInv c p a nr s _ (worldInit_inv s.e s.cfg) worldInit_treeInv

/-! ## 3 つの出力 -/

theorem getStable_mem {st : Store} (h : TreeInv st) : getStable st ∈ st.tree.elems := by
  unfold getStable
  split_ifs
  · exact h.stable
  · exact h.f

theorem getConfirmed_mem {st : Store} (h : TreeInv st) : getConfirmed st ∈ st.tree.elems := by
  unfold getConfirmed
  split_ifs
  · exact h.confirmed
  · exact getStable_mem h

/-- どの出力の読みもその store の tree の要素。 -/
theorem outputAt_mem (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (g : Model.Consensus.Spec.Interface.Output)
    (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (v : ValidatorId) (t : Int) :
    Model.Consensus.Spec.Interface.outputAt c p a nr g s rho v t ∈ (storeAt c p a nr s rho v t).core.tree.elems := by
  have h := readAt_treeInv c p a nr s rho t v
  cases g with
  | Confirmed => exact getConfirmed_mem h
  | Stable => exact getStable_mem h
  | Finalized => exact h.f

end Proofs.Consensus.Trees
