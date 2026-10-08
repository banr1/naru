import DecoupledConsensusModel.Protocol.Tick
import DecoupledConsensusModel.Protocol.Evidence
import DecoupledConsensusModel.Execution.Instance
open DecoupledConsensusModel DecoupledConsensusModel.Protocol

-- 手書き Model の同じ値(tests/golden/protocol_generated.lean と同じ順)。golden test の予行(周回 6〜10)。
-- 実行: cd verified-consensus && lake env lean ../tests/golden/protocol_handwritten.lean(Model の全層(Protocol / Execution / Generic)の olean がビルド済みであること)

def el : Electorate (Fin 3) := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by decide }
def env : Env (Fin 3) :=
  { Δ := 2, Δ_pos := by decide, t_GST := 0, t_GST_nonneg := by decide,
    proposer := fun _ => 0, committees := ⟨fun _ => {0}⟩, electorate := el }

def vA : GoldfishVote (Fin 3) := ⟨0, 1, ⟨1⟩⟩
def vB : GoldfishVote (Fin 3) := ⟨1, 1, ⟨1⟩⟩
def vC : GoldfishVote (Fin 3) := ⟨0, 1, ⟨0⟩⟩
def vD : GoldfishVote (Fin 3) := ⟨2, 1, ⟨99⟩⟩
def vE : GoldfishVote (Fin 3) := ⟨1, 2, ⟨1⟩⟩
def vF : GoldfishVote (Fin 3) := ⟨1, 1, ⟨2⟩⟩

def g : Block (Fin 3) := .genesis
def b1 : Block (Fin 3) := .node g 1 ⟨1⟩ [] [] [] 0
def b1' : Block (Fin 3) := .node g 1 ⟨5⟩ [] [] [] 1
def b2 : Block (Fin 3) := .node b1 2 ⟨2⟩ [vA, vB] [vA] [] 0
def b2' : Block (Fin 3) := .node b1 2 ⟨3⟩ [vB, vF, vE] [vF] [] 1
def b3 : Block (Fin 3) := .node b2 3 ⟨4⟩ [vE] [vA] [] 0

def st : GoldfishStore (Fin 3) :=
  { t := 16, s := 2, T := {g, b1, b1', b2, b2', b3},
    timestamp_block := fun B =>
      if B = g then some ⊥ else if B = b1 then some ((5 : Time) : Stamp) else if B = b1' then some ((30 : Time) : Stamp)
      else if B = b2 then some ((9 : Time) : Stamp) else if B = b2' then some ((20 : Time) : Stamp)
      else if B = b3 then some ((10 : Time) : Stamp) else none,
    timestamp_vote := fun v =>
      if v = vA then some ((6 : Time) : Stamp) else if v = vB then some ((12 : Time) : Stamp)
      else if v = vC then some ((7 : Time) : Stamp) else if v = vD then some ((6 : Time) : Stamp) else none,
    gf_votes := fun k => if k = 1 then [vA, vB, vC, vD] else if k = 2 then [vE] else [],
    live_confirmed := g, latest_confirmed := g }

def pool1 := st.pool 1

#eval equivocates pool1 0
#eval equivocates pool1 1
#eval participates pool1 2
#eval (votes_by pool1 0).card
#eval (proposal_time env 3, vote_time env 3, support_cutoff env 3, view_freeze env 3, confirmation_time env 3)
#eval vote_well_formed env vA
#eval vote_well_formed env vB
#eval (carried_votes_well_formed b2, carried_votes_well_formed b2', carried_votes_well_formed b3, carried_votes_well_formed g)
#eval (carried_support_well_formed b2, carried_support_well_formed b2', carried_support_well_formed b3)

#eval (resolved st.T vA, resolved st.T vD, resolved st.T vF, resolved st.T ⟨0, 3, ⟨2⟩⟩, resolved st.T vE)
#eval resolution_time st.T st.timestamp_block st.timestamp_vote vA == some ((6 : Time) : Stamp)
#eval resolution_time st.T st.timestamp_block st.timestamp_vote vC == some ((7 : Time) : Stamp)
#eval (resolution_time st.T st.timestamp_block st.timestamp_vote vD).isNone
#eval (resolution_time st.T st.timestamp_block st.timestamp_vote vF).isNone
#eval (resolution_time st.T st.timestamp_block st.timestamp_vote vE).isNone
#eval decide (pool1 = {vA, vB, vC, vD})
#eval (st.pool 5).card
#eval st.tau vB == some ((12 : Time) : Stamp)

#eval decide (voter_view env st 2 = {vA, vB, vC, vD, vF})
#eval (voter_view env st 2).card
#eval decide (voter_support_view env st 2 = {vA, vB, vC})
#eval decide (voter_processed_block_tree env st 2 = {g, b1, b2, b2', b3})
#eval (voter_processed_block_tree env st 2).card
#eval proposer_view st 2 == [vA, vB, vC, vD]
#eval proposer_support_view st 2 == [vA, vB, vC]
#eval decide (voter_view env st 3 = {vE})
#eval (voter_support_view env st 3) = ∅

def w0 : GoldfishVote (Fin 3) := ⟨0, 2, ⟨2⟩⟩
def w1 : GoldfishVote (Fin 3) := ⟨1, 2, ⟨3⟩⟩
def w1' : GoldfishVote (Fin 3) := ⟨1, 2, ⟨2⟩⟩
def w2 : GoldfishVote (Fin 3) := ⟨2, 2, ⟨2⟩⟩
def wv : Finset (GoldfishVote (Fin 3)) := {w0, w1, w1', w2}
def tree := st.T
def score : Block (Fin 3) → Nat := fun b => goldfish_score env tree wv wv 2 b
def rootOf (b : Block (Fin 3)) : Nat := b.root.value
#eval (decide (raw_equivocators wv = {1}), decide (raw_participants wv = {0, 1, 2}), voters_count env wv 2)
#eval (score g, score b1, score b1', score b2, score b2', score b3)
#eval (targets_under tree b1 w0, targets_under tree b3 w0, targets_under tree b2 vD)
#eval (outranks score b2 b2', outranks score b2' b2, outranks score b1 b1')
#eval (argmax? score {b2, b2'}).map rootOf
#eval (argmax? score (∅ : Finset (Block (Fin 3)))).isNone
def tieScore : Block (Fin 3) → Nat := fun b => goldfish_score env tree {w1, w2} {w1, w2} 2 b
#eval (tieScore b2, tieScore b2', (argmax? tieScore {b2, b2'}).map rootOf)
#eval decide (ghost_children tree (fun _ => true) b1 = {b2, b2'})
#eval decide (ghost_children tree (fun b => b.root != ⟨3⟩) b1 = {b2})
#eval (ghost_step tree score (fun _ => true) g).map rootOf
#eval rootOf (ghost g tree score (fun _ => true))
#eval rootOf (ghost g tree score (fun b => decide (2 ≤ score b)))
#eval rootOf (ghost b2' tree score (fun _ => true))
#eval rootOf (ghost_walk tree score (fun _ => true) 1 g)
#eval (no_second_vote_in wv w0, no_second_vote_in wv w1)
#eval (latest_window 3 5, latest_window 3 2, latest_window 3 0)
#eval (decide ((⟨1, ⟨5⟩⟩ : HeightId) < ⟨2, ⟨0⟩⟩), decide ((⟨2, ⟨1⟩⟩ : HeightId) > ⟨2, ⟨0⟩⟩))
#eval decide (finalized_descendants b1 tree = {b1, b2, b2', b3})

-- ChainState (周回 7)
def fp1 : FinalityPair := ⟨2, ⟨7⟩⟩
#eval (conflictsWithFinality .empty fp1, conflictsWithFinality (.timeout 2) fp1,
       conflictsWithFinality (.target 2 ⟨7⟩) fp1, conflictsWithFinality (.target 2 ⟨8⟩) fp1,
       conflictsWithFinality (.timeout 3) fp1)
def a0 : CombinedAttestation (Fin 3) := ⟨0, 1, some ⟨1⟩, .target 2 ⟨7⟩, some ⟨2, ⟨7⟩⟩⟩
def a1 : CombinedAttestation (Fin 3) := ⟨0, 1, some ⟨2⟩, .target 2 ⟨8⟩, none⟩
def a2 : CombinedAttestation (Fin 3) := ⟨1, 1, some ⟨1⟩, .timeout 2, some ⟨2, ⟨7⟩⟩⟩
def a3 : CombinedAttestation (Fin 3) := ⟨0, 2, some ⟨2⟩, .target 3 ⟨9⟩, none⟩
#eval (e1Slashable a0 a1, e2Slashable a0 a1, slashable a0 a1, selfSlashable a0, selfSlashable a2, e1Slashable a0 a2, e2Slashable a0 a3)
#eval (sgHeadEquivocation a0 a1, sgHeadEquivocation a0 a3, sgHeadEquivocation a0 a0)

def cfg : HeightConfig := ⟨4, 2, 1, by decide, by decide⟩
def σ0 : ChainState (Fin 3) := ChainState.initial
#eval (σ0.h, σ0.h_j, σ0.h_F, σ0.nj, rootOf σ0.L, rootOf σ0.T_h, rootOf σ0.J, rootOf σ0.F, σ0.s, σ0.target_participation.card)
#eval (nonjustifiable cfg 4 0, nonjustifiable cfg 4 2, nonjustifiable cfg 5 0, nonjustifiable cfg 8 5, nonjustifiable cfg 8 6)
def σA : ChainState (Fin 3) := { σ0 with target_participation := {0, 1}, progress := {1, 2}, finalize := {0} }
#eval (σA.targetQuorum env, σA.progQuorum env, σA.finalityQuorum env)

def σB : ChainState (Fin 3) := { σ0 with h := 2, T_h := b1, h_j := 1, J := g, h_F := 0, s := 2, L := b1 }
def t0 : CombinedAttestation (Fin 3) := ⟨0, 1, none, .target 2 ⟨1⟩, some ⟨1, ⟨0⟩⟩⟩
def t1 : CombinedAttestation (Fin 3) := ⟨1, 1, none, .timeout 2, some ⟨1, ⟨5⟩⟩⟩
def t2 : CombinedAttestation (Fin 3) := ⟨2, 1, none, .target 3 ⟨1⟩, none⟩
def t3 : CombinedAttestation (Fin 3) := ⟨2, 1, none, .empty, some ⟨1, ⟨0⟩⟩⟩
def r0 := process_attestation σB t0
def r1 := process_attestation r0 t1
def r2 := process_attestation r1 t2
def r3 := process_attestation r2 t3
#eval (r0.target_participation.card, r0.progress.card, r0.finalize.card)
#eval (r1.target_participation.card, r1.progress.card, r1.finalize.card)
#eval decide (r2 = r1)
#eval (decide (r3.target_participation = {0}), decide (r3.progress = {0, 1}), decide (r3.finalize = {0, 2}))

def p3 := process_height_events env cfg r3
#eval (p3.h, p3.h_j, p3.h_F, rootOf p3.J, rootOf p3.F, rootOf p3.T_h, p3.nj, p3.finalize.card, p3.target_participation.card, p3.progress.card)
def p3' := process_height_events env cfg { r3 with s := 1 }
#eval (p3'.h, p3'.h_F, p3'.progress.card)
def p4 := process_height_events env cfg { r3 with target_participation := {0, 1} }
#eval (p4.h, p4.h_j, p4.h_F, rootOf p4.J, rootOf p4.F, p4.finalize.card, p4.nj)
def σE : ChainState (Fin 3) := { σB with h := 3, target_participation := {0, 1} }
def p5 := process_height_events env cfg σE
#eval (p5.h, p5.nj, p5.h_j)
def p6 := process_height_events env cfg { p5 with target_participation := {0, 1}, progress := {0, 1}, s := 5 }
#eval (p6.h, p6.h_j, p6.nj)

def n0 : NamedAttestation (Fin 3) := ⟨0, 0, none, .vote 1 ⟨0⟩ false, none⟩
def n1 : NamedAttestation (Fin 3) := ⟨1, 0, none, .vote 1 ⟨0⟩ false, none⟩
def nb1 : NamedBlock (Fin 3) := .node .genesis 1 ⟨1⟩ [] [] [n0, n1] 0
def m0 : NamedAttestation (Fin 3) := ⟨0, 1, none, .vote 2 ⟨1⟩ false, some ⟨1, ⟨0⟩⟩⟩
def m1 : NamedAttestation (Fin 3) := ⟨1, 1, none, .vote 2 ⟨1⟩ true, some ⟨1, ⟨0⟩⟩⟩
def m2 : NamedAttestation (Fin 3) := ⟨2, 1, none, .vote 2 ⟨5⟩ false, none⟩
def nb2 : NamedBlock (Fin 3) := .node nb1 2 ⟨2⟩ [] [] [m0, m1, m2] 1
def d1 := derive_named env cfg nb1
#eval (d1.h, d1.h_j, d1.h_F, rootOf d1.J, rootOf d1.F, rootOf d1.T_h, rootOf d1.L, d1.s, d1.nj, d1.finalize.card)
def d2 := derive_named env cfg nb2
#eval (d2.h, d2.h_j, d2.h_F, rootOf d2.J, rootOf d2.F, rootOf d2.T_h, rootOf d2.L, d2.s, d2.nj, d2.finalize.card,
       d2.target_participation.card, d2.progress.card)
#eval (TimeoutBinding.targetedHeightPair d1 m2 == .empty, TimeoutBinding.targetedHeightPair d1 m1 == .timeout 2,
       TimeoutBinding.targetedHeightPair d1 m0 == .target 2 ⟨1⟩)
#eval decide (derive_named env cfg .genesis = (ChainState.initial : ChainState (Fin 3)))

-- Goldfish 後半 (周回 7)
def σ1 : ChainState (Fin 3) := { σ0 with h := 2 }
def σ2 : ChainState (Fin 3) := { σ0 with h := 3 }
def sig : Block (Fin 3) → ChainState (Fin 3) := fun B =>
  if B = b1 then σ1 else if B = b2 then σ2 else if B = b2' then σ1 else if B = b3 then σ2 else .initial
def fg : FGStore (Fin 3) :=
  { toSG := { toGoldfishStore := st, sg_votes := fun _ => ∅, timestamp_sg_vote := fun _ => none },
    σ := sig, F := g, J := b1, h_j := 1, h_max := 3 }
#eval ((sig g).h, (sig b2).h, (sig b1').h)
#eval (rootOf (get_fg_root fg), rootOf (get_fg_root { fg with h_max := 2 }), rootOf (get_fg_root { fg with h_max := 1 }))
#eval (viable sig 3 tree g, viable sig 3 tree b1, viable sig 3 tree b1', viable sig 3 tree b2',
       viable sig 3 tree b3, viable sig 4 tree b2', viable sig 4 tree b2)
#eval decide (viable_tree sig g 3 tree = {g, b1, b2, b2', b3})
#eval decide (viable_tree sig b1 4 tree = {b1, b2, b3})
#eval decide (get_filtered_block_tree fg = {g, b1, b2, b2', b3})
#eval decide (get_filtered_block_tree { fg with h_max := 2 } = {b1, b2, b2', b3})
#eval decide (get_filtered_block_tree_from fg {g, b1, b2'} = {g, b1, b2'})
def elig (cur : Nat) (b : Block (Fin 3)) : Bool := goldfish_eligible env sig 3 tree cur wv wv 2 b
#eval (elig 2 b1, elig 2 b1', elig 2 b2, elig 2 b2', elig 2 b3, elig 3 b2', elig 3 b3)
#eval rootOf (goldfish_fork_choice env sig 3 tree 2 g tree wv wv 2)
#eval rootOf (goldfish_fork_choice env sig 3 tree 3 g tree wv wv 2)
#eval rootOf (goldfish_fork_choice env sig 3 tree 2 (get_fg_root fg) (get_filtered_block_tree fg) wv wv 2)
#eval rootOf (goldfish_fork_choice env sig 3 tree 2 b1 {b2'} wv wv 2)

-- ValidatorClient (周回 8)
def idOf (o : Option BlockId) : Option Nat := o.map (·.value)
def rec0 := Record.initial
#eval ((finality_pair rec0 2 ⟨7⟩ 1).map (fun p => (p.height, p.target.value)),
       (finality_pair rec0 2 ⟨7⟩ 2).isNone,
       (finality_pair (rec0.with_target 2 ⟨8⟩) 2 ⟨7⟩ 1).isNone,
       (finality_pair (rec0.with_target 2 ⟨7⟩) 2 ⟨7⟩ 1).isSome,
       (finality_pair (rec0.with_timeout 2) 2 ⟨7⟩ 1).isNone,
       (finality_pair (rec0.with_lock 2 ⟨9⟩) 2 ⟨7⟩ 1).isNone,
       (finality_pair (rec0.with_lock 2 ⟨7⟩) 2 ⟨7⟩ 1).isSome)
def f35 : Option (Height × BlockId × Bool) := some (3, ⟨5⟩, false)
def f35t : Option (Height × BlockId × Bool) := some (3, ⟨5⟩, true)
#eval (height_pair rec0 none none == .empty,
       height_pair (rec0.with_timeout 3) f35 none == .timeout 3,
       height_pair (rec0.with_lock 3 ⟨5⟩) f35 none == .target 3 ⟨5⟩,
       height_pair (rec0.with_lock 3 ⟨6⟩) f35 none == .empty,
       height_pair (rec0.with_target 3 ⟨5⟩) f35t none == .target 3 ⟨5⟩,
       height_pair (rec0.with_target 3 ⟨6⟩) f35 none == .timeout 3,
       height_pair rec0 f35 none == .target 3 ⟨5⟩,
       height_pair rec0 f35t none == .timeout 3,
       height_pair rec0 f35 (some ⟨3, ⟨6⟩⟩) == .empty,
       height_pair rec0 f35t (some ⟨3, ⟨5⟩⟩) == .target 3 ⟨5⟩,
       height_pair rec0 f35 (some ⟨4, ⟨6⟩⟩) == .target 3 ⟨5⟩)
def ra1 := record_attestation rec0 (⟨0, 1, none, .target 3 ⟨5⟩, some ⟨2, ⟨7⟩⟩⟩ : CombinedAttestation (Fin 3))
def ra2 := record_attestation ra1 (⟨0, 2, none, .timeout 3, none⟩ : CombinedAttestation (Fin 3))
def ra3 := record_attestation ra2 (⟨0, 3, none, .target 3 ⟨9⟩, none⟩ : CombinedAttestation (Fin 3))
#eval (idOf (ra1.target 3), idOf (ra1.lock 2), ra1.timeout 3, ra2.timeout 3, idOf (ra3.target 3), idOf (ra3.target 4), idOf (ra3.lock 3))
def ca1 := create_attestation rec0 (0 : Fin 3) 1 (some ⟨1⟩) f35 2 ⟨7⟩ 1
#eval (decide (ca1.2 = ⟨0, 1, some ⟨1⟩, .target 3 ⟨5⟩, some ⟨2, ⟨7⟩⟩⟩), idOf (ca1.1.target 3), idOf (ca1.1.lock 2))
def ca2 := create_attestation ca1.1 (0 : Fin 3) 2 none (some (3, ⟨6⟩, false)) 2 ⟨7⟩ 1
#eval (decide (ca2.2 = ⟨0, 2, none, .timeout 3, some ⟨2, ⟨7⟩⟩⟩), ca2.1.timeout 3)
def ca3 := create_attestation ca2.1 (0 : Fin 3) 3 none f35 2 ⟨7⟩ 2
#eval decide (ca3.2 = ⟨0, 3, none, .timeout 3, none⟩)
#eval (NamedRecord.encodeHeight f35 (.target 3 ⟨5⟩) == .vote 3 ⟨5⟩ false, NamedRecord.encodeHeight f35 (.timeout 3) == .vote 3 ⟨5⟩ true,
       NamedRecord.encodeHeight none (.target 3 ⟨5⟩) == .empty, NamedRecord.encodeHeight f35 .empty == .empty)
#eval (decide (NamedRecord.rememberTimeout ∅ (.vote 3 ⟨5⟩ true) = {(3, ⟨5⟩)}),
       decide (NamedRecord.rememberTimeout ∅ (.vote 3 ⟨5⟩ false) = ∅))
def inp1 : NamedRecord.Input (Fin 3) := ⟨0, 1, some ⟨1⟩, f35, 2, ⟨7⟩, 1⟩
def nc1 := NamedRecord.create NamedRecord.initial inp1
#eval (decide (nc1.2 = ⟨0, 1, some ⟨1⟩, .vote 3 ⟨5⟩ false, some ⟨2, ⟨7⟩⟩⟩), decide (nc1.1.timeoutHistory = ∅), idOf (nc1.1.legacy.target 3))
def inp2 : NamedRecord.Input (Fin 3) := ⟨0, 2, none, some (3, ⟨6⟩, false), 2, ⟨7⟩, 1⟩
def nc2 := NamedRecord.create nc1.1 inp2
#eval (decide (nc2.2 = ⟨0, 2, none, .vote 3 ⟨6⟩ true, some ⟨2, ⟨7⟩⟩⟩), decide (nc2.1.timeoutHistory = {(3, ⟨6⟩)}), nc2.1.legacy.timeout 3)

-- Grades (周回 8)
def hc : HealConfig := ⟨3, by decide, 2, by decide⟩
#eval (hc.round_of 7, hc.opening_slot 2, hc.a 2 1)
#eval (head_covers tree b1 (some ⟨2⟩), head_covers tree b2' (some ⟨2⟩), head_covers tree b1 none, head_covers tree b1 (some ⟨99⟩))
def hs0 : HealingStore (Fin 3) := ⟨fg⟩
#eval decide (hs0.gradeView.tree = {g, b1, b2, b2', b3})
#eval ((chain_of b3).map rootOf, (chain_up 1 b3).map rootOf, (chain_up 0 b3).map rootOf, (chain_of g).map rootOf)
#eval ((deepest_clear none b3 (fun _ => true)).map rootOf, (deepest_clear (some b1) b3 (fun b => b.root != ⟨4⟩)).map rootOf,
       (deepest_clear (some b2') b3 (fun _ => true)).isNone, (deepest_clear none b3 (fun b => b.slot == 0)).map rootOf)
#eval (rootOf (clipGrade b3 b2'), rootOf (clipGrade b3 b2), rootOf (clipGrade g b3), rootOf (clipGrade b2' b3))
def frRoots (fr : Frame (Fin 3)) := (fr.g0.map (fun o => o.map rootOf), fr.g1.map (fun o => o.map rootOf), fr.g2.map (fun o => o.map rootOf))
def frA : Frame (Fin 3) := ⟨some (some b1), some none, some (some b3)⟩
def frB : Frame (Fin 3) := ⟨none, some (some b2'), some (some b3)⟩
def frC : Frame (Fin 3) := ⟨some (some b2), none, none⟩
#eval (clear frC b3, clear frC b2', clear frB b2', clear ⟨some none, none, none⟩ b2')
#eval (allClosed frA, allClosed frB, allClosed (pendingFrame : Frame (Fin 3)), allClosed (emptyFrame : Frame (Fin 3)))
#eval ((grade2Block hs0 frA).map rootOf, (grade2Block hs0 frB).isNone, (grade2Block hs0 ⟨some none, some none, some (some b2')⟩).map rootOf,
       (grade2Block hs0 ⟨some none, some none, some (some b1')⟩).map rootOf, (grade2Block hs0 emptyFrame).isNone)
#eval (rootOf (anchor env hc hs0 0 (some (some b2'))), rootOf (anchor env hc hs0 0 (some none)), rootOf (anchor env hc hs0 0 none),
       rootOf (anchor env hc hs0 0 (some (some b1'))), rootOf (anchor env hc hs0 0 (some (some b3))))
def tk (r : Nat) (k : Option Nat) : Token (Option BlockId) := ⟨r, k.map fun n => ⟨n⟩⟩
def early1 : Finset (Token (Option BlockId)) := {tk 1 (some 2), tk 2 (some 4)}
def late1 : Finset (Token (Option BlockId)) := {tk 3 (some 4)}
def raw1 : Finset (Token (Option BlockId)) := {tk 1 (some 2), tk 2 (some 4), tk 3 (some 4)}
def raw2 : Finset (Token (Option BlockId)) := {tk 1 (some 2), tk 2 (some 4), tk 3 (some 4), tk 3 (some 3)}
def cov : Option BlockId → Block (Fin 3) → Bool := fun k b => head_covers tree b k
instance (raw : Finset (Token (Option BlockId))) (k : Nat) : Decidable (CleanFrom raw k) := by unfold CleanFrom; infer_instance
#eval (decide (CleanFrom raw1 1), decide (CleanFrom raw2 2), decide (CleanFrom raw2 3), decide (CleanFrom raw2 4))
#eval (decide (Supports (fun k x => cov k x = true) early1 late1 raw1 b1), decide (Supports (fun k x => cov k x = true) early1 late1 raw1 b2'),
       decide (Supports (fun k x => cov k x = true) early1 late1 raw2 b1), decide (Supports (fun k x => cov k x = true) ∅ late1 raw1 b1))
#eval (decide (Opposes (fun k x => cov k x = true) early1 late1 raw1 b2'), decide (Opposes (fun k x => cov k x = true) early1 late1 raw1 b1),
       decide (Opposes (fun k x => cov k x = true) early1 late1 raw2 b1), decide (Opposes (fun k x => cov k x = true) early1 ∅ raw1 b2'))
def u1 : SGVote (Fin 3) := ⟨0, 1, some ⟨2⟩⟩
def u2 : SGVote (Fin 3) := ⟨0, 2, some ⟨4⟩⟩
def u3 : SGVote (Fin 3) := ⟨1, 2, some ⟨3⟩⟩
def u4 : SGVote (Fin 3) := ⟨0, 3, none⟩
def u5 : SGVote (Fin 3) := ⟨0, 2, some ⟨99⟩⟩
def u6 : SGVote (Fin 3) := ⟨1, 3, some ⟨2⟩⟩
def fgSg : FGStore (Fin 3) :=
  { fg with
    sg_votes := fun r => if r = 1 then {u1} else if r = 2 then {u2, u3, u5} else if r = 3 then {u4, u6} else ∅,
    timestamp_sg_vote := fun u =>
      if u = u1 then some ((5 : Time) : Stamp) else if u = u2 then some ((15 : Time) : Stamp) else if u = u3 then some ((7 : Time) : Stamp)
      else if u = u4 then some ((20 : Time) : Stamp) else if u = u6 then some ((9 : Time) : Stamp) else none }
def hs : HealingStore (Fin 3) := ⟨fgSg⟩
def gv2 := hs.gradeView
#eval (decide (rawInputs gv2 2 3 16 0 = {u1, u2}), decide (rawInputs gv2 2 3 10 0 = {u1}),
       decide (rawInputs gv2 2 4 30 0 = {u2, u4}), decide (rawInputs gv2 2 3 16 1 = {u3}))
#eval (bodyReady gv2 g 16 u1, bodyReady gv2 g 16 u2, bodyReady gv2 b2 16 u3, bodyReady gv2 b2' 16 u2,
       bodyReady gv2 g 16 u4, bodyReady gv2 g 16 u5, bodyReady gv2 g 8 u1)
#eval (decide (interpretedInputs gv2 g 2 3 16 0 = {u1, u2}), decide (interpretedInputs gv2 b2' 2 3 16 0 = ∅))
#eval (decide (rawView gv2 2 3 16 0 = {tk 1 (some 2), tk 2 (some 4)}), decide (readyView gv2 b2' 2 3 16 0 = ∅))
def pos (f : Block (Fin 3)) (v : Fin 3) (b : Block (Fin 3)) : Bool := positive gv2 f 2 3 10 16 v b
def opp (f : Block (Fin 3)) (v : Fin 3) (b : Block (Fin 3)) : Bool := opposing gv2 f 2 3 10 16 v b
#eval (pos g 0 g, pos g 0 b1, pos g 0 b2, pos g 0 b1', pos g 0 b2', pos g 0 b3)
#eval (opp g 0 g, opp g 0 b1, opp g 0 b2, opp g 0 b1', opp g 0 b2', opp g 0 b3)
#eval (pos g 1 b1, opp g 1 b1, pos g 2 b1, opp g 2 b1, pos b2' 0 g, opp b2' 0 b2')
def grd (f : Block (Fin 3)) (b : Block (Fin 3)) : Bool := gradeBool env gv2 f 2 3 10 16 b
#eval (grd g g, grd g b1, grd g b2, grd g b1', grd g b2', grd g b3)
#eval ((freezeRoot env gv2 g 2 3 10 16).map rootOf, (freezeRoot env gv2 b2' 2 3 10 16).isNone)
#eval ((freezeRoot env gv2 g 2 3 62 70).map rootOf, gradeBool env gv2 g 2 3 62 70 b2', gradeBool env gv2 g 2 3 62 70 b2)
#eval ((Phase.earlyOffset .g0, Phase.earlyOffset .g1, Phase.earlyOffset .g2), (Phase.lateOffset .g0, Phase.lateOffset .g1, Phase.lateOffset .g2),
       (Phase.domainOffset .g0, Phase.domainOffset .g1, Phase.domainOffset .g2))
#eval (opening env hc 1, early env hc 1 .g2, late env hc 1 .g2, domain env hc 1 .g2, domain env hc 1 .g1, domain env hc 1 .g0)
#eval (phaseResult frA .g1 == some none, frRoots (putPhase pendingFrame .g1 (some b2)), frRoots (emptyFrame : Frame (Fin 3)))
def c70 := completeOne env hc hs 3 70 .g2 pendingFrame
#eval (frRoots c70, frRoots (completeOne env hc hs 3 69 .g2 pendingFrame), frRoots (completeOne env hc hs 3 70 .g2 emptyFrame))
def cf70 := completeFrame env hc hs 3 70 pendingFrame
def cf72 := completeFrame env hc hs 3 72 cf70
def cf74 := completeFrame env hc hs 3 74 cf72
#eval (frRoots cf70, frRoots cf72, frRoots cf74)
#eval (frRoots (clipFrame b2' ⟨some (some b3), some none, none⟩), frRoots (clipFrame g cf74))
def cacheRoots (c : Cache (Fin 3)) := (c.round, frRoots c.current, frRoots c.next)
def c0 : Cache (Fin 3) := initialCache
def c1 := onPhaseTick env hc hs 70 c0
def c2 := onPhaseTick env hc hs 72 c1
def c3 := onPhaseTick env hc hs 74 c2
def c4 := onPhaseTick env hc hs 94 c3
def c5 := onPhaseTick env hc hs 96 c4
#eval (cacheRoots c0, cacheRoots c1)
#eval cacheRoots c2
#eval cacheRoots c3
#eval cacheRoots c4
#eval cacheRoots c5
#eval (cacheRoots (alignRound c1 3), (alignRound c1 2).round, cacheRoots (alignRound c1 5))
#eval (frRoots (cacheAtRound c1 2), frRoots (cacheAtRound c1 3), frRoots (cacheAtRound c1 4))
def rd3 := frameGradeRead c1 env hc hs 3
#eval (rootOf rd3.anchor, rd3.Q2.isNone, (letI := rd3.rawG2_decidable; decide rd3.rawG2), rd3.clear b2', frRoots (readFrame c1 hs 3))
#eval rootOf (currentSGVote hs rd3)
def rd3c := frameGradeRead c3 env hc hs 3
#eval (rootOf rd3c.anchor, rd3c.Q2.map rootOf, (letI := rd3c.rawG2_decidable; decide rd3c.rawG2), rd3c.clear b2', rd3c.clear b2)
def hsLive3 : HealingStore (Fin 3) := ⟨{ fgSg with live_confirmed := b3 }⟩
#eval (rootOf (currentSGVote hs rd3c), rootOf (currentSGVote hsLive3 rd3c),
       rootOf (currentSGVote hs { rd3c with Q2 := none }),
       rootOf (currentSGVote hs ⟨rd3c.anchor, none, rd3c.clear, False, inferInstance⟩))
def hsS9 : HealingStore (Fin 3) := ⟨{ fgSg with s := 9 }⟩
#eval ((frameSGCandidate c1 env hc hs 0).isNone, (frameSGCandidate c3 env hc hsS9 0).map rootOf,
       (frameStableRoot c1 env hc hs 3).map rootOf, (frameStableRoot c1 env hc hs 0).map rootOf)

-- Head (周回 8)
def cB : Cache (Fin 3) := ⟨0, ⟨none, some (some b2'), none⟩, pendingFrame⟩
def cC : Cache (Fin 3) := ⟨0, ⟨none, some (some b3), none⟩, pendingFrame⟩
def hsF : HealingStore (Fin 3) := ⟨{ fgSg with F := b2' }⟩
#eval (rootOf (get_sg_root_with (frameContract c1) env hc hs 3), rootOf (get_sg_root_with (frameContract cB) env hc hs 0),
       rootOf (get_sg_root_with (frameContract c3) env hc hs 3), rootOf (get_sg_root_with (frameContract cC) env hc hsF 0), frRoots (readFrame cC hsF 0))
#eval (rootOf (get_head_with (frameContract cB) env hc hs wv wv 2), rootOf (get_head_with (frameContract c1) env hc hs wv wv 2),
       rootOf (get_head_in_tree_with_layer (frameContract cB) env hc hs {g, b1} wv wv 2))

-- Duties.Inputs (周回 8)
def nd0 : Node (Fin 3) := { val_index := 0, new_root := fun s => ⟨s + 1⟩, awake := fun _ => true }
def nd1 : Node (Fin 3) := { val_index := 1, new_root := fun s => ⟨s + 1⟩, awake := fun _ => true }
def pi1 := with_proposal_input (frameContract c1) env hc nd0 hs id
#eval (rootOf pi1.parent, pi1.slot, pi1.root.value, pi1.gf_votes == [vA, vB, vC, vD], pi1.gf_support_votes == [vA, vB, vC], (pi1.proposer : Nat))
def ai1 := with_attestation_input (frameContract c1) env hc nd0 hs id
#eval ((ai1.val_index : Nat), ai1.round, idOf ai1.confirmed, ai1.fields.isNone, ai1.h_j, ai1.J.value, ai1.h_F)
def cD : Cache (Fin 3) := ⟨0, ⟨some (some b2), some (some b2), some (some b3)⟩, pendingFrame⟩
#eval ((grade2_block_with (frameContract cD) env hc hs 0).map rootOf, (grade2_block_with (frameContract c1) env hc hs 0).isNone)
#eval (rootOf (get_sg_vote_with (frameContract cD) env hc hs 0 (some b3)), rootOf (get_sg_vote_with (frameContract cD) env hc hsLive3 0 (some b3)),
       rootOf (get_sg_vote_with (frameContract cD) env hc hs 0 none), rootOf (get_sg_vote_with (frameContract c1) env hc hs 0 none))
def hsLive2' : HealingStore (Fin 3) := ⟨{ fgSg with live_confirmed := b2' }⟩
#eval ((fg_source_with (frameContract cD) env hc hs 0 (some b3)).map rootOf, (fg_source_with (frameContract cD) env hc hs 0 none).isNone,
       (fg_source_with (frameContract cD) env hc hsLive3 0 (some b2)).map rootOf,
       (fg_source_with (frameContract cD) env hc hsLive2' 0 (some b1)).map rootOf)
def fv1 := get_fg_vote_with (frameContract cD) env hc hs 0 (some b3)
#eval (fv1.1.map (fun t => (t.1, t.2.1.value, t.2.2)), fv1.2.1, fv1.2.2.1.value, fv1.2.2.2)
def ai2 := with_attestation_input (frameContract cD) env hc nd1 hs id
#eval ((ai2.val_index : Nat), ai2.round, idOf ai2.confirmed, ai2.fields.map (fun t => (t.1, t.2.1.value, t.2.2)), ai2.h_j, ai2.J.value, ai2.h_F)

-- Store / Handlers (周回 9)
def s0 : Store (Fin 3) := Store.init
#eval (s0.t, s0.s, decide (s0.T = {g}), s0.timestamp_block g == some ⊥, (s0.timestamp_block b1).isNone,
       s0.h_max, s0.h_j, rootOf s0.F, rootOf s0.J, decide (s0.pool 1 = ∅), decide (s0.sg_pool 0 = ∅))
#eval (rootOf (advance_confirmed b2 b1), rootOf (advance_confirmed b1 b2), rootOf (advance_confirmed b2 b2'), rootOf (advance_confirmed b2 b2))
#eval (rootOf (floor_on_stable b1 b2 b2'), rootOf (floor_on_stable b2 b1' b2), rootOf (floor_on_stable b2 b1' b1'), rootOf (floor_on_stable g b2' b3))
def s1 : Store (Fin 3) := { s0 with t := 8, s := 1 }
def s1b := on_block env cfg s1 b1
#eval (decide (s1b.T = {g, b1}), s1b.timestamp_block b1 == some ((8 : Time) : Stamp), (s1b.σ b1).s, rootOf (s1b.σ b1).L, s1b.h_max)
def s1x := on_block env cfg s1 b2
def s1y := on_block env cfg s1b b1'
def s1z := on_block env cfg { s1b with s := 2 } b3
def s1d := on_block env cfg s1b b1
#eval (decide (s1x.T = s0.T), decide (s1y.T = s1b.T), decide (s1z.T = s1b.T), decide (s1d.T = s1b.T) && s1d.timestamp_block b1 == s1b.timestamp_block b1)
def s2 : Store (Fin 3) := { s1b with t := 10 }
def vg1 := on_goldfish_vote s2 vA
def vg2 := on_goldfish_vote vg1 vC
def vg3 := on_goldfish_vote vg2 ⟨0, 1, ⟨5⟩⟩
def vg4 := on_goldfish_vote vg3 vA
def vg5 := on_goldfish_vote vg4 ⟨1, 3, ⟨1⟩⟩
def vg6 := on_goldfish_vote { vg4 with s := 3 } ⟨2, 1, ⟨1⟩⟩
def vg7 := on_goldfish_vote_checked env vg4 vB
def vg8 := on_goldfish_vote_checked env vg4 ⟨0, 0, ⟨0⟩⟩
#eval (vg1.gf_votes 1 == [vA], vg1.timestamp_vote vA == some ((10 : Time) : Stamp), vg2.gf_votes 1 == [vA, vC],
       vg3.gf_votes 1 == [vA, vC], (vg3.timestamp_vote ⟨0, 1, ⟨5⟩⟩).isNone, vg4.gf_votes 1 == [vA, vC],
       (vg5.gf_votes 3).isEmpty, (vg6.gf_votes 1).length, (vg7.gf_votes 1).length, vg8.gf_votes 0 == [⟨0, 0, ⟨0⟩⟩])
#eval (decide (vg2.pool 1 = {vA, vC}), vg2.tau vA == some ((10 : Time) : Stamp), (vg2.tau vD).isNone)
def sa0 : CombinedAttestation (Fin 3) := ⟨0, 0, some ⟨1⟩, .empty, none⟩
def sa1 : CombinedAttestation (Fin 3) := ⟨0, 0, some ⟨1⟩, .timeout 1, none⟩
def sa2 : CombinedAttestation (Fin 3) := ⟨0, 0, none, .empty, none⟩
def sa3 : CombinedAttestation (Fin 3) := ⟨0, 0, some ⟨0⟩, .empty, none⟩
def sa4 : CombinedAttestation (Fin 3) := ⟨1, 1, some ⟨1⟩, .empty, none⟩
def sg1 := on_sg_vote hc vg2 sa0
def sg2 := on_sg_vote hc sg1 sa1
def sg3 := on_sg_vote hc sg2 sa2
def sg4 := on_sg_vote hc sg3 sa3
def sg5 := on_sg_vote hc sg4 sa4
def sg6 := on_sg_vote hc { sg4 with s := 9 } ⟨2, 0, none, .empty, none⟩
def sg7 := on_sg_vote hc { sg4 with s := 9 } sa4
#eval (sg1.sg_votes 0 == [sa0], sg1.timestamp_sg_vote (sgVote sa0) == some ((10 : Time) : Stamp), sg2.sg_votes 0 == [sa0],
       sg3.sg_votes 0 == [sa0, sa2], decide (round_votes sg3 sa3 = {some ⟨1⟩, none}), sg4.sg_votes 0 == [sa0, sa2],
       (sg5.sg_votes 1).isEmpty, decide (sg3.sg_pool 0 = {sa0, sa2}), (sg6.sg_votes 0).length, sg7.sg_votes 1 == [sa4])
#eval (decide (sg3.toHealing.sg_votes 0 = {⟨0, 0, some ⟨1⟩⟩, ⟨0, 0, none⟩}), sg3.toHealing.s, decide (sg3.toHealing.sg_votes 5 = ∅),
       decide (sg3.toHealing.T = sg3.T), sg3.toHealing.timestamp_sg_vote (sgVote sa0) == some ((10 : Time) : Stamp))
def uf : Store (Fin 3) := { s0 with T := tree, σ := sig, F := g, J := g, h_j := 0, h_max := 1 }
def σJ : ChainState (Fin 3) := { σ0 with h := 3, J := b1, h_j := 2, F := g, h_F := 0 }
def uf1 := update_finality uf σJ
def σF : ChainState (Fin 3) := { σ0 with h := 4, J := b2, h_j := 3, F := b1, h_F := 2 }
def uf2 := update_finality uf1 σF
def σG : ChainState (Fin 3) := { σ0 with h := 4, J := b2', h_j := 3, F := b2', h_F := 3 }
def uf3 := update_finality uf2 σG
def σH : ChainState (Fin 3) := { σ0 with h := 4, J := b2', h_j := 3, F := b2, h_F := 3 }
def uf4 := update_finality uf3 σH
def σI : ChainState (Fin 3) := { σ0 with h := 4, J := b3, h_j := 4, F := b2, h_F := 3 }
def uf5 := update_finality uf4 σI
#eval ((uf1.h_max, rootOf uf1.J, uf1.h_j, rootOf uf1.F), (uf2.h_max, rootOf uf2.J, uf2.h_j, rootOf uf2.F), (uf3.h_max, rootOf uf3.J, uf3.h_j, rootOf uf3.F),
       (uf4.h_max, rootOf uf4.J, uf4.h_j, rootOf uf4.F), (uf5.h_max, rootOf uf5.J, uf5.h_j, rootOf uf5.F))
def gs : Store (Fin 3) := { s0 with F := b1, latest_stable := b2, latest_confirmed := b3 }
#eval (rootOf (get_stable gs), rootOf (get_confirmed gs), rootOf (get_stable { gs with F := b2' }), rootOf (get_confirmed { gs with F := b2' }),
       rootOf (get_confirmed { gs with latest_confirmed := b1 }), rootOf (get_confirmed { gs with latest_confirmed := b2' }))

-- The named path (周回 9)
def z10 : NamedAttestation (Fin 3) := ⟨0, 0, none, .vote 1 ⟨0⟩ false, none⟩
def z11 : NamedAttestation (Fin 3) := ⟨1, 0, none, .vote 1 ⟨0⟩ false, none⟩
def z20 : NamedAttestation (Fin 3) := ⟨0, 0, some ⟨1⟩, .vote 2 ⟨1⟩ false, some ⟨1, ⟨0⟩⟩⟩
def z21 : NamedAttestation (Fin 3) := ⟨1, 0, some ⟨1⟩, .vote 2 ⟨1⟩ true, some ⟨1, ⟨0⟩⟩⟩
def z22 : NamedAttestation (Fin 3) := ⟨2, 0, none, .vote 2 ⟨5⟩ false, none⟩
def z30 : NamedAttestation (Fin 3) := ⟨0, 1, some ⟨2⟩, .vote 3 ⟨2⟩ false, none⟩
def z31 : NamedAttestation (Fin 3) := ⟨1, 1, some ⟨2⟩, .vote 3 ⟨2⟩ false, none⟩
def z40 : NamedAttestation (Fin 3) := ⟨0, 1, some ⟨3⟩, .empty, some ⟨3, ⟨2⟩⟩⟩
def z41 : NamedAttestation (Fin 3) := ⟨1, 1, some ⟨3⟩, .empty, some ⟨3, ⟨2⟩⟩⟩
def mb1 : NamedBlock (Fin 3) := .node .genesis 1 ⟨1⟩ [] [] [z10, z11] 0
def mb2 : NamedBlock (Fin 3) := .node mb1 2 ⟨2⟩ [vA] [vA] [z20, z21, z22] 0
def mb3 : NamedBlock (Fin 3) := .node mb2 3 ⟨3⟩ [] [] [z30, z31] 0
def mb4 : NamedBlock (Fin 3) := .node mb3 4 ⟨4⟩ [] [] [z40, z41] 0
def e1 := mb1.erase
def e2 := mb2.erase
def e3 := mb3.erase
def e4 := mb4.erase
def cs (st : Store (Fin 3)) (b : Block (Fin 3)) := st.σ b
def csr (σ : ChainState (Fin 3)) := (σ.h, σ.h_j, σ.h_F, rootOf σ.J, rootOf σ.F, rootOf σ.T_h, σ.nj, σ.finalize.card)
def ns0 : NamedStore (Fin 3) := NamedStore.initial
def ns1 := NamedAdmission.on_block_with .alsoCarried env hc cfg (NamedStore.setClock env ns0 8) mb1
def ns2 := NamedAdmission.on_block_with .alsoCarried env hc cfg (NamedStore.setClock env ns1 16) mb2
def ns3 := NamedAdmission.on_block_with .alsoCarried env hc cfg (NamedStore.setClock env ns2 24) mb3
def ns4 := NamedAdmission.on_block_with .alsoCarried env hc cfg (NamedStore.setClock env ns3 32) mb4
#eval (ns0.bodies.card, ns0.core.T.card, (NamedStore.setClock env ns0 8).core.t, (NamedStore.setClock env ns0 8).core.s)
#eval (ns1.core.T.card, csr (cs ns1.core e1), ns1.core.h_max, ns1.core.h_j, rootOf ns1.core.J, rootOf ns1.core.F, ns1.sg_rows 0 == [z10, z11], ns1.bodies.card,
       ns1.core.timestamp_block e1 == some ((8 : Time) : Stamp), ns1.core.timestamp_sg_vote ⟨1, 0, none⟩ == some ((8 : Time) : Stamp))
#eval (ns2.core.T.card, csr (cs ns2.core e2), ns2.core.h_max, ns2.core.h_j, rootOf ns2.core.J, rootOf ns2.core.F, ns2.sg_rows 0 == [z10, z11, z20, z21, z22], ns2.bodies.card,
       ns2.core.gf_votes 1 == [vA], ns2.core.timestamp_vote vA == some ((16 : Time) : Stamp), (ns2.core.sg_pool 0).card)
#eval (ns3.core.T.card, csr (cs ns3.core e3), ns3.core.h_max, ns3.core.h_j, rootOf ns3.core.J, rootOf ns3.core.F, ns3.sg_rows 1 == [z30, z31], ns3.bodies.card)
#eval (ns4.core.T.card, csr (cs ns4.core e4), ns4.core.h_max, ns4.core.h_j, rootOf ns4.core.J, rootOf ns4.core.F, ns4.sg_rows 1 == [z30, z31, z40, z41], ns4.bodies.card,
       rootOf (get_stable ns4.core), rootOf (get_confirmed ns4.core), ns4.core.tau vA == some ((16 : Time) : Stamp))
#eval decide (ns4.core.toHealing.sg_votes 1 = {⟨0, 1, some ⟨2⟩⟩, ⟨1, 1, some ⟨2⟩⟩, ⟨0, 1, some ⟨3⟩⟩, ⟨1, 1, some ⟨3⟩⟩})
#eval ((chain_attestations e1).card, (chain_attestations e2).card, (chain_attestations e4).card, decide (chain_attestations g = ∅),
       (store_attestations ns4.core).card, decide (z22.erase ∈ store_attestations ns4.core), (store_attestations ns1.core).card)
def mbx : NamedBlock (Fin 3) := .node nb1 5 ⟨7⟩ [] [] [] 0
def mby : NamedBlock (Fin 3) := .node mb4 5 ⟨7⟩ [] [] [⟨2, 2, none, .empty, none⟩] 0
def mbz : NamedBlock (Fin 3) := .node mb4 5 ⟨7⟩ [] [] [] 1
def ns5c := NamedStore.setClock env ns4 40
#eval (ns5c.core.t, ns5c.core.s, (NamedAdmission.on_block_with .alsoCarried env hc cfg ns5c mbx).bodies.card,
       (NamedAdmission.on_block_with .alsoCarried env hc cfg ns5c mby).bodies.card, (NamedAdmission.on_block_with .alsoCarried env hc cfg ns5c mbz).bodies.card,
       (NamedAdmission.on_block_with .alsoCarried env hc cfg ns5c mb4).bodies.card, (NamedAdmission.on_block_with .alsoCarried env hc cfg ns5c (.node mb4 5 ⟨7⟩ [] [] [] 0)).bodies.card)

-- Duties.Proposals (周回 9)
#eval (ProposalRows.inWindow hc ns5c.core 0, ProposalRows.inWindow hc ns5c.core 1, ProposalRows.inWindow hc ns5c.core 2,
       ProposalRows.inWindow hc { ns5c.core with s := 9 } 0, ProposalRows.inWindow hc { ns5c.core with s := 9 } 1)
#eval (NamedProposalRows.processedRows hc ns5c == [z10, z11, z20, z21, z22, z30, z31, z40, z41], (NamedProposalRows.orderedRoots ns5c).map (·.value),
       (NamedProposalRows.orderedBodies ns5c).map (fun b => b.root.value), (NamedProposalRows.poolRows hc ns5c).length,
       NamedProposalRows.carriedRows hc ns5c == [z10, z11, z20, z21, z22, z30, z31, z40, z41], (NamedProposalRows.select .poolAndCarried hc ns5c).length)
#eval (NamedProposalRows.chainRows mb2 == [z20, z21, z22, z10, z11], (NamedProposalRows.chainRows (.genesis : NamedBlock (Fin 3))).isEmpty, NamedProposalRows.excludeOnChain mb2 [z10, z30, z20, z40] == [z30, z40],
       NamedProposalRows.capPerSigner [z30, z30, z40, ⟨0, 1, some ⟨9⟩, .empty, none⟩, z31] == [z30, z40, z31],
       NamedProposalRows.proposalRows mb2 (NamedProposalRows.select .poolAndCarried hc ns5c) == [z30, z31, z40, z41])
#eval ((NamedActions.parentBody? ns5c e2).map (fun b => b.root.value), (NamedActions.parentBody? ns5c b2).isNone,
       ((NamedActions.creatorInput ai1).round, idOf (NamedActions.creatorInput ai1).confirmed, (NamedActions.creatorInput ai1).h_F))
def prop5 := NamedActions.proposal_with (frameContract c0) .poolAndCarried env hc nd0 ns5c
#eval prop5.map (fun b => (b.root.value, b.slot, b.parent.root.value, b.attestations == [z30, z31, z40, z41], b.gf_votes.isEmpty))
def pb5 := NamedDuties.propose_block_with (frameContract c0) env hc cfg nd0 ns5c
def e5 := (pb5.2.getD .genesis).erase
#eval (pb5.2.map (fun b => b.root.value), pb5.1.bodies.card, pb5.1.core.T.card, csr (cs pb5.1.core e5), pb5.1.core.timestamp_block e5 == some ((40 : Time) : Stamp),
       (pb5.1.sg_rows 1).length, rootOf pb5.1.core.F, pb5.1.core.h_max)
def ns5v := NamedStore.setClock env pb5.1 42
def gv5 := NamedDuties.goldfish_vote_with (frameContract c0) env hc nd0 ns5v
def gv5' := NamedDuties.goldfish_vote_with (frameContract c0) env hc nd1 ns5v
#eval (gv5.2 == some ⟨0, 5, ⟨6⟩⟩, gv5.1.core.gf_votes 5 == [⟨0, 5, ⟨6⟩⟩], gv5.1.core.timestamp_vote ⟨0, 5, ⟨6⟩⟩ == some ((42 : Time) : Stamp),
       gv5'.2.isNone, (gv5'.1.core.gf_votes 5).isEmpty)
def ns5u := NamedDuties.update_confirmation_with (frameContract c0) env hc (NamedStore.setClock env gv5.1 44) 4
#eval (rootOf ns5u.core.live_confirmed, rootOf ns5u.core.latest_stable, rootOf ns5u.core.latest_confirmed, rootOf (get_stable ns5u.core), rootOf (get_confirmed ns5u.core))
def ns6u := NamedDuties.update_confirmation_with (frameContract c0) env hc (NamedStore.setClock env ns5u 52) 5
#eval (rootOf ns6u.core.live_confirmed, rootOf ns6u.core.latest_stable, rootOf ns6u.core.latest_confirmed, rootOf (get_stable ns6u.core), rootOf (get_confirmed ns6u.core))
def at4 := NamedDuties.attest_with (frameContract c0) env hc nd0 (NamedStore.setClock env ns4 36) NamedRecord.initial
#eval (decide (at4.2.2 = ⟨0, 1, some ⟨2⟩, .empty, none⟩), (at4.2.1.legacy.target 1).isNone, decide (at4.2.1.timeoutHistory = ∅), (at4.1.sg_rows 1).length, (at4.1.core.sg_pool 1).card)
def at7 := NamedDuties.attest_with (frameContract c0) env hc nd0 (NamedStore.setClock env ns6u 60) NamedRecord.initial
#eval (decide (at7.2.2 = ⟨0, 2, some ⟨6⟩, .empty, none⟩), at7.1.sg_rows 2 == [⟨0, 2, some ⟨6⟩, .empty, none⟩],
       at7.1.core.timestamp_sg_vote ⟨0, 2, some ⟨6⟩⟩ == some ((60 : Time) : Stamp), decide (at7.1.core.sg_pool 2 = {⟨0, 2, some ⟨6⟩, .empty, none⟩}))

-- Tick / Execution.Objects (周回 9)
def objKind (o : Execution.NamedObject (Fin 3)) : Nat := match o with | .block _ => 0 | .gfVote _ => 1 | .attest _ => 2
def objRoot (o : Execution.NamedObject (Fin 3)) : Nat := match o with
  | .block b => b.root.value
  | .gfVote v => v.head.value
  | .attest row => (row.confirmed.map (·.value)).getD 99
def objAuthor (o : Execution.NamedObject (Fin 3)) : Option Nat := (Execution.NamedObject.author o).map (fun v => (v : Nat))
#eval (objAuthor (.block mb1), objAuthor (.block .genesis), objAuthor (.gfVote vB), objAuthor (.attest z22))
def tk36 := NamedTick.tick (frameContract c0) env hc cfg nd0 ns4 NamedRecord.initial 36
#eval (tk36.2.2.map objKind, tk36.2.2.map objRoot, tk36.2.2.map objAuthor, tk36.1.core.t, tk36.1.core.s, (tk36.1.sg_rows 1).length,
       rootOf tk36.1.core.live_confirmed, rootOf tk36.1.core.latest_stable, rootOf tk36.1.core.latest_confirmed)
def tk40 := NamedTick.tick (frameContract c0) env hc cfg nd0 tk36.1 tk36.2.1 40
#eval (tk40.2.2.map objKind, tk40.2.2.map objRoot, tk40.1.bodies.card, tk40.1.core.T.card, rootOf tk40.1.core.F, tk40.1.core.s)
def tk42 := NamedTick.tick (frameContract c0) env hc cfg nd0 tk40.1 tk40.2.1 42
#eval (tk42.2.2.map objKind, tk42.2.2.map objRoot, tk42.1.core.gf_votes 5 == [⟨0, 5, ⟨6⟩⟩])
def tk44 := NamedTick.tick (frameContract c0) env hc cfg nd0 tk42.1 tk42.2.1 44
def tk46 := NamedTick.tick (frameContract c0) env hc cfg nd0 tk44.1 tk44.2.1 46
#eval (tk44.2.2.isEmpty, rootOf tk44.1.core.live_confirmed, tk46.2.2.isEmpty, tk46.1.core.t, tk46.1.core.s)
def tk52 := NamedTick.tick (frameContract c0) env hc cfg nd0 tk46.1 tk46.2.1 52
#eval (tk52.2.2.isEmpty, rootOf tk52.1.core.live_confirmed, rootOf tk52.1.core.latest_stable, rootOf tk52.1.core.latest_confirmed, tk52.1.core.s)
def tk60 := NamedTick.tick (frameContract c0) env hc cfg nd0 tk52.1 tk52.2.1 60
#eval (tk60.2.2.map objKind, tk60.2.2.map objRoot, rootOf tk60.1.core.live_confirmed, rootOf tk60.1.core.latest_confirmed, (tk60.1.sg_rows 2).length,
       tk60.1.sg_rows 2 == [⟨0, 2, some ⟨2⟩, .empty, none⟩])
def nd0s : Node (Fin 3) := { val_index := 0, new_root := fun s => ⟨s + 1⟩, awake := fun _ => false }
def tk60s := NamedTick.tick (frameContract c0) env hc cfg nd0s tk52.1 tk52.2.1 60
def tk40o := NamedTick.tick (frameContract c0) env hc cfg nd1 tk36.1 tk36.2.1 40
#eval (tk60s.2.2.isEmpty, (tk60s.1.sg_rows 2).isEmpty, tk40o.2.2.isEmpty, tk40o.1.bodies.card)

-- Execution (周回 10): the Witnesses' runs (the WeakGenesis / Outage / StrongRecovery fixtures restated here; the Witnesses modules import Proofs)
def rootOf2 (b : Block (Fin 2)) : Nat := b.root.value
def objKind2 (o : Execution.NamedObject (Fin 2)) : Nat := match o with | .block _ => 0 | .gfVote _ => 1 | .attest _ => 2
def objRoot2 (o : Execution.NamedObject (Fin 2)) : Nat := match o with
  | .block b => b.root.value
  | .gfVote v => v.head.value
  | .attest row => (row.confirmed.map (·.value)).getD 99
def objAuthor2 (o : Execution.NamedObject (Fin 2)) : Option Nat := (Execution.NamedObject.author o).map (fun v => (v : Nat))
def wE : Env (Fin 2) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 0, t_GST_nonneg := by decide, proposer := fun _ => 0, committees := ⟨fun _ => {0}⟩,
    electorate := { weight := fun v => if v = 0 then 2 else 1, weight_pos := by decide } }
def wHc : HealConfig := ⟨3, by decide, 2, by decide⟩
def wCfg : HeightConfig := ⟨4, 2, 6, by decide, by decide⟩
def wNode (v : Fin 2) : Node (Fin 2) := { val_index := v, new_root := fun s => ⟨s + 1⟩, awake := fun _ => v = 0 }
def wS : Execution.Setup (Fin 2) :=
  { E := wE, hc := wHc, cfg := wCfg, node := wNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0} : Finset (Fin 2)).Nonempty; exact Finset.singleton_nonempty 0, outage_window := by decide }
def wEvents : List (Execution.NamedEvent (Fin 2)) := (List.range 31).map (fun (n : Nat) => .tick 0 (n : Time))
def wRho : Execution.NamedRun (Fin 2) := { honest := {0}, horizon := 30, events := wEvents }
#eval (((wS.node 1).val_index : Nat), wS.a 0, wS.a 1, wS.a 2)
def evT : Execution.NamedEvent (Fin 2) := .tick 0 7
def evD : Execution.NamedEvent (Fin 2) := .deliver 1 (.gfVote ⟨0, 1, ⟨1⟩⟩) 7
#eval (Generic.Event.time evT, ((Generic.Event.node evD : Fin 2) : Nat), (Generic.Event.object? evT).isNone, (Generic.Event.object? evD).map objKind2,
       Generic.Event.phase evT, Generic.Event.phase evD, ofLex (Generic.Event.key evD), decide (Generic.Event.key evT < Generic.Event.key evD),
       decide (Generic.Event.key (Execution.NamedEvent.deliver 1 (.gfVote ⟨0, 1, ⟨1⟩⟩) 6) < Generic.Event.key evT))
def worlds (S : Execution.Setup (Fin 2)) (rho : Execution.NamedRun (Fin 2)) : Array (Execution.NamedWorld (Fin 2)) :=
  (rho.events.scanl (fun w ev => Execution.NamedWorld.step S w ev) Execution.NamedWorld.init).toArray
def readSt (st : NamedStore (Fin 2)) : String :=
  toString (st.core.t, st.core.s, st.core.T.card, st.bodies.card, rootOf2 st.core.F, rootOf2 st.core.J, st.core.h_max, st.core.h_j,
            rootOf2 (get_stable st.core), rootOf2 (get_confirmed st.core), rootOf2 st.core.live_confirmed,
            (st.core.gf_votes st.core.s).length, (st.sg_rows 0).length + (st.sg_rows 1).length + (st.sg_rows 2).length)
def readOf (w : Execution.NamedWorld (Fin 2)) (v : Fin 2) : String := readSt (w v).st
def emitsOf (S : Execution.Setup (Fin 2)) (w : Execution.NamedWorld (Fin 2)) (v : Fin 2) (t : Time) : List (Execution.NamedObject (Fin 2)) :=
  (Execution.NamedNode.tick S v (w v) t).2
def objsOf (os : List (Execution.NamedObject (Fin 2))) : String := toString (os.map objKind2, os.map objRoot2, os.map objAuthor2)
def wWorlds := worlds wS wRho
def wAt (i : Nat) : Execution.NamedWorld (Fin 2) := wWorlds.getD i Execution.NamedWorld.init
#eval do for i in List.range 31 do IO.println (toString i ++ " " ++ readOf (wAt i) 0 ++ " " ++ objsOf (emitsOf wS (wAt i) 0 (i : Time)))
#eval (wWorlds.size, readOf (wAt 31) 0)
#eval (([4, 31] : List Nat).all (fun i => readOf (Execution.NamedRun.stateBefore wS wRho i) 0 == readOf (wAt i) 0),
       ([6, 30] : List Nat).all (fun t => readSt (Execution.Run.storeAt wS wRho 0 (t : Time)) == readOf (wAt (t + 1)) 0),
       readOf (Execution.NamedRun.stateBeforeTime wS wRho 4) 0 == readOf (wAt 4) 0,
       readOf (Execution.NamedRun.readAt wS wRho 4) 0 == readOf (wAt 5) 0,
       ([4, 30] : List Nat).all (fun i => objsOf (Generic.Run.emittedAt (Execution.spec wS) wRho i 0 (i : Time) : List (Execution.NamedObject (Fin 2))) == objsOf (emitsOf wS (wAt i) 0 (i : Time))),
       readOf (Generic.Run.final (Execution.spec wS) wRho : Execution.NamedWorld (Fin 2)) 0 == readOf (wAt 31) 0,
       readOf (Generic.Run.final (Execution.spec wS) wRho : Execution.NamedWorld (Fin 2)) 1 == readOf Execution.NamedWorld.init 1,
       (Execution.NamedWorld.init (V := Fin 2) 0).st.bodies.card)
def wEvents2 : List (Execution.NamedEvent (Fin 2)) :=
  (List.range 8).flatMap (fun (n : Nat) =>
    [(.tick 0 (n : Time) : Execution.NamedEvent (Fin 2)), .tick 1 (n : Time)]
      ++ (emitsOf wS (wAt n) 0 (n : Time)).map (fun o => (.deliver 1 o (n : Time) : Execution.NamedEvent (Fin 2))))
def wRho2 : Execution.NamedRun (Fin 2) := { honest := {0, 1}, horizon := 7, events := wEvents2 }
def wObjs := Execution.NamedRun.objects wRho2
#eval (wEvents2.length, wObjs.length, (wObjs.filter (fun o => objKind2 o == 0)).length, (wObjs.filter (fun o => objKind2 o == 1)).length, (wObjs.filter (fun o => objKind2 o == 2)).length,
       (Execution.NamedRun.objects wRho).isEmpty)
def wWorlds2 := worlds wS wRho2
def idxB (t : Nat) : Nat := (wEvents2.filter (fun ev => decide (Generic.Event.time ev < (t : Time)))).length
def idxA (t : Nat) : Nat := (wEvents2.filter (fun ev => decide (Generic.Event.time ev ≤ (t : Time)))).length
def w2At (j : Nat) : Execution.NamedWorld (Fin 2) := wWorlds2.getD j Execution.NamedWorld.init
def delivLine (t : Nat) : String :=
  let os := emitsOf wS (wAt t) 0 (t : Time)
  let before := (w2At (idxB t) 1).st
  let after := (w2At (idxA t) 1).st
  toString (os.map (Execution.NamedReceipt.wellFormed wS), os.map (Execution.NamedReceipt.depsPresent before), os.map (Execution.NamedReceipt.processed before),
            os.map (Execution.NamedReceipt.processed after), os.map (Execution.NamedReceipt.excludes after))
#eval do for t in List.range 8 do IO.println (toString t ++ " " ++ readOf (w2At (idxA t)) 1 ++ " " ++ delivLine t)
#eval ((List.range 8).all (fun t => readOf (w2At (idxA t)) 0 == readOf (wAt (t + 1)) 0),
       readSt (Execution.Run.storeAt wS wRho2 1 6) == readOf (w2At (idxA 6)) 1,
       (idxB 4, idxA 4, idxA 7))
def wB4? : Option (NamedBlock (Fin 2)) := match emitsOf wS (wAt 4) 0 4 with | [.block b] => some b | _ => none
def st1b3 := (w2At (idxB 4) 1).st
#eval (wB4?.map (fun b => b.root.value), wB4?.map (fun b => (Execution.NamedReceiptCalls.postCore wS st1b3 b).bodies.card),
       wB4?.map (fun b => (Execution.NamedReceiptCalls.postCore wS (NamedStore.setClock wE st1b3 4) b).bodies.card),
       wB4?.map (fun b => (Execution.NamedReceiptCalls.postCore wS (w2At (idxA 4) 1).st b).bodies.card))
def cr6 := Execution.NamedActionReads.confirmationReadAt wS wRho 0 6
#eval (cr6.st.core.t, cr6.st.core.s, cr6.cache.round, cr6.st.bodies.card, (Execution.NamedActionReads.preparedCache wS (wAt 6 0) 6).round)
def oE : Env (Fin 2) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 44, t_GST_nonneg := by decide, proposer := fun s => if s = 1 then 0 else 1, committees := ⟨fun _ => {0}⟩,
    electorate := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by decide } }
def oS : Execution.Setup (Fin 2) :=
  { E := oE, hc := wHc, cfg := wCfg, node := wNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0} : Finset (Fin 2)).Nonempty; exact Finset.singleton_nonempty 0, outage_window := by decide }
def oRho : Execution.NamedRun (Fin 2) := { honest := {0}, horizon := 45, events := (List.range 46).map (fun (n : Nat) => .tick 0 (n : Time)) }
def oWorlds := worlds oS oRho
def oAt (i : Nat) : Execution.NamedWorld (Fin 2) := oWorlds.getD i Execution.NamedWorld.init
#eval do for i in List.range 46 do IO.println (toString i ++ " " ++ readOf (oAt i) 0 ++ " " ++ objsOf (emitsOf oS (oAt i) 0 (i : Time)))
#eval readOf (oAt 46) 0
def rE : Env (Fin 2) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 1, t_GST_nonneg := by decide, proposer := fun _ => 0, committees := ⟨fun _ => {0}⟩,
    electorate := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by decide } }
def rNode (v : Fin 2) : Node (Fin 2) := { val_index := v, new_root := fun s => ⟨s + 1⟩, awake := fun _ => true }
def rS : Execution.Setup (Fin 2) :=
  { E := rE, hc := wHc, cfg := wCfg, node := rNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0} : Finset (Fin 2)).Nonempty; exact Finset.singleton_nonempty 0, outage_window := by decide }
def rWorlds := worlds rS wRho
def rAt (i : Nat) : Execution.NamedWorld (Fin 2) := rWorlds.getD i Execution.NamedWorld.init
#eval do for i in List.range 31 do IO.println (toString i ++ " " ++ readOf (rAt i) 0 ++ " " ++ objsOf (emitsOf rS (rAt i) 0 (i : Time)))
#eval readOf (rAt 31) 0

-- reviewer の fixture (周回 10): 生成側と同じ順
def xB1 : NamedBlock (Fin 2) := match emitsOf wS (wAt 4) 0 4 with | [.block b] => b | _ => .genesis
def xB2 : NamedBlock (Fin 2) := match emitsOf wS (wAt 8) 0 8 with | [.block b] => b | _ => .genesis
def xV1 : Execution.NamedObject (Fin 2) := (emitsOf wS (wAt 5) 0 5).headD (.block .genesis)
def xA0 : Execution.NamedObject (Fin 2) := (emitsOf wS (wAt 6) 0 6).headD (.block .genesis)
def xBadVote : Execution.NamedObject (Fin 2) := .gfVote ⟨1, 1, ⟨2⟩⟩
def xFork : NamedBlock (Fin 2) := .node .genesis 1 ⟨77⟩ [] [] [] 0
def xBadBlk : NamedBlock (Fin 2) := .node xB1 2 ⟨78⟩ [⟨1, 1, ⟨2⟩⟩] [] [] 0
def xBadSlot : NamedBlock (Fin 2) := .node xB1 2 ⟨79⟩ [⟨0, 5, ⟨2⟩⟩] [] [] 0
def xOrphan : NamedBlock (Fin 2) := .node xFork 2 ⟨80⟩ [] [] [] 0
#eval (rootOf2 xB1.erase, rootOf2 xB2.erase, objsOf [xV1, xA0])
def xEvents : List (Execution.NamedEvent (Fin 2)) :=
  [.tick 1 8, .deliver 1 (.block xB2) 8, .deliver 1 xV1 8, .deliver 1 xA0 8, .deliver 1 (.block xB1) 8,
   .deliver 1 (.block xB2) 8, .deliver 1 (.block xB2) 8, .deliver 1 xV1 8, .deliver 1 xBadVote 8,
   .deliver 1 (.block xFork) 8, .deliver 1 (.block xBadBlk) 8, .deliver 1 (.block xBadSlot) 8, .deliver 1 (.block xOrphan) 8, .tick 1 9]
def xRho : Execution.NamedRun (Fin 2) := { honest := {1}, horizon := 9, events := xEvents }
def xWorlds := worlds wS xRho
def xAt (j : Nat) : Execution.NamedWorld (Fin 2) := xWorlds.getD j Execution.NamedWorld.init
def objChecks (pre post : NamedStore (Fin 2)) (o : Execution.NamedObject (Fin 2)) : String :=
  toString (Execution.NamedReceipt.wellFormed wS o, Execution.NamedReceipt.depsPresent pre o, Execution.NamedReceipt.processed pre o,
            Execution.NamedReceipt.processed post o, Execution.NamedReceipt.excludes pre o)
#eval do for j in List.range xEvents.length do
  let ev := xEvents.getD j (.tick 1 0)
  let pre := (xAt j 1).st
  let post := (xAt (j+1) 1).st
  let extra := match ev with
    | .deliver _ o _ => objChecks pre post o
    | .tick v t => objsOf (emitsOf wS (xAt j) v t)
  IO.println (toString j ++ " " ++ readOf (xAt (j+1)) 1 ++ " " ++ extra ++ " " ++ toString (xAt (j+1) 1).cache.round)
#eval (readOf (Execution.NamedRun.readAt wS xRho 8) 1 == readOf (xAt 13) 1,
       readOf (Execution.NamedRun.stateBeforeTime wS xRho 9) 1 == readOf (xAt 13) 1,
       readOf (Generic.Run.final (Execution.spec wS) xRho : Execution.NamedWorld (Fin 2)) 1 == readOf (xAt 14) 1,
       readOf (Generic.Run.final (Execution.spec wS) xRho : Execution.NamedWorld (Fin 2)) 0 == readOf Execution.NamedWorld.init 0,
       (Execution.NamedRun.objects xRho).length)
def xSt := (xAt 13 1).st
def xStF : NamedStore (Fin 2) := { xSt with core := { xSt.core with F := xB2.erase } }
#eval ([xB1, xB2, xFork, xOrphan, xBadBlk].map (fun b => Execution.NamedReceipt.excludes xStF (.block b)), Execution.NamedReceipt.excludes xStF xV1, Execution.NamedReceipt.excludes xStF xA0)
def xNF : Execution.NamedNodeState (Fin 2) := { (xAt 13 1) with st := xStF }
#eval ((Execution.NamedNode.process wS xNF (.block xFork)).st.bodies.card, readSt (Execution.NamedNode.process wS xNF xV1).st,
       (Execution.NamedNode.process wS xNF xA0).cache.round)
def yEvents : List (Execution.NamedEvent (Fin 2)) := [.deliver 1 (.block xB1) 4, .tick 1 4, .deliver 1 (.block xB1) 4, .deliver 1 xV1 5, .tick 1 5, .tick 1 6]
def yRho : Execution.NamedRun (Fin 2) := { honest := {1}, horizon := 6, events := yEvents }
def yWorlds := worlds wS yRho
#eval do for j in List.range (yEvents.length + 1) do IO.println (toString j ++ " " ++ readOf (yWorlds.getD j Execution.NamedWorld.init) 1)
#eval (readSt (Execution.Run.storeAt wS yRho 1 4), objsOf (Generic.Run.emittedAt (Execution.spec wS) yRho 5 1 6 : List (Execution.NamedObject (Fin 2))))
def yCr := Execution.NamedActionReads.confirmationReadAt wS yRho 1 6
#eval (readSt yCr.st, yCr.cache.round)
