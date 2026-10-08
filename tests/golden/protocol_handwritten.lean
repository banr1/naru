import DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
open DecoupledConsensusModel DecoupledConsensusModel.Protocol

-- 手書き Model の同じ値(tests/golden/protocol_generated.lean と同じ順)。golden test の予行(周回 6)。
-- 実行: cd verified-consensus && lake env lean ../tests/golden/protocol_handwritten.lean(Protocol 層の olean がビルド済みであること)

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
