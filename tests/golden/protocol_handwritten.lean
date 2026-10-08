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
