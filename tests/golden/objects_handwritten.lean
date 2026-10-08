import DecoupledConsensusModel.Objects.Parameters
import DecoupledConsensusModel.Objects.NamedBlocks
open DecoupledConsensusModel

-- 手書き Model の同じ値(tests/golden/objects_generated.lean と同じ順)。golden test の予行(周回 5)。
-- 実行: cd verified-consensus && lake env lean ../tests/golden/objects_handwritten.lean(Objects 層の olean がビルド済みであること)
#eval slotOfTime 1 (-1)
#eval slotOfTime 2 8
#eval slotOfTime 2 (slotStart 2 5)
#eval slotOfTime 1 7
#eval occurrenceMax (some ⊥) (some ((3 : Time) : Stamp)) == some ((3 : Time) : Stamp)
#eval occurrenceMax none (some ((3 : Time) : Stamp)) == none
#eval occurrenceBefore (some ⊥) (-100)
#eval occurrenceBefore (some ((3 : Time) : Stamp)) 3
#eval occurrenceBefore (some ((2 : Time) : Stamp)) 3
#eval occurrenceBefore none 100
#eval decide ((⊥ : Stamp) < ((-1000 : Time) : Stamp))

def g : Block (Fin 2) := .genesis
def b1 : Block (Fin 2) := .node g 1 ⟨1⟩ [] [] [] 0
def b2 : Block (Fin 2) := .node b1 2 ⟨2⟩ [] [] [] 0
def b2' : Block (Fin 2) := .node b1 2 ⟨3⟩ [] [] [] 1
def dup : Block (Fin 2) := .node g 1 ⟨2⟩ [] [] [] 1
#eval Block.preceq g b2
#eval Block.preceq b2 b2
#eval Block.preceq b2 b1
#eval Block.prec b2 b2
#eval Block.prec b1 b2
#eval Block.compatible b2 b2'
#eval Block.compatible b1 b2'
#eval Block.deeper b2' b2
#eval Block.deeper b2 b2'
#eval Block.deeper b2 b1
#eval Block.depth b2
#eval (Block.deepest? ({g, b1, b2, b2'} : Finset (Block (Fin 2)))).map Block.root
#eval (Block.deepest? ({b2, b2', b1, g} : Finset (Block (Fin 2)))).map Block.root
#eval (Block.deepest? (∅ : Finset (Block (Fin 2)))).map Block.root
#eval (Block.find? ({g, b1, b2} : Finset (Block (Fin 2))) ⟨2⟩).map Block.slot
#eval (Block.find? ({g, b1, b2, dup} : Finset (Block (Fin 2))) ⟨2⟩).map Block.slot
#eval Block.root g == genesisRoot
#eval Block.parent? g
#eval (Block.parent b2 == b1, Block.parent g == g)

def el : Electorate (Fin 2) := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by decide }
#eval el.totalWeight
#eval el.finalityThreshold
#eval el.quorumCheck {0}
#eval el.quorumCheck {1}
#eval el.weightOf {0, 1}

#eval NamedHeightPair.erase (.vote 5 ⟨1⟩ true)
#eval NamedHeightPair.erase (.vote 5 ⟨1⟩ false)
#eval NamedHeightPair.matchesEntry 5 ⟨1⟩ (.vote 5 ⟨1⟩ true)
#eval NamedHeightPair.matchesEntry 5 ⟨2⟩ (.vote 5 ⟨1⟩ true)
def nb : NamedBlock (Fin 2) := .node .genesis 1 ⟨7⟩ [] [] [⟨0, 0, none, .vote 1 ⟨7⟩ true, none⟩] 0
#eval Block.root nb.erase
#eval (Block.attestations nb.erase).map (·.height_pair)
#eval NamedBlock.preceq .genesis nb

def env : Env (Fin 2) :=
  { Δ := 2, Δ_pos := by decide, t_GST := 0, t_GST_nonneg := by decide,
    proposer := fun _ => 0, committees := ⟨fun _ => {0}⟩, electorate := el }
#eval env.t 3
#eval env.slotOf 25
#eval env.W
#eval env.q
