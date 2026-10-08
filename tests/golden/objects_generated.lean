-- 生成 Model(Objects 層)の値。tests/golden/objects_handwritten.lean(手書き Model)と同じ順で同じ値を出すこと。golden test の予行(周回 5)。
-- 実行: lake build Model && lake env lean tests/golden/objects_generated.lean(リポジトリのルートで)
import Model
open Model.Consensus.Objects

-- Time: 床除算と slot の往復、−∞ / +∞ の扱い(手書き Time.lean の意味)
#eval Time.slotOfTime 1 (-1)                      -- 0  (floor(-1/4) = -1 → toNat 0: times before t_0 clamp to slot 0)
#eval Time.slotOfTime 2 8                         -- 1
#eval Time.slotOfTime 2 (Time.slotStart 2 5)      -- 5  (slotOfTime Δ (slotStart Δ s) = s)
#eval Time.slotOfTime 1 7                         -- 1
#eval Time.occurrenceMax (some .Bottom) (some (.At 3))   -- some (At 3): −∞ drops out
#eval Time.occurrenceMax none (some (.At 3))             -- none: +∞ absorbing
#eval Time.occurrenceBefore (some .Bottom) (-100)        -- true: −∞ passes
#eval Time.occurrenceBefore (some (.At 3)) 3             -- false: strict
#eval Time.occurrenceBefore (some (.At 2)) 3             -- true
#eval Time.occurrenceBefore none 100                     -- false: +∞ fails
#eval (compare Time.Stamp.Bottom (Time.Stamp.At (-1000)))  -- lt

-- Blocks: ancestry / deeper / deepest? / findRoot?
def g : Blocks.Block := .Genesis
def b1 : Blocks.Block := .Node g 1 ⟨1⟩ [] [] [] ⟨0⟩
def b2 : Blocks.Block := .Node b1 2 ⟨2⟩ [] [] [] ⟨0⟩
def b2' : Blocks.Block := .Node b1 2 ⟨3⟩ [] [] [] ⟨1⟩
def dup : Blocks.Block := .Node g 1 ⟨2⟩ [] [] [] ⟨1⟩
#eval Blocks.preceq g b2            -- true
#eval Blocks.preceq b2 b2           -- true
#eval Blocks.preceq b2 b1           -- false
#eval Blocks.prec b2 b2             -- false
#eval Blocks.prec b1 b2             -- true
#eval Blocks.compatible b2 b2'      -- false
#eval Blocks.compatible b1 b2'      -- true
#eval Blocks.deeper b2' b2          -- true  (same depth, root 3 > 2 wins the tie)
#eval Blocks.deeper b2 b2'          -- false
#eval Blocks.deeper b2 b1           -- true  (greater depth)
#eval Blocks.depth b2               -- 2
#eval (Blocks.deepest? (NaruStd.Set.of [g, b1, b2, b2'])).map Blocks.root   -- some ⟨3⟩
#eval (Blocks.deepest? (NaruStd.Set.of [b2, b2', b1, g])).map Blocks.root   -- some ⟨3⟩ (order-independent)
#eval Blocks.deepest? (NaruStd.Set.empty : NaruStd.Set Blocks.Block)       -- none
#eval (Blocks.findRoot? (NaruStd.Set.of [g, b1, b2]) ⟨2⟩).map Blocks.slot   -- some 2
#eval (Blocks.findRoot? (NaruStd.Set.of [g, b1, b2, dup]) ⟨2⟩).map Blocks.slot  -- none (two blocks share root 2)
#eval Blocks.root g == Identifiers.genesisRoot   -- true
#eval Blocks.parent? g                           -- none
#eval (Blocks.parent b2 == b1, Blocks.parent g == g)  -- (true, true)

-- Weights: Table で持つ electorate
def el : Weights.Electorate := ⟨(NaruStd.Table.empty.insert ⟨0⟩ 3).insert ⟨1⟩ 1⟩
#eval Weights.totalWeight el                                -- 4
#eval Weights.finalityThreshold el                          -- 3  ((2*4+2)/3)
#eval Weights.quorumCheck el (NaruStd.Set.of [⟨0⟩])         -- true  (3 ≤ 3)
#eval Weights.quorumCheck el (NaruStd.Set.of [⟨1⟩])         -- false (3 ≤ 1)
#eval Weights.weightOf el (NaruStd.Set.of [⟨0⟩, ⟨1⟩, ⟨9⟩])  -- 4 (outside the electorate counts 0)

-- NamedBlocks: erasure
#eval NamedBlocks.eraseHeightPair (.Vote 5 ⟨1⟩ true)    -- Timeout 5
#eval NamedBlocks.eraseHeightPair (.Vote 5 ⟨1⟩ false)   -- Target 5 ⟨1⟩
#eval NamedBlocks.matchesEntry (.Vote 5 ⟨1⟩ true) 5 ⟨1⟩   -- true
#eval NamedBlocks.matchesEntry (.Vote 5 ⟨1⟩ true) 5 ⟨2⟩   -- false
def nb : NamedBlocks.NamedBlock := .Node .Genesis 1 ⟨7⟩ [] [] [⟨⟨0⟩, 0, none, .Vote 1 ⟨7⟩ true, none⟩] ⟨0⟩
#eval Blocks.root (NamedBlocks.eraseBlock nb)                                   -- ⟨7⟩
#eval (Blocks.attestations (NamedBlocks.eraseBlock nb)).map (·.heightPair)      -- [Timeout 1]
#eval NamedBlocks.namedPreceq .Genesis nb                                        -- true

-- Parameters
def env : Parameters.ProtocolEnv := ⟨2, 0, el⟩
#eval Parameters.slotTime env 3   -- 24
#eval Parameters.slotOf env 25    -- 3
#eval Parameters.envW env         -- 4
#eval Parameters.envQ env         -- 3
