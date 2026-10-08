-- 生成 Model(Protocol 層: Schedule / StoreBase / ForkChoice.Views / ForkChoice.Goldfish 前半)の値。
-- tests/golden/protocol_handwritten.lean(手書き Model)と同じ順で同じ値を出すこと。golden test の予行(周回 6)。
-- 集合・Occurrence は期待値との `==` で Bool に落とし、root は `.value` で出して、表現(Repr)の違いに依らず比較する。
-- 実行: lake build Model && lake env lean tests/golden/protocol_generated.lean(リポジトリのルートで)
import Model
open Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Protocol.ForkChoice

def tblOf {κ ν : Type} [Ord κ] (xs : List (κ × ν)) : NaruStd.Table κ ν :=
  xs.foldl (fun t e => t.insert e.1 e.2) NaruStd.Table.empty

-- fixture: validators 0 / 1 / 2、Δ = 2(t_s = 8s)、committee = {0}
def el : Weights.Electorate := ⟨tblOf [(⟨0⟩, 3), (⟨1⟩, 1), (⟨2⟩, 1)]⟩
def env : Parameters.ProtocolEnv := ⟨2, 0, el⟩
def committee : Nat → NaruStd.Set Identifiers.ValidatorId := fun _ => NaruStd.Set.of [⟨0⟩]

def vA : Blocks.GoldfishVote := ⟨⟨0⟩, 1, ⟨1⟩⟩
def vB : Blocks.GoldfishVote := ⟨⟨1⟩, 1, ⟨1⟩⟩
def vC : Blocks.GoldfishVote := ⟨⟨0⟩, 1, ⟨0⟩⟩     -- 0 equivocates in slot 1 (vA, vC)
def vD : Blocks.GoldfishVote := ⟨⟨2⟩, 1, ⟨99⟩⟩    -- head never stored: unresolved
def vE : Blocks.GoldfishVote := ⟨⟨1⟩, 2, ⟨1⟩⟩     -- slot 2, unstamped
def vF : Blocks.GoldfishVote := ⟨⟨1⟩, 1, ⟨2⟩⟩     -- names a slot-2 block from slot 1: never resolves

def g : Blocks.Block := .Genesis
def b1 : Blocks.Block := .Node g 1 ⟨1⟩ [] [] [] ⟨0⟩
def b1' : Blocks.Block := .Node g 1 ⟨5⟩ [] [] [] ⟨1⟩
def b2 : Blocks.Block := .Node b1 2 ⟨2⟩ [vA, vB] [vA] [] ⟨0⟩
def b2' : Blocks.Block := .Node b1 2 ⟨3⟩ [vB, vF, vE] [vF] [] ⟨1⟩
def b3 : Blocks.Block := .Node b2 3 ⟨4⟩ [vE] [vA] [] ⟨0⟩

def st : StoreBase.GoldfishStore :=
  ⟨16, 2, NaruStd.Set.of [g, b1, b1', b2, b2', b3],
   tblOf [(g, .Bottom), (b1, .At 5), (b1', .At 30), (b2, .At 9), (b2', .At 20), (b3, .At 10)],
   tblOf [(vA, .At 6), (vB, .At 12), (vC, .At 7), (vD, .At 6)],
   tblOf [(1, [vA, vB, vC, vD]), (2, [vE])],
   g, g⟩

def pool1 := StoreBase.pool st 1

-- Schedule: vocabulary
#eval Schedule.equivocates pool1 ⟨0⟩                 -- true
#eval Schedule.equivocates pool1 ⟨1⟩                 -- false
#eval Schedule.participates pool1 ⟨2⟩                -- true
#eval (Schedule.votesBy pool1 ⟨0⟩).size              -- 2
-- Schedule: instants (Δ = 2, slot 3)
#eval (Schedule.proposalTime env 3, Schedule.voteTime env 3, Schedule.supportCutoff env 3,
       Schedule.viewFreeze env 3, Schedule.confirmationTime env 3)   -- (24, 26, 28, 30, 36)
-- Schedule: constraints
#eval Schedule.voteWellFormed committee vA           -- true  (0 ∈ committee)
#eval Schedule.voteWellFormed committee vB           -- false
#eval (Schedule.carriedVotesWellFormed b2, Schedule.carriedVotesWellFormed b2',
       Schedule.carriedVotesWellFormed b3, Schedule.carriedVotesWellFormed g)   -- (true, false, true, true)
#eval (Schedule.carriedSupportWellFormed b2, Schedule.carriedSupportWellFormed b2',
       Schedule.carriedSupportWellFormed b3)                                    -- (true, true, false)

-- StoreBase: resolution
#eval (StoreBase.resolved st.tree vA, StoreBase.resolved st.tree vD, StoreBase.resolved st.tree vF,
       StoreBase.resolved st.tree ⟨⟨0⟩, 3, ⟨2⟩⟩, StoreBase.resolved st.tree vE)   -- (true, false, false, true, true)
#eval StoreBase.resolutionTime st.tree st.timestampBlock st.timestampVote vA == some (.At 6)   -- true
#eval StoreBase.resolutionTime st.tree st.timestampBlock st.timestampVote vC == some (.At 7)   -- true (−∞ drops out)
#eval (StoreBase.resolutionTime st.tree st.timestampBlock st.timestampVote vD).isNone            -- true
#eval (StoreBase.resolutionTime st.tree st.timestampBlock st.timestampVote vF).isNone            -- true
#eval (StoreBase.resolutionTime st.tree st.timestampBlock st.timestampVote vE).isNone            -- true (unstamped)
#eval pool1 == NaruStd.Set.of [vA, vB, vC, vD]      -- true
#eval (StoreBase.pool st 5).size                     -- 0
#eval StoreBase.tau st vB == some (.At 12)           -- true

-- Views (slot 2: freeze = view_freeze 1 = 14)
#eval Views.voterView env st 2 == NaruStd.Set.of [vA, vB, vC, vD, vF]          -- true
#eval (Views.voterView env st 2).size                                           -- 5
#eval Views.voterSupportView env st 2 == NaruStd.Set.of [vA, vB, vC]           -- true
#eval Views.voterProcessedBlockTree env st 2 == NaruStd.Set.of [g, b1, b2, b2', b3]   -- true (b1' stamped 30 and not under a slot-2 proposal)
#eval (Views.voterProcessedBlockTree env st 2).size                             -- 5
#eval Views.proposerView st 2 == [vA, vB, vC, vD]                               -- true
#eval Views.proposerSupportView st 2 == [vA, vB, vC]                            -- true
-- Views (slot 3: freeze = 22; vE is unstamped so only the carried arm sees it)
#eval Views.voterView env st 3 == NaruStd.Set.of [vE]                           -- true
#eval (Views.voterSupportView env st 3).isEmpty                                 -- true

-- Goldfish (slot-2 votes over the same tree; validator 1 equivocates with w1 / w1')
def w0 : Blocks.GoldfishVote := ⟨⟨0⟩, 2, ⟨2⟩⟩
def w1 : Blocks.GoldfishVote := ⟨⟨1⟩, 2, ⟨3⟩⟩
def w1' : Blocks.GoldfishVote := ⟨⟨1⟩, 2, ⟨2⟩⟩
def w2 : Blocks.GoldfishVote := ⟨⟨2⟩, 2, ⟨2⟩⟩
def wv := NaruStd.Set.of [w0, w1, w1', w2]
def tree := st.tree
def score : Blocks.Block → Nat := fun b => Goldfish.goldfishScore env tree wv wv 2 b
def rootOf (b : Blocks.Block) : Nat := (Blocks.root b).value
#eval (Goldfish.rawEquivocators wv == NaruStd.Set.of [⟨1⟩], Goldfish.rawParticipants wv == NaruStd.Set.of [⟨0⟩, ⟨1⟩, ⟨2⟩],
       Goldfish.votersCount env wv 2)                                            -- (true, true, 3)
#eval (score g, score b1, score b1', score b2, score b2', score b3)              -- (3, 3, 1, 3, 1, 1)
#eval (Goldfish.targetsUnder tree b1 w0, Goldfish.targetsUnder tree b3 w0, Goldfish.targetsUnder tree b2 vD)   -- (true, false, false)
#eval (Goldfish.outranks score b2 b2', Goldfish.outranks score b2' b2, Goldfish.outranks score b1 b1')         -- (true, false, true)
#eval (Goldfish.argmax? score (NaruStd.Set.of [b2, b2'])).map rootOf            -- some 2
#eval (Goldfish.argmax? score (NaruStd.Set.empty : NaruStd.Set Blocks.Block)).isNone   -- true
def tieScore : Blocks.Block → Nat := fun b => Goldfish.goldfishScore env tree (NaruStd.Set.of [w1, w2]) (NaruStd.Set.of [w1, w2]) 2 b
#eval (tieScore b2, tieScore b2', (Goldfish.argmax? tieScore (NaruStd.Set.of [b2, b2'])).map rootOf)   -- (1, 1, some 3): root order breaks the tie
#eval Goldfish.ghostChildren tree (fun _ => true) b1 == NaruStd.Set.of [b2, b2']               -- true
#eval Goldfish.ghostChildren tree (fun b => Blocks.root b != ⟨3⟩) b1 == NaruStd.Set.of [b2]    -- true
#eval (Goldfish.ghostStep tree score (fun _ => true) g).map rootOf              -- some 1
#eval rootOf (Goldfish.ghost g tree score (fun _ => true))                      -- 4 (g → b1 → b2 → b3)
#eval rootOf (Goldfish.ghost g tree score (fun b => 2 <= score b))              -- 2 (b3 scores 1: not eligible)
#eval rootOf (Goldfish.ghost b2' tree score (fun _ => true))                    -- 3 (no children)
#eval rootOf (Goldfish.ghostWalk tree score (fun _ => true) 1 g)                -- 1 (fuel 1: one step)
#eval (Goldfish.noSecondVoteIn wv w0, Goldfish.noSecondVoteIn wv w1)            -- (true, false)
#eval (Goldfish.latestWindow 3 5, Goldfish.latestWindow 3 2, Goldfish.latestWindow 3 0)   -- ([2, 3, 4], [0, 1], [])
#eval (Ord.compare (⟨1, ⟨5⟩⟩ : Goldfish.HeightId) ⟨2, ⟨0⟩⟩ == .lt, Ord.compare (⟨2, ⟨1⟩⟩ : Goldfish.HeightId) ⟨2, ⟨0⟩⟩ == .gt)   -- (true, true)
#eval Goldfish.finalizedDescendants b1 tree == NaruStd.Set.of [b1, b2, b2', b3]   -- true
