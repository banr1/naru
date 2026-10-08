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

-- ChainState (周回 7): §4 slashing
def fp1 : Blocks.FinalityPair := ⟨2, ⟨7⟩⟩
#eval (ChainState.conflictsWithFinality .Empty fp1, ChainState.conflictsWithFinality (.Timeout 2) fp1,
       ChainState.conflictsWithFinality (.Target 2 ⟨7⟩) fp1, ChainState.conflictsWithFinality (.Target 2 ⟨8⟩) fp1,
       ChainState.conflictsWithFinality (.Timeout 3) fp1)                      -- (false, true, false, true, false)
def a0 : Blocks.CombinedAttestation := ⟨⟨0⟩, 1, some ⟨1⟩, .Target 2 ⟨7⟩, some ⟨2, ⟨7⟩⟩⟩
def a1 : Blocks.CombinedAttestation := ⟨⟨0⟩, 1, some ⟨2⟩, .Target 2 ⟨8⟩, none⟩
def a2 : Blocks.CombinedAttestation := ⟨⟨1⟩, 1, some ⟨1⟩, .Timeout 2, some ⟨2, ⟨7⟩⟩⟩
def a3 : Blocks.CombinedAttestation := ⟨⟨0⟩, 2, some ⟨2⟩, .Target 3 ⟨9⟩, none⟩
#eval (ChainState.e1Slashable a0 a1, ChainState.e2Slashable a0 a1, ChainState.slashable a0 a1, ChainState.selfSlashable a0,
       ChainState.selfSlashable a2, ChainState.e1Slashable a0 a2, ChainState.e2Slashable a0 a3)   -- (true, true, true, false, true, false, false)
#eval (ChainState.sgHeadEquivocation a0 a1, ChainState.sgHeadEquivocation a0 a3, ChainState.sgHeadEquivocation a0 a0)   -- (true, false, false)

-- ChainState: §4 the chain state and its quorum reads (q = 4: validator 0 (3) needs one more)
def cfg : ChainState.HeightConfig := ⟨4, 2, 1⟩
def σ0 : ChainState.ChainState := ChainState.initialChainState
#eval (σ0.h, σ0.hJ, σ0.hF, σ0.nj, rootOf σ0.l, rootOf σ0.tH, rootOf σ0.j, rootOf σ0.f, σ0.s, σ0.targetParticipation.size)   -- (1, 0, 0, false, 0, 0, 0, 0, 0, 0)
#eval (ChainState.nonjustifiable cfg 4 0, ChainState.nonjustifiable cfg 4 2, ChainState.nonjustifiable cfg 5 0,
       ChainState.nonjustifiable cfg 8 5, ChainState.nonjustifiable cfg 8 6)   -- (true, false, false, true, false)
def σA : ChainState.ChainState :=
  { σ0 with targetParticipation := NaruStd.Set.of [⟨0⟩, ⟨1⟩], progress := NaruStd.Set.of [⟨1⟩, ⟨2⟩], finalize := NaruStd.Set.of [⟨0⟩] }
#eval (ChainState.targetQuorum env σA, ChainState.progQuorum env σA, ChainState.finalityQuorum env σA)   -- (true, false, false)

-- ChainState: §4 process_attestation at (h = 2, T_h = b1, h_j = 1, J = g, h_F = 0)
def σB : ChainState.ChainState := { σ0 with h := 2, tH := b1, hJ := 1, j := g, hF := 0, s := 2, l := b1 }
def t0 : Blocks.CombinedAttestation := ⟨⟨0⟩, 1, none, .Target 2 ⟨1⟩, some ⟨1, ⟨0⟩⟩⟩   -- target + finality
def t1 : Blocks.CombinedAttestation := ⟨⟨1⟩, 1, none, .Timeout 2, some ⟨1, ⟨5⟩⟩⟩       -- timeout; finality target mismatch
def t2 : Blocks.CombinedAttestation := ⟨⟨2⟩, 1, none, .Target 3 ⟨1⟩, none⟩             -- wrong height: nothing
def t3 : Blocks.CombinedAttestation := ⟨⟨2⟩, 1, none, .Empty, some ⟨1, ⟨0⟩⟩⟩           -- finality only
def r0 := ChainState.processAttestation σB t0
def r1 := ChainState.processAttestation r0 t1
def r2 := ChainState.processAttestation r1 t2
def r3 := ChainState.processAttestation r2 t3
#eval (r0.targetParticipation.size, r0.progress.size, r0.finalize.size)   -- (1, 1, 1)
#eval (r1.targetParticipation.size, r1.progress.size, r1.finalize.size)   -- (1, 2, 1)
#eval r2 == r1                                                             -- true
#eval (r3.targetParticipation == NaruStd.Set.of [⟨0⟩], r3.progress == NaruStd.Set.of [⟨0⟩, ⟨1⟩], r3.finalize == NaruStd.Set.of [⟨0⟩, ⟨2⟩])   -- (true, true, true)

-- ChainState: §4 process_height_events (finality falls through; justification beats progress; the nj latch)
def p3 := ChainState.processHeightEvents env cfg r3
#eval (p3.h, p3.hJ, p3.hF, rootOf p3.j, rootOf p3.f, rootOf p3.tH, p3.nj, p3.finalize.size, p3.targetParticipation.size, p3.progress.size)   -- (3, 1, 1, 0, 0, 1, false, 2, 0, 0)
def p3' := ChainState.processHeightEvents env cfg { r3 with s := 1 }
#eval (p3'.h, p3'.hF, p3'.progress.size)                                    -- (2, 1, 2): timeout gate closed
def p4 := ChainState.processHeightEvents env cfg { r3 with targetParticipation := NaruStd.Set.of [⟨0⟩, ⟨1⟩] }
#eval (p4.h, p4.hJ, p4.hF, rootOf p4.j, rootOf p4.f, p4.finalize.size, p4.nj)   -- (3, 2, 1, 1, 0, 0, false)
def σE : ChainState.ChainState := { σB with h := 3, targetParticipation := NaruStd.Set.of [⟨0⟩, ⟨1⟩] }
def p5 := ChainState.processHeightEvents env cfg σE
#eval (p5.h, p5.nj, p5.hJ)                                                  -- (4, true, 3)
def p6 := ChainState.processHeightEvents env cfg { p5 with targetParticipation := NaruStd.Set.of [⟨0⟩, ⟨1⟩], progress := NaruStd.Set.of [⟨0⟩, ⟨1⟩], s := 5 }
#eval (p6.h, p6.hJ, p6.nj)                                                  -- (5, 3, false): nj blocks justification, progress advances

-- ChainState: entry-bound rows and derive_named over a named chain
def n0 : NamedBlocks.NamedAttestation := ⟨⟨0⟩, 0, none, .Vote 1 ⟨0⟩ false, none⟩
def n1 : NamedBlocks.NamedAttestation := ⟨⟨1⟩, 0, none, .Vote 1 ⟨0⟩ false, none⟩
def nb1 : NamedBlocks.NamedBlock := .Node .Genesis 1 ⟨1⟩ [] [] [n0, n1] ⟨0⟩
def m0 : NamedBlocks.NamedAttestation := ⟨⟨0⟩, 1, none, .Vote 2 ⟨1⟩ false, some ⟨1, ⟨0⟩⟩⟩
def m1 : NamedBlocks.NamedAttestation := ⟨⟨1⟩, 1, none, .Vote 2 ⟨1⟩ true, some ⟨1, ⟨0⟩⟩⟩
def m2 : NamedBlocks.NamedAttestation := ⟨⟨2⟩, 1, none, .Vote 2 ⟨5⟩ false, none⟩   -- entry mismatch
def nb2 : NamedBlocks.NamedBlock := .Node nb1 2 ⟨2⟩ [] [] [m0, m1, m2] ⟨1⟩
def d1 := ChainState.deriveNamed env cfg nb1
#eval (d1.h, d1.hJ, d1.hF, rootOf d1.j, rootOf d1.f, rootOf d1.tH, rootOf d1.l, d1.s, d1.nj, d1.finalize.size)   -- (2, 1, 0, 0, 0, 1, 1, 1, false, 0)
def d2 := ChainState.deriveNamed env cfg nb2
#eval (d2.h, d2.hJ, d2.hF, rootOf d2.j, rootOf d2.f, rootOf d2.tH, rootOf d2.l, d2.s, d2.nj, d2.finalize.size,
       d2.targetParticipation.size, d2.progress.size)                       -- (3, 1, 1, 0, 0, 2, 2, 2, false, 2, 0, 0)
#eval (ChainState.targetedHeightPair d1 m2 == .Empty, ChainState.targetedHeightPair d1 m1 == .Timeout 2,
       ChainState.targetedHeightPair d1 m0 == .Target 2 ⟨1⟩)                -- (true, true, true)
#eval ChainState.deriveNamed env cfg .Genesis == ChainState.initialChainState   -- true

-- Goldfish 後半 (周回 7): FGStore, viability, the FG root and the §5 gate (σ: g 1, b1 2, b1' 1, b2 3, b2' 2, b3 3)
def σ1 : ChainState.ChainState := { σ0 with h := 2 }
def σ2 : ChainState.ChainState := { σ0 with h := 3 }
def sig : Goldfish.ChainStates := tblOf [(b1, σ1), (b2, σ2), (b2', σ1), (b3, σ2)]
def fg : Goldfish.FGStore :=
  ⟨st.t, st.s, st.tree, st.timestampBlock, st.timestampVote, st.gfVotes, st.liveConfirmed, st.latestConfirmed,
   NaruStd.Table.empty, NaruStd.Table.empty, sig, g, b1, 1, 3⟩
#eval ((Goldfish.chainStateOf sig g).h, (Goldfish.chainStateOf sig b2).h, (Goldfish.chainStateOf sig b1').h)   -- (1, 3, 1)
#eval (rootOf (Goldfish.getFgRoot fg), rootOf (Goldfish.getFgRoot { fg with hMax := 2 }), rootOf (Goldfish.getFgRoot { fg with hMax := 1 }))   -- (0, 1, 0)
#eval (Goldfish.viable sig 3 tree g, Goldfish.viable sig 3 tree b1, Goldfish.viable sig 3 tree b1', Goldfish.viable sig 3 tree b2',
       Goldfish.viable sig 3 tree b3, Goldfish.viable sig 4 tree b2', Goldfish.viable sig 4 tree b2)   -- (true, true, false, true, true, false, true)
#eval Goldfish.viableTree sig g 3 tree == NaruStd.Set.of [g, b1, b2, b2', b3]           -- true
#eval Goldfish.viableTree sig b1 4 tree == NaruStd.Set.of [b1, b2, b3]                  -- true
#eval Goldfish.getFilteredBlockTree fg == NaruStd.Set.of [g, b1, b2, b2', b3]           -- true (root F = g)
#eval Goldfish.getFilteredBlockTree { fg with hMax := 2 } == NaruStd.Set.of [b1, b2, b2', b3]   -- true (root J = b1)
#eval Goldfish.getFilteredBlockTreeFrom fg (NaruStd.Set.of [g, b1, b2']) == NaruStd.Set.of [g, b1, b2']   -- true (witnesses within blocks)
def elig (cur : Nat) (b : Blocks.Block) : Bool := Goldfish.goldfishEligible env sig 3 tree cur wv wv 2 b
#eval (elig 2 b1, elig 2 b1', elig 2 b2, elig 2 b2', elig 2 b3, elig 3 b2', elig 3 b3)   -- (true, true, true, true, false, false, true)
#eval rootOf (Goldfish.goldfishForkChoice env sig 3 tree 2 g tree wv wv 2)               -- 2 (g → b1 → b2; b3 not eligible)
#eval rootOf (Goldfish.goldfishForkChoice env sig 3 tree 3 g tree wv wv 2)               -- 4 (cur = 3: b3 eligible by slot)
#eval rootOf (Goldfish.goldfishForkChoice env sig 3 tree 2 (Goldfish.getFgRoot fg) (Goldfish.getFilteredBlockTree fg) wv wv 2)   -- 2
#eval rootOf (Goldfish.goldfishForkChoice env sig 3 tree 2 b1 (NaruStd.Set.of [b2']) wv wv 2)   -- 3 (walk tree holds only b2')
