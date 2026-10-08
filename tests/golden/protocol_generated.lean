-- 生成 Model(Protocol 層: Schedule / StoreBase / ForkChoice.Views / ForkChoice.Goldfish / ChainState(周回 7)/ ValidatorClient /
-- Grades / ForkChoice.Head / Duties.Inputs(周回 8))の値。
-- tests/golden/protocol_handwritten.lean(手書き Model)と同じ順で同じ値を出すこと。golden test の予行(周回 6〜8)。
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

-- ValidatorClient (周回 8): §5.3 the record Λ, the pair rules, create_attestation and the named codec
def idOf (o : Option Identifiers.BlockId) : Option Nat := o.map (·.value)
def rec0 := ValidatorClient.initialRecord
#eval ((ValidatorClient.finalityPair rec0 2 ⟨7⟩ 1).map (fun p => (p.height, p.target.value)),
       (ValidatorClient.finalityPair rec0 2 ⟨7⟩ 2).isNone,
       (ValidatorClient.finalityPair (ValidatorClient.withTarget rec0 2 ⟨8⟩) 2 ⟨7⟩ 1).isNone,
       (ValidatorClient.finalityPair (ValidatorClient.withTarget rec0 2 ⟨7⟩) 2 ⟨7⟩ 1).isSome,
       (ValidatorClient.finalityPair (ValidatorClient.withTimeout rec0 2) 2 ⟨7⟩ 1).isNone,
       (ValidatorClient.finalityPair (ValidatorClient.withLock rec0 2 ⟨9⟩) 2 ⟨7⟩ 1).isNone,
       (ValidatorClient.finalityPair (ValidatorClient.withLock rec0 2 ⟨7⟩) 2 ⟨7⟩ 1).isSome)   -- (some (2, 7), true, true, true, true, true, true)
def f35 : Option (Nat × Identifiers.BlockId × Bool) := some (3, ⟨5⟩, false)
def f35t : Option (Nat × Identifiers.BlockId × Bool) := some (3, ⟨5⟩, true)
-- the seven rows of the height_pair table in order, then the own-lock override (same height / other height)
#eval (ValidatorClient.heightPair rec0 none none == .Empty,
       ValidatorClient.heightPair (ValidatorClient.withTimeout rec0 3) f35 none == .Timeout 3,
       ValidatorClient.heightPair (ValidatorClient.withLock rec0 3 ⟨5⟩) f35 none == .Target 3 ⟨5⟩,
       ValidatorClient.heightPair (ValidatorClient.withLock rec0 3 ⟨6⟩) f35 none == .Empty,
       ValidatorClient.heightPair (ValidatorClient.withTarget rec0 3 ⟨5⟩) f35t none == .Target 3 ⟨5⟩,
       ValidatorClient.heightPair (ValidatorClient.withTarget rec0 3 ⟨6⟩) f35 none == .Timeout 3,
       ValidatorClient.heightPair rec0 f35 none == .Target 3 ⟨5⟩,
       ValidatorClient.heightPair rec0 f35t none == .Timeout 3,
       ValidatorClient.heightPair rec0 f35 (some ⟨3, ⟨6⟩⟩) == .Empty,
       ValidatorClient.heightPair rec0 f35t (some ⟨3, ⟨5⟩⟩) == .Target 3 ⟨5⟩,
       ValidatorClient.heightPair rec0 f35 (some ⟨4, ⟨6⟩⟩) == .Target 3 ⟨5⟩)   -- all true
def ra1 := ValidatorClient.recordAttestation rec0 ⟨⟨0⟩, 1, none, .Target 3 ⟨5⟩, some ⟨2, ⟨7⟩⟩⟩
def ra2 := ValidatorClient.recordAttestation ra1 ⟨⟨0⟩, 2, none, .Timeout 3, none⟩
def ra3 := ValidatorClient.recordAttestation ra2 ⟨⟨0⟩, 3, none, .Target 3 ⟨9⟩, none⟩
#eval (idOf (ValidatorClient.recordTarget ra1 3), idOf (ValidatorClient.recordLock ra1 2), ValidatorClient.recordTimeout ra1 3,
       ValidatorClient.recordTimeout ra2 3, idOf (ValidatorClient.recordTarget ra3 3), idOf (ValidatorClient.recordTarget ra3 4),
       idOf (ValidatorClient.recordLock ra3 3))   -- (some 5, some 7, false, true, some 5, none, none): target[3] is write-once
def ca1 := ValidatorClient.createAttestation rec0 ⟨0⟩ 1 (some ⟨1⟩) f35 2 ⟨7⟩ 1
#eval (ca1.2 == ⟨⟨0⟩, 1, some ⟨1⟩, .Target 3 ⟨5⟩, some ⟨2, ⟨7⟩⟩⟩, idOf (ValidatorClient.recordTarget ca1.1 3), idOf (ValidatorClient.recordLock ca1.1 2))   -- (true, some 5, some 7)
def ca2 := ValidatorClient.createAttestation ca1.1 ⟨0⟩ 2 none (some (3, ⟨6⟩, false)) 2 ⟨7⟩ 1
#eval (ca2.2 == ⟨⟨0⟩, 2, none, .Timeout 3, some ⟨2, ⟨7⟩⟩⟩, ValidatorClient.recordTimeout ca2.1 3)   -- (true, true): recorded target 5 ≠ 6 falls through to a timeout
def ca3 := ValidatorClient.createAttestation ca2.1 ⟨0⟩ 3 none f35 2 ⟨7⟩ 2
#eval ca3.2 == ⟨⟨0⟩, 3, none, .Timeout 3, none⟩   -- true (h_F = h_j: no finality pair; timeout[3] set)
#eval (ValidatorClient.encodeHeight f35 (.Target 3 ⟨5⟩) == .Vote 3 ⟨5⟩ false, ValidatorClient.encodeHeight f35 (.Timeout 3) == .Vote 3 ⟨5⟩ true,
       ValidatorClient.encodeHeight none (.Target 3 ⟨5⟩) == .Empty, ValidatorClient.encodeHeight f35 .Empty == .Empty)   -- (true, true, true, true)
#eval (ValidatorClient.rememberTimeout NaruStd.Set.empty (.Vote 3 ⟨5⟩ true) == NaruStd.Set.of [(3, ⟨5⟩)],
       (ValidatorClient.rememberTimeout NaruStd.Set.empty (.Vote 3 ⟨5⟩ false)).isEmpty)   -- (true, true)
def inp1 : ValidatorClient.RecordInput := ⟨⟨0⟩, 1, some ⟨1⟩, f35, 2, ⟨7⟩, 1⟩
def nc1 := ValidatorClient.namedCreate ValidatorClient.initialNamedRecord inp1
#eval (nc1.2 == ⟨⟨0⟩, 1, some ⟨1⟩, .Vote 3 ⟨5⟩ false, some ⟨2, ⟨7⟩⟩⟩, nc1.1.timeoutHistory.isEmpty, idOf (ValidatorClient.recordTarget nc1.1.legacy 3))   -- (true, true, some 5)
def inp2 : ValidatorClient.RecordInput := ⟨⟨0⟩, 2, none, some (3, ⟨6⟩, false), 2, ⟨7⟩, 1⟩
def nc2 := ValidatorClient.namedCreate nc1.1 inp2
#eval (nc2.2 == ⟨⟨0⟩, 2, none, .Vote 3 ⟨6⟩ true, some ⟨2, ⟨7⟩⟩⟩, nc2.1.timeoutHistory == NaruStd.Set.of [(3, ⟨6⟩)],
       ValidatorClient.recordTimeout nc2.1.legacy 3)   -- (true, true, true): the named timeout carries the source entry 6

-- Grades (周回 8): §6.1 schedule (R = 3, η_SG = 2), the grade view and the §6 store
def hc : Grades.HealConfig := ⟨3, 2⟩
#eval (Grades.roundOf hc 7, Grades.openingSlot hc 2, Grades.actionTime hc 2 1)   -- (2, 6, 36)
#eval (Grades.headCovers tree b1 (some ⟨2⟩), Grades.headCovers tree b2' (some ⟨2⟩), Grades.headCovers tree b1 none, Grades.headCovers tree b1 (some ⟨99⟩))   -- (true, false, false, false)
#eval (Grades.gradeView fg).filteredTree == NaruStd.Set.of [g, b1, b2, b2', b3]   -- true
-- chains, the deepest clear ancestor, clipping
#eval ((Grades.chainOf b3).map rootOf, (Grades.chainUp 1 b3).map rootOf, (Grades.chainUp 0 b3).map rootOf, (Grades.chainOf g).map rootOf)   -- ([4, 2, 1, 0], [4, 2], [4], [0])
#eval ((Grades.deepestClear none b3 (fun _ => true)).map rootOf, (Grades.deepestClear (some b1) b3 (fun b => Blocks.root b != ⟨4⟩)).map rootOf,
       (Grades.deepestClear (some b2') b3 (fun _ => true)).isNone, (Grades.deepestClear none b3 (fun b => Blocks.slot b == 0)).map rootOf)   -- (some 4, some 2, true, some 0)
#eval (rootOf (Grades.clipGrade b3 b2'), rootOf (Grades.clipGrade b3 b2), rootOf (Grades.clipGrade g b3), rootOf (Grades.clipGrade b2' b3))   -- (1, 4, 0, 1)
-- frames: clear / allClosed / grade2Block / anchor
def frRoots (fr : Grades.Frame) := (fr.g0.map (fun o => o.map rootOf), fr.g1.map (fun o => o.map rootOf), fr.g2.map (fun o => o.map rootOf))
def frA : Grades.Frame := ⟨some (some b1), some none, some (some b3)⟩
def frB : Grades.Frame := ⟨none, some (some b2'), some (some b3)⟩
def frC : Grades.Frame := ⟨some (some b2), none, none⟩
#eval (Grades.clear frC b3, Grades.clear frC b2', Grades.clear frB b2', Grades.clear ⟨some none, none, none⟩ b2')   -- (true, false, true, true)
#eval (Grades.allClosed frA, Grades.allClosed frB, Grades.allClosed Grades.pendingFrame, Grades.allClosed Grades.emptyFrame)   -- (true, false, false, true)
#eval ((Grades.grade2Block fg frA).map rootOf, (Grades.grade2Block fg frB).isNone, (Grades.grade2Block fg ⟨some none, some none, some (some b2')⟩).map rootOf,
       (Grades.grade2Block fg ⟨some none, some none, some (some b1')⟩).map rootOf, (Grades.grade2Block fg Grades.emptyFrame).isNone)   -- (some 4, true, some 3, some 0, true)
#eval (rootOf (Grades.anchor env hc fg 0 (some (some b2'))), rootOf (Grades.anchor env hc fg 0 (some none)), rootOf (Grades.anchor env hc fg 0 none),
       rootOf (Grades.anchor env hc fg 0 (some (some b1'))), rootOf (Grades.anchor env hc fg 0 (some (some b3))))   -- (3, 0, 0, 0, 4)
-- the support / opposition algebra on tokens (covers = head_covers in the processed tree)
def tk (r : Nat) (k : Option Nat) : Grades.Token := ⟨r, k.map fun n => ⟨n⟩⟩
def early1 := NaruStd.Set.of [tk 1 (some 2), tk 2 (some 4)]
def late1 := NaruStd.Set.of [tk 3 (some 4)]
def raw1 := NaruStd.Set.of [tk 1 (some 2), tk 2 (some 4), tk 3 (some 4)]
def raw2 := NaruStd.Set.of [tk 1 (some 2), tk 2 (some 4), tk 3 (some 4), tk 3 (some 3)]
def cov : Option Identifiers.BlockId → Blocks.Block → Bool := fun k b => Grades.headCovers tree b k
#eval (Grades.cleanFrom raw1 1, Grades.cleanFrom raw2 2, Grades.cleanFrom raw2 3, Grades.cleanFrom raw2 4)   -- (true, false, false, true)
#eval (Grades.supports cov early1 late1 raw1 b1, Grades.supports cov early1 late1 raw1 b2', Grades.supports cov early1 late1 raw2 b1,
       Grades.supports cov NaruStd.Set.empty late1 raw1 b1)   -- (true, false, false, false)
#eval (Grades.opposes cov early1 late1 raw1 b2', Grades.opposes cov early1 late1 raw1 b1, Grades.opposes cov early1 late1 raw2 b1,
       Grades.opposes cov early1 NaruStd.Set.empty raw1 b2')   -- (true, false, true, false)
-- SG votes for the grade inputs (η = 2, r = 3: window [1, 2]); validator 0 confirms b2 then b3, validator 1 confirms b2'
def u1 : Goldfish.SGVote := ⟨⟨0⟩, 1, some ⟨2⟩⟩   -- confirmed b2 (block stamped 9), vote stamped 5
def u2 : Goldfish.SGVote := ⟨⟨0⟩, 2, some ⟨4⟩⟩   -- confirmed b3 (block stamped 10), vote stamped 15
def u3 : Goldfish.SGVote := ⟨⟨1⟩, 2, some ⟨3⟩⟩   -- confirmed b2' (block stamped 20), vote stamped 7
def u4 : Goldfish.SGVote := ⟨⟨0⟩, 3, none⟩        -- ⊥, vote stamped 20
def u5 : Goldfish.SGVote := ⟨⟨0⟩, 2, some ⟨99⟩⟩  -- unknown root, never stamped
def u6 : Goldfish.SGVote := ⟨⟨1⟩, 3, some ⟨2⟩⟩   -- confirmed b2, vote stamped 9
def sgTbl : NaruStd.Table Nat (NaruStd.Set Goldfish.SGVote) :=
  tblOf [(1, NaruStd.Set.of [u1]), (2, NaruStd.Set.of [u2, u3, u5]), (3, NaruStd.Set.of [u4, u6])]
def sgStamp : NaruStd.Table Goldfish.SGVote Time.Stamp := tblOf [(u1, .At 5), (u2, .At 15), (u3, .At 7), (u4, .At 20), (u6, .At 9)]
def hs : Goldfish.FGStore := { fg with sgVotes := sgTbl, timestampSgVote := sgStamp }
def gv2 := Grades.gradeView hs
#eval (Grades.rawInputs gv2 2 3 16 ⟨0⟩ == NaruStd.Set.of [u1, u2], Grades.rawInputs gv2 2 3 10 ⟨0⟩ == NaruStd.Set.of [u1],
       Grades.rawInputs gv2 2 4 30 ⟨0⟩ == NaruStd.Set.of [u2, u4], Grades.rawInputs gv2 2 3 16 ⟨1⟩ == NaruStd.Set.of [u3])   -- (true, true, true, true)
#eval (Grades.bodyReady gv2 g 16 u1, Grades.bodyReady gv2 g 16 u2, Grades.bodyReady gv2 b2 16 u3, Grades.bodyReady gv2 b2' 16 u2,
       Grades.bodyReady gv2 g 16 u4, Grades.bodyReady gv2 g 16 u5, Grades.bodyReady gv2 g 8 u1)   -- (true, true, false, false, true, false, false)
#eval (Grades.interpretedInputs gv2 g 2 3 16 ⟨0⟩ == NaruStd.Set.of [u1, u2], (Grades.interpretedInputs gv2 b2' 2 3 16 ⟨0⟩).isEmpty)   -- (true, true)
#eval (Grades.rawView gv2 2 3 16 ⟨0⟩ == NaruStd.Set.of [tk 1 (some 2), tk 2 (some 4)], (Grades.readyView gv2 b2' 2 3 16 ⟨0⟩).isEmpty)   -- (true, true)
-- positive / opposing / gradeBool / freezeRoot at (F = g, η = 2, r = 3, early = 10, late = 16): only validator 0 has a body
def pos (f : Blocks.Block) (v : Nat) (b : Blocks.Block) : Bool := Grades.positive gv2 f 2 3 10 16 ⟨v⟩ b
def opp (f : Blocks.Block) (v : Nat) (b : Blocks.Block) : Bool := Grades.opposing gv2 f 2 3 10 16 ⟨v⟩ b
#eval (pos g 0 g, pos g 0 b1, pos g 0 b2, pos g 0 b1', pos g 0 b2', pos g 0 b3)   -- (true, true, true, false, false, false)
#eval (opp g 0 g, opp g 0 b1, opp g 0 b2, opp g 0 b1', opp g 0 b2', opp g 0 b3)   -- (false, false, false, true, true, true)
#eval (pos g 1 b1, opp g 1 b1, pos g 2 b1, opp g 2 b1, pos b2' 0 g, opp b2' 0 b2')   -- (false, false, false, false, false, false)
def grd (f : Blocks.Block) (b : Blocks.Block) : Bool := Grades.gradeBool env gv2 f 2 3 10 16 b
#eval (grd g g, grd g b1, grd g b2, grd g b1', grd g b2', grd g b3)   -- (true, true, true, false, false, false)
#eval ((Grades.freezeRoot env gv2 g 2 3 10 16).map rootOf, (Grades.freezeRoot env gv2 b2' 2 3 10 16).isNone)   -- (some 2, true)
-- with cutoffs 62 / 70 every stamp passes: validator 1 (weight 1) grades b2' against validator 0 (weight 3)
#eval ((Grades.freezeRoot env gv2 g 2 3 62 70).map rootOf, Grades.gradeBool env gv2 g 2 3 62 70 b2', Grades.gradeBool env gv2 g 2 3 62 70 b2)   -- (some 4, false, true)
-- the phase cache (R = 3, Δ = 2: round r opens at t = 24r)
#eval ((Grades.earlyOffset .G0, Grades.earlyOffset .G1, Grades.earlyOffset .G2), (Grades.lateOffset .G0, Grades.lateOffset .G1, Grades.lateOffset .G2),
       (Grades.domainOffset .G0, Grades.domainOffset .G1, Grades.domainOffset .G2))   -- ((-3, -4, -5), (-3, -2, -1), (1, 0, -1))
#eval (Grades.openingTime env hc 1, Grades.earlyTime env hc 1 .G2, Grades.lateTime env hc 1 .G2, Grades.domainTime env hc 1 .G2,
       Grades.domainTime env hc 1 .G1, Grades.domainTime env hc 1 .G0)   -- (24, 14, 22, 22, 24, 26)
#eval (Grades.phaseResult frA .G1 == some none, frRoots (Grades.putPhase Grades.pendingFrame .G1 (some b2)), frRoots Grades.emptyFrame)   -- (true, (none, some (some 2), none), (some none, some none, some none))
-- round 3 opens at 72: G2 freezes at 70 (62 / 70), G1 at 72 (64 / 68), G0 at 74 (66 / 66)
def c70 := Grades.completeOne env hc hs 3 70 .G2 Grades.pendingFrame
#eval (frRoots c70, frRoots (Grades.completeOne env hc hs 3 69 .G2 Grades.pendingFrame), frRoots (Grades.completeOne env hc hs 3 70 .G2 Grades.emptyFrame))   -- ((none, none, some (some 4)), (none, none, none), (some none, some none, some none))
def cf70 := Grades.completeFrame env hc hs 3 70 Grades.pendingFrame
def cf72 := Grades.completeFrame env hc hs 3 72 cf70
def cf74 := Grades.completeFrame env hc hs 3 74 cf72
#eval (frRoots cf70, frRoots cf72, frRoots cf74)   -- ((none, none, some (some 4)), (none, some (some 4), some (some 4)), (some (some 4), some (some 4), some (some 4)))
#eval (frRoots (Grades.clipFrame b2' ⟨some (some b3), some none, none⟩), frRoots (Grades.clipFrame g cf74))   -- ((some (some 1), some none, none), (some (some 4), some (some 4), some (some 4)))
def cacheRoots (c : Grades.Cache) := (c.round, frRoots c.current, frRoots c.next)
def c0 := Grades.initialCache
def c1 := Grades.onPhaseTick env hc hs 70 c0   -- t = 70 is slot 8 = round 2; the next round's G2 freezes
def c2 := Grades.onPhaseTick env hc hs 72 c1   -- round 3 opens: the cache rotates and G1 freezes
def c3 := Grades.onPhaseTick env hc hs 74 c2   -- G0 freezes
def c4 := Grades.onPhaseTick env hc hs 94 c3   -- round 4's G2 (window [2, 3]: validator 0's latest token is ⊥) completes empty
def c5 := Grades.onPhaseTick env hc hs 96 c4   -- round 4 opens
#eval (cacheRoots c0, cacheRoots c1)   -- ((0, (some none, some none, some none), (none, none, none)), (2, (none, none, none), (none, none, some (some 4))))
#eval cacheRoots c2   -- (3, (none, some (some 4), some (some 4)), (none, none, none))
#eval cacheRoots c3   -- (3, (some (some 4), some (some 4), some (some 4)), (none, none, none))
#eval cacheRoots c4   -- (3, (some (some 4), some (some 4), some (some 4)), (none, none, some none))
#eval cacheRoots c5   -- (4, (none, some none, some none), (none, none, none))
#eval (cacheRoots (Grades.alignRound c1 3), (Grades.alignRound c1 2).round, cacheRoots (Grades.alignRound c1 5))   -- ((3, (none, none, some (some 4)), (none, none, none)), 2, (5, (none, none, none), (none, none, none)))
#eval (frRoots (Grades.cacheAtRound c1 2), frRoots (Grades.cacheAtRound c1 3), frRoots (Grades.cacheAtRound c1 4))   -- ((none, none, none), (none, none, some (some 4)), (none, none, none))
-- the frame contract
def rd3 := Grades.frameGradeRead c1 env hc hs 3
#eval (rootOf rd3.anchor, rd3.q2.isNone, rd3.rawG2, Grades.clear rd3.frame b2', frRoots (Grades.readFrame c1 hs 3))   -- (0, true, true, true, (none, none, some (some 4)))
#eval rootOf (Grades.currentSGVote hs rd3)   -- 0 (the clear walk from the anchor g reaches live_confirmed = g)
def rd3c := Grades.frameGradeRead c3 env hc hs 3
#eval (rootOf rd3c.anchor, rd3c.q2.map rootOf, rd3c.rawG2, Grades.clear rd3c.frame b2', Grades.clear rd3c.frame b2)   -- (4, some 4, true, false, true)
#eval (rootOf (Grades.currentSGVote hs rd3c), rootOf (Grades.currentSGVote { hs with liveConfirmed := b3 } rd3c),
       rootOf (Grades.currentSGVote hs { rd3c with q2 := none }), rootOf (Grades.currentSGVote hs { rd3c with q2 := none, rawG2 := false }))   -- (4, 4, 0, 4)
#eval ((Grades.frameSgCandidate c1 env hc hs 0).isNone, (Grades.frameSgCandidate c3 env hc { hs with s := 9 } 0).map rootOf,
       (Grades.frameStableRoot c1 env hc hs 3).map rootOf, (Grades.frameStableRoot c1 env hc hs 0).map rootOf)   -- (true, some 4, some 4, some 0)

-- Head (周回 8): the SG root and the composed head over the saved grades (hs.s = 2 → round 0)
def cB : Grades.Cache := ⟨0, ⟨none, some (some b2'), none⟩, Grades.pendingFrame⟩
def cC : Grades.Cache := ⟨0, ⟨none, some (some b3), none⟩, Grades.pendingFrame⟩
#eval (rootOf (Head.getSgRootWith c1 env hc hs 3), rootOf (Head.getSgRootWith cB env hc hs 0), rootOf (Head.getSgRootWith c3 env hc hs 3),
       rootOf (Head.getSgRootWith cC env hc { hs with f := b2' } 0), frRoots (Grades.readFrame cC { hs with f := b2' } 0))   -- (0, 3, 4, 3, (none, some (some 1), none)): the saved b3 clips to b1 under F = b2'
#eval (rootOf (Head.getHeadWith cB env hc hs wv wv 2), rootOf (Head.getHeadWith c1 env hc hs wv wv 2),
       rootOf (Head.getHeadInTreeWithLayer cB env hc hs (NaruStd.Set.of [g, b1]) wv wv 2))   -- (3, 2, 3)

-- Duties.Inputs (周回 8): the shared proposal / attestation reads (hs.s = 2 → round 0; new_root s = s + 1)
def newRoot : Identifiers.ValidatorId → Nat → Identifiers.BlockId := fun _ s => ⟨s + 1⟩
def pi1 := Duties.Inputs.proposalInput newRoot c1 env hc ⟨⟨0⟩⟩ hs
#eval (rootOf pi1.parent, pi1.slot, pi1.root.value, pi1.gfVotes == [vA, vB, vC, vD], pi1.gfSupportVotes == [vA, vB, vC], pi1.proposer.value)   -- (3, 2, 3, true, true, 0)
def ai1 := Duties.Inputs.attestationInput c1 env hc ⟨⟨0⟩⟩ hs
#eval (ai1.valIndex.value, ai1.round, idOf ai1.confirmed, ai1.fields.isNone, ai1.hJ, ai1.j.value, ai1.hF)   -- (0, 0, some 0, true, 0, 0, 0)
def cD : Grades.Cache := ⟨0, ⟨some (some b2), some (some b2), some (some b3)⟩, Grades.pendingFrame⟩
#eval ((Duties.Inputs.grade2BlockWith cD env hc hs 0).map rootOf, (Duties.Inputs.grade2BlockWith c1 env hc hs 0).isNone)   -- (some 4, true)
#eval (rootOf (Duties.Inputs.getSgVoteWith cD env hc hs 0 (some b3)), rootOf (Duties.Inputs.getSgVoteWith cD env hc { hs with liveConfirmed := b3 } 0 (some b3)),
       rootOf (Duties.Inputs.getSgVoteWith cD env hc hs 0 none), rootOf (Duties.Inputs.getSgVoteWith c1 env hc hs 0 none))   -- (4, 4, 0, 0)
#eval ((Duties.Inputs.fgSourceWith cD env hc hs 0 (some b3)).map rootOf, (Duties.Inputs.fgSourceWith cD env hc hs 0 none).isNone,
       (Duties.Inputs.fgSourceWith cD env hc { hs with liveConfirmed := b3 } 0 (some b2)).map rootOf,
       (Duties.Inputs.fgSourceWith cD env hc { hs with liveConfirmed := b2' } 0 (some b1)).map rootOf)   -- (some 4, true, some 4, some 1)
def fv1 := Duties.Inputs.getFgVoteWith cD env hc hs 0 (some b3)
#eval (fv1.1.map (fun t => (t.1, t.2.1.value, t.2.2)), fv1.2.1, fv1.2.2.1.value, fv1.2.2.2)   -- (some (3, 0, false), 0, 0, 0): head b2 (b3 is not eligible), source b3
def ai2 := Duties.Inputs.attestationInput cD env hc ⟨⟨1⟩⟩ hs
#eval (ai2.valIndex.value, ai2.round, idOf ai2.confirmed, ai2.fields.map (fun t => (t.1, t.2.1.value, t.2.2)), ai2.hJ, ai2.j.value, ai2.hF)   -- (1, 0, some 4, some (3, 0, false), 0, 0, 0)
