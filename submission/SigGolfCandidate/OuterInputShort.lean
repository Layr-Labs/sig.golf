import SigGolfCandidate.OuterPairedSatHeap
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterInputShort
open ClaudeWCT
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
attribute [local irreducible] OuterCanonicalModel.nodes
theorem sharedNodes_short {A T : Answers} (hAT : ShortAgree A T)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    OuterCanonicalModel.nodes A first index coord.val pads = OuterCanonicalModel.nodes T first index coord.val pads := by
  unfold OuterCanonicalModel.nodes
  rw [sharedLeaves_short hAT first index coord]
  exact OuterCanonicalShort.hybrid_short first index coord.val pads _ A T hAT

theorem expectedPairRoot_short {A T : Answers} (hAT : ShortAgree A T)
    (index : Nat) (pair : Fin 4) (prev : PairRoot) :
    OuterCanonicalModel.root A index pair.val prev = OuterCanonicalModel.root T index pair.val prev := by
  have ha : OuterCanonicalModel.firstNodes A index pair.val prev = OuterCanonicalModel.firstNodes T index pair.val prev :=
    sharedNodes_short hAT true index ⟨2 * pair.val, by have := pair.isLt; omega⟩ _
  have hb : OuterCanonicalModel.secondNodes A index pair.val prev = OuterCanonicalModel.secondNodes T index pair.val prev := by
    unfold OuterCanonicalModel.secondNodes
    rw [ha]
    exact sharedNodes_short hAT false index ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ _
  unfold OuterCanonicalModel.root
  rw [hb]
theorem nodeAt_short (coord index heap : Nat) (left right : Digest) : ShortRespects (OuterExtractGround.nodeAt coord index heap left right) := by
  unfold OuterExtractGround.nodeAt
  split
  · exact OuterCanonicalShort.node_short _ _ _ _ _
  · exact ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.ftsNodeAt_short _ _ _ _ _
theorem pairPrev_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat) (hp : pair ≤ 4) :
    OuterExtractModel.pairPrev A index pair = OuterExtractModel.pairPrev T index pair := by
  induction pair with
  | zero => rfl
  | succ pair ih =>
      simp only [OuterExtractModel.pairPrev]
      rw [ih (by omega)]
      exact expectedPairRoot_short hAT index ⟨pair,by omega⟩ _

theorem firstNodes_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat)
    (hp : pair<4) (prev : PairRoot) : OuterCanonicalModel.firstNodes A index pair prev = OuterCanonicalModel.firstNodes T index pair prev :=
  sharedNodes_short hAT true index ⟨2*pair,by omega⟩ _

theorem secondNodes_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat)
    (hp : pair<4) (prev : PairRoot) : OuterCanonicalModel.secondNodes A index pair prev = OuterCanonicalModel.secondNodes T index pair prev := by
  unfold OuterCanonicalModel.secondNodes
  rw [firstNodes_short hAT index pair hp]
  exact sharedNodes_short hAT false index ⟨2*pair+1,by omega⟩ _

theorem pads_short {A T : Answers} (hAT : ShortAgree A T) (index coord branch : Nat) (hc : coord<9) :
    OuterExtractModel.pads A index coord branch = OuterExtractModel.pads T index coord branch := by
  unfold OuterExtractModel.pads
  split
  · rw [pairPrev_short hAT index 4 (by omega)]
  · rename_i hn
    split
    · rw [pairPrev_short hAT index (coord/2) (by omega)]
    · rw [pairPrev_short hAT index (coord/2) (by omega),firstNodes_short hAT index (coord/2) (by omega)]

theorem nodes_short {A T : Answers} (hAT : ShortAgree A T) (index coord : Nat) (hc : coord<9) :
    OuterExtractModel.nodes A index coord = OuterExtractModel.nodes T index coord := by
  unfold OuterExtractModel.nodes
  split
  · rw [pairPrev_short hAT index 4 (by omega)]
    exact sharedNodes_short hAT false index ⟨8,by decide⟩ _
  · rename_i hn
    split
    · rw [pairPrev_short hAT index (coord/2) (by omega),firstNodes_short hAT index (coord/2) (by omega)]
    · rw [pairPrev_short hAT index (coord/2) (by omega),secondNodes_short hAT index (coord/2) (by omega)]

theorem honestInput_short {A T : Answers} (hAT : ShortAgree A T)
    (position : Extract.Pos) (hb : Extract.Paired.Bounded position) :
    OuterExtractModel.honestInput A position = OuterExtractModel.honestInput T position := by
  cases position with
  | chain | leaf | node | wctChain => exact ClaudeWCT.W9.T3.Security.Wots.Ref.honestInput_short hAT _ hb.legacy
  | forest => exact hb.elim
  | wctLeaf index coord child =>
      obtain ⟨hi,hc,hch⟩ := hb
      simp only [OuterExtractModel.honestInput]
      rw [pads_short hAT index coord _ hc,ClaudeWCT.W9.T3.Security.Wots.Ref.wctEnds_short hAT index coord child hc hch]
  | wctNode index coord level node =>
      have hc := hb.legacy.2.1
      simp only [OuterExtractModel.honestInput, OuterExtractModel.honestFtsNonce]
      rw [nodes_short hAT index coord hc,pads_short hAT index coord _ hc,
        nodeAt_short _ _ _ _ _ A T hAT]

theorem honestInput_short_all {A T : Answers} (hAT : ShortAgree A T)
    (position : Extract.Pos) (hb : position.Bounded) :
    OuterExtractModel.honestInput A position = OuterExtractModel.honestInput T position := by
  cases position with
  | chain | leaf | node | wctChain | forest => exact ClaudeWCT.W9.T3.Security.Wots.Ref.honestInput_short hAT _ hb
  | wctLeaf index coord child =>
      obtain ⟨hi,hc,hch⟩ := hb
      simp only [OuterExtractModel.honestInput]
      rw [pads_short hAT index coord _ hc,ClaudeWCT.W9.T3.Security.Wots.Ref.wctEnds_short hAT index coord child hc hch]
  | wctNode index coord level node =>
      have hc := hb.2.1
      simp only [OuterExtractModel.honestInput, OuterExtractModel.honestFtsNonce]
      rw [nodes_short hAT index coord hc,pads_short hAT index coord _ hc,
        nodeAt_short _ _ _ _ _ A T hAT]
#print axioms honestInput_short_all
#print axioms honestInput_short
end OuterInputShort
