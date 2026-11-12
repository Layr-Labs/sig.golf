import SigGolfCandidate.OuterExtractGround
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExtractModel
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.Research
open ClaudeWCT.W9.T3M
open Extract Extract.Paired
def pairPrev (answers : Answers) (index : Nat) : Nat → SharedForest.PairRoot
  | 0 => ClaudeWCT.WCT9.ftsStart
  | n+1 => OuterCanonicalModel.root answers index n (pairPrev answers index n)

def first (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)

def physical (coord raw : Nat) : Nat := SharedForest.physicalChild (first coord) raw

def pads (answers : Answers) (index coord branch : Nat) : SharedForest.PairRoot :=
  if coord = 8 then pairPrev answers index 4
  else if first coord then pairPrev answers index (coord/2)
  else SharedForest.nodesPair
    (OuterCanonicalModel.firstNodes answers index (coord/2) (pairPrev answers index (coord/2))) branch

def nodes (answers : Answers) (index coord : Nat) : Array Digest :=
  if coord = 8 then OuterCanonicalModel.nodes answers false index 8 (fun _ => pairPrev answers index 4)
  else if first coord then OuterCanonicalModel.firstNodes answers index (coord/2) (pairPrev answers index (coord/2))
  else OuterCanonicalModel.secondNodes answers index (coord/2) (pairPrev answers index (coord/2))

noncomputable def honestFtsNonce (answers : Answers) (index coord heap : Nat) : Nat :=
  (evalWithAnswerFn answers (OuterExtractGround.nodeAt coord index heap
    ((nodes answers index coord).getD (2*heap) 0) ((nodes answers index coord).getD (2*heap+1) 0))).1

/-- E8: the honest input of a level-3 (heap `8..15`) FTS node carries its honest (found) nonce in the pad slot; Y5:
so does a level-2 (heap `16..31`) node of coordinates `0..3` (`ftsNonceLevel`). -/
noncomputable def honestInput (answers : Answers) : Extract.Pos → HashInput
  | .wctLeaf index coord child => pad64 (Extract.wctLeafInputP index coord child
      (pads answers index coord (physical coord child/64)).1 (wctEnds answers index coord child))
  | .wctNode index coord level node =>
      let heap := 2^(6-level)+node
      pad64 (ClaudeWCT.WCT9.wctTopInput coord index heap
        ((nodes answers index coord).getD (2*heap) 0)
        (if level = 4 then (pads answers index coord (heap/2-2)).2
          else if OuterExtractGround.ftsNonceLevel coord level then
            BitVec.ofNat 128 (honestFtsNonce answers index coord heap % 2 ^ 64) else 0)
        ((nodes answers index coord).getD (2*heap+1) 0))
  | position => Extract.honestInput answers position

theorem nodes_shared (answers : Answers) (index coord : Nat) (hc : coord < 9) :
    nodes answers index coord = OuterCanonicalModel.nodes answers (first coord) index coord
      (pads answers index coord) := by
  by_cases he : coord = 8
  · subst coord
    simp only [nodes, pads, if_pos rfl]
    rfl
  · by_cases hf : first coord = true
    · have hp : coord % 2 = 0 := (of_decide_eq_true hf).2
      have hi : 2*(coord/2) = coord := by omega
      simp only [nodes, if_neg he, hf, if_true, OuterCanonicalModel.firstNodes, hi]
      apply congrArg (OuterCanonicalModel.nodes answers true index coord)
      funext branch
      simp only [pads, if_neg he, hf, if_true]
    · have hff : first coord = false := Bool.eq_false_iff.mpr hf
      have hp : coord % 2 = 1 := by
        have hn : ¬(coord<8 ∧ coord%2=0) := by
          simpa only [first, decide_eq_true_eq] using hf
        omega
      have hi : 2*(coord/2)+1 = coord := by omega
      simp only [nodes, if_neg he, hff, Bool.false_eq_true, if_false,
        OuterCanonicalModel.secondNodes, hi]
      apply congrArg (OuterCanonicalModel.nodes answers false index coord)
      funext branch
      simp only [pads, if_neg he, hff, Bool.false_eq_true, if_false]

theorem nodes_graph (answers : Answers) (index coord : Nat) (hc : coord < 9) :
    OuterCanonicalNode.HeapInv answers (first coord) index coord (pads answers index coord)
      (SharedForest.sharedLeaves answers (first coord) index coord (pads answers index coord))
      (128-SharedForest.heapCut (first coord)) (nodes answers index coord) := by
  rw [nodes_shared answers index coord hc]
  exact OuterCanonicalNode.graph ..


#print axioms nodes_graph
end OuterExtractModel
