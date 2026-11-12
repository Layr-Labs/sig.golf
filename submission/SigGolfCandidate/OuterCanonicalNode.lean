import SigGolfCandidate.OuterCanonicalNonEnc
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalNode
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest

def node (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot) (left right : Digest) : M Digest  := 
  if first=false ∧ heap<4 then Prod.snd <$> OuterGroundCore.nodeAt coord index heap left right
  else sharedNode first coord index heap pads left right

def HeapInv (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (done : Nat) (nodes : Array Digest) : Prop  := 
  nodes.size=256 ∧
    (∀ i, 128 ≤ i → i<256 → nodes.getD i 0=leaves.getD (i-128) 0) ∧
    (∀ i, heapCut first ≤ i → i<128 → 128-done ≤ i → nodes.getD i 0=
      evalWithAnswerFn answers (node first coord index i pads (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)))

theorem graph (answers : Answers) (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) :
    HeapInv answers first index coord pads (sharedLeaves answers first index coord pads)
      (128-heapCut first) (OuterCanonicalModel.nodes answers first index coord pads)  :=  by
  cases first with
  | true=>
    simpa only [HeapInv,SharedHeapInv,node,OuterCanonicalModel.nodes,OuterCanonicalModel.heap,sharedNodes,Bool.true_eq_false,false_and,if_false,if_true]
      using sharedNodes_graph answers true index coord pads
  | false=>
    have hg := sharedNodes_graph answers false index coord pads
    refine ⟨OuterCoordinateCorrectness.nodes_size answers index coord pads,?_,?_⟩
    · intro i hi hj
      change (OuterCoordinateCorrectness.nodes answers index coord pads).getD i 0=_
      rw [OuterCoordinateCorrectness.nodes_agree answers index coord pads i (by omega)]
      exact hg.2.1 i hi hj
    · intro i hi hj hk
      change (OuterCoordinateCorrectness.nodes answers index coord pads).getD i 0=_
      have hi2 : 2 ≤ i := hi
      by_cases h : i<4
      · simp only [node,true_and,if_pos h,evalWithAnswerFn_map]
        rcases (show i=2 ∨ i=3 by omega) with rfl|rfl
        · exact OuterCoordinateCorrectness.top2 answers index coord pads
        · exact OuterCoordinateCorrectness.top3 answers index coord pads
      · simp only [node,true_and,if_neg h]
        change _=evalWithAnswerFn answers (sharedNode false coord index i pads
          ((OuterCoordinateCorrectness.nodes answers index coord pads).getD (2*i) 0)
          ((OuterCoordinateCorrectness.nodes answers index coord pads).getD (2*i+1) 0))
        rw [OuterCoordinateCorrectness.nodes_agree answers index coord pads i (by omega),
          OuterCoordinateCorrectness.nodes_agree answers index coord pads (2*i) (by omega),
          OuterCoordinateCorrectness.nodes_agree answers index coord pads (2*i+1) (by omega)]
        exact hg.2.2 i hi hj hk
#print axioms graph
end OuterCanonicalNode
