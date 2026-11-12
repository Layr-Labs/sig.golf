import SigGolfCandidate.OuterWorldFree
import SigGolfCandidate.OuterPairModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalModel
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest

def heap (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) : M (Array Digest):=
  if first then sharedHeap true index coord pads leaves else OuterHeapMoment.heap coord index pads leaves

def coordinate (first : Bool) (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat→PairRoot) :
    M (Array Digest×List Digest):=do
  let coefs←ftsCoefs index coord
  let rows←sharedRows first index coord selected word coefs pads
  let nodes←heap first index coord pads rows.1
  pure (nodes,rows.2)

def nodes (answers : Answers) (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) : Array Digest:=
  evalWithAnswerFn answers (heap first index coord pads (sharedLeaves answers first index coord pads))

theorem coordinate_eq (first : Bool) (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat→PairRoot) :
    coordinate first index coord selected word pads=OuterForestBudget.buildCoord first index coord selected word pads := by
  cases first with
  | false=>
    simp only [coordinate,heap,Bool.false_eq_true,if_false,OuterForestBudget.buildCoord,
      OuterCoordinate.build,OuterCoordinate.prelude,OuterCoordinate.children,sharedRows,bind_assoc]
  | true=>
    simp only [OuterForestBudget.buildCoord,if_true]
    rw [OuterForestBudget.buildA_eq]
    rfl

theorem coordinate_result (answers : Answers) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat→PairRoot) :
    evalWithAnswerFn answers (coordinate first index coord selected word pads)=
      (nodes answers first index coord pads,List.ofFn (fun i : Fin 6=>chainValue answers index coord (rawChild first selected.val) word i)) := by
  cases first with
  | false=>
    rw [coordinate_eq]
    exact OuterCoordinateCorrectness.build_result answers index coord selected word pads
  | true=>
    rw [coordinate_eq]
    simp only [OuterForestBudget.buildCoord,if_true,OuterForestBudget.buildA_eq]
    exact buildSharedCoordinate_result answers true index coord selected word pads

def firstNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest:=nodes answers true index (2*pair) (fun _=>prev)
def secondNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest:=nodes answers false index (2*pair+1) (nodesPair (firstNodes answers index pair prev))

def opening (answers : Answers) (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aw bw : Rank) (prev : PairRoot) : PairOpening where
  firstValues:=fun i=>(List.ofFn (fun j : Fin 6=>chainValue answers index (2*pair) (rawChild true (firstChild s).val) aw j)).getD i.val 0
  firstPath:=fun i=>authAt (firstNodes answers index pair prev) (firstChild s).val i.val
  secondValues:=fun i=>(List.ofFn (fun j : Fin 6=>chainValue answers index (2*pair+1) (rawChild false (secondChild s).val) bw j)).getD i.val 0
  secondPath:=fun i=>authAt (secondNodes answers index pair prev) (secondChild s).val i.val

def root (answers : Answers) (index pair : Nat) (prev : PairRoot) : PairRoot:=
  ((secondNodes answers index pair prev).getD 2 0,(secondNodes answers index pair prev).getD 3 0)

theorem pair_result (answers : Answers) (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aw bw : Rank) (prev : PairRoot) :
    evalWithAnswerFn answers (OuterForestMoment.pair index pair s aw bw prev)=
      (opening answers index pair s aw bw prev,root answers index pair prev) := by
  exact OuterPairModel.build_result answers index pair s aw bw prev

def commitment (answers : Answers) (index : Nat) : PairRoot:=
  let r0:=root answers index 0 ftsStart
  let r1:=root answers index 1 r0
  let r2:=root answers index 2 r1
  let r3:=root answers index 3 r2
  let last:=nodes answers false index 8 (fun _=>r3)
  (last.getD 2 0,last.getD 3 0)

theorem forest_result (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    (evalWithAnswerFn answers (OuterForestMoment.forest index selected words)).2=commitment answers index := by
  have hfour : List.finRange 4=[0,1,2,3]:=by decide
  simp only [OuterForestMoment.forest,hfour,List.foldlM_cons,List.foldlM_nil,
    evalWithAnswerFn_bind,evalWithAnswerFn_pure,pair_result,
    OuterForestMoment.singleton,OuterForestBudget.buildCoord,Bool.false_eq_true,if_false,
    OuterCoordinateCorrectness.build_result]
  rfl
#print axioms coordinate_eq
#print axioms coordinate_result
#print axioms pair_result
#print axioms forest_result
end OuterCanonicalModel
