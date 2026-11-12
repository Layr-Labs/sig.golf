import SigGolfCandidate.OuterPairedSatNode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalModel
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh

def step (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (nodes : Array Digest) (h : Nat) : M (Array Digest) := do
  let v←OuterCanonicalNode.node first coord index h pads (nodes.getD (2*h) 0) (nodes.getD (2*h+1) 0)
  pure (nodes.set! h v)

theorem fold_inner (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (xs : List Nat)
    (hx : ∀ h∈xs, 4≤h) (nodes : Array Digest) :
    xs.foldlM (step first index coord pads) nodes=xs.foldlM (heapStep first index coord pads) nodes := by
  induction xs generalizing nodes with
  | nil=>rfl
  | cons h xs ih=>
    have hh:=hx h (by simp)
    simp only [List.foldlM_cons,step,OuterCanonicalNode.node,if_neg (show ¬(first=false ∧ h<4) by omega),heapStep]
    congr 1
    funext v
    exact ih (fun j hj=>hx j (by simp [hj])) _

theorem heap_fold (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    heap first index coord pads leaves=
      (List.range' (heapCut first) (128-heapCut first)).reverse.foldlM (step first index coord pads)
        ((List.replicate 128 (0:Digest)++leaves).toArray) := by
  cases first with
  | true=>
    simp only [heap,if_true,heapCut,if_true]
    rw [fold_inner true index coord pads _ (by intro h hh;have := List.mem_range'.mp (List.mem_reverse.mp hh);omega)]
    rfl
  | false=>
    have hl : (List.range' 2 126).reverse=(List.range' 4 124).reverse++[3,2] := by decide +kernel
    simp only [heap,Bool.false_eq_true,if_false,heapCut,Bool.false_eq_true,if_false]
    rw [hl,List.foldlM_append,fold_inner false index coord pads _ (by intro h hh;have := List.mem_range'.mp (List.mem_reverse.mp hh);omega)]
    unfold OuterHeapMoment.heap OuterInnerMoment.innerHeap
    congr 1
    funext nodes
    simp only [List.foldlM_cons,List.foldlM_nil,step,OuterCanonicalNode.node,true_and,
      show (3:Nat)<4 by decide,show (2:Nat)<4 by decide,if_true,map_eq_bind_pure_comp,Function.comp_apply,bind_assoc,pure_bind,bind_pure]
    unfold OuterHeapMoment.finish
    congr 1
    funext a
    rw [getD_set_other nodes 3 4 a.2 (by decide),getD_set_other nodes 3 5 a.2 (by decide)]

#print axioms heap_fold
end OuterCanonicalModel
