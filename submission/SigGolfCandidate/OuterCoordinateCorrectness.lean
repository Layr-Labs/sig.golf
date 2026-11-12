import SigGolfCandidate.OuterCoordinate
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterCoordinateCorrectness
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
abbrev A := SigGolfCandidate.T3.Correctness.Answers

theorem prelude_result (answers : A) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat → PairRoot) :
    evalWithAnswerFn answers (OuterCoordinate.prelude first index coord selected word pads)=
      (sharedLeaves answers first index coord pads,
        List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild first selected.val) word i)) := by
  let rows:=evalWithAnswerFn answers (sharedRows first index coord selected word (List.ofFn (ftsCoef answers index coord)) pads)
  have hr : SharedRows answers first index coord selected word pads 128 rows := eval_sharedRows answers first index coord selected word pads
  rcases hr with ⟨hlen,hroot,hvalues⟩
  have hroots : rows.1=sharedLeaves answers first index coord pads := by
    apply List.ext_getElem (by simpa only [sharedLeaves,List.length_ofFn] using hlen)
    intro j hj hk
    simpa only [sharedLeaves,List.getD_eq_getElem _ _ hj,List.getElem_ofFn] using hroot j (by omega)
  rw [if_pos selected.isLt] at hvalues
  unfold OuterCoordinate.prelude
  rw [evalWithAnswerFn_bind,eval_ftsCoefs]
  change rows=_
  exact Prod.ext hroots hvalues

theorem sharedHeap_split (index coord : Nat) (pads : Nat → PairRoot) (leaves : List Digest) :
    sharedHeap false index coord pads leaves=(do
      let nodes←OuterInnerMoment.innerHeap false index coord pads leaves
      let nodes←heapStep false index coord pads nodes 3
      heapStep false index coord pads nodes 2) := by
  have hl : (List.range' 2 126).reverse=(List.range' 4 124).reverse++[3,2] := by decide +kernel
  unfold sharedHeap OuterInnerMoment.innerHeap
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [hl,List.foldlM_append]
  simp only [List.foldlM_cons,List.foldlM_nil,bind_pure]
  rfl

def innerNodes (answers : A) (index coord : Nat) (pads : Nat → PairRoot) : Array Digest :=
  evalWithAnswerFn answers (OuterInnerMoment.innerHeap false index coord pads (sharedLeaves answers false index coord pads))
def nodes (answers : A) (index coord : Nat) (pads : Nat → PairRoot) : Array Digest :=
  evalWithAnswerFn answers (OuterHeapMoment.heap coord index pads (sharedLeaves answers false index coord pads))

theorem eval_step (answers : A) (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) (a : Array Digest) (h : Nat) :
    evalWithAnswerFn answers (heapStep first index coord pads a h)=
      a.set! h (evalWithAnswerFn answers (sharedNode first coord index h pads (a.getD (2*h) 0) (a.getD (2*h+1) 0))) := by
  rw [heapStep,evalWithAnswerFn_bind]
  rfl

theorem inner_agrees (answers : A) (index coord : Nat) (pads : Nat → PairRoot) (j : Nat) (hj : 4≤j) :
    (innerNodes answers index coord pads).getD j 0=(sharedNodes answers false index coord pads).getD j 0 := by
  unfold sharedNodes
  rw [sharedHeap_split,evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_bind,eval_step]
  rw [getD_set_other _ 2 j _ (by omega),getD_set_other _ 3 j _ (by omega)]
  rfl

theorem nodes_agree (answers : A) (index coord : Nat) (pads : Nat → PairRoot) (j : Nat) (hj : 4≤j) :
    (nodes answers index coord pads).getD j 0=(sharedNodes answers false index coord pads).getD j 0 := by
  unfold nodes OuterHeapMoment.heap
  rw [evalWithAnswerFn_bind]
  unfold OuterHeapMoment.finish
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  rw [getD_set_other _ 2 j _ (by omega),getD_set_other _ 3 j _ (by omega)]
  exact inner_agrees answers index coord pads j hj

theorem build_result (answers : A) (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    evalWithAnswerFn answers (OuterCoordinate.build index coord selected word pads)=
      (nodes answers index coord pads,List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild false selected.val) word i)) := by
  unfold OuterCoordinate.build
  rw [evalWithAnswerFn_bind,prelude_result]
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  rfl

theorem inner_size (answers : A) (index coord : Nat) (pads : Nat → PairRoot) :
    (innerNodes answers index coord pads).size=256 := by
  have h:=(sharedNodes_graph answers false index coord pads).1
  unfold sharedNodes at h
  rw [sharedHeap_split,evalWithAnswerFn_bind] at h
  simpa only [innerNodes,evalWithAnswerFn_bind,eval_step,Array.size_set!] using h

theorem nodes_size (answers : A) (index coord : Nat) (pads : Nat → PairRoot) :
    (nodes answers index coord pads).size=256 := by
  unfold nodes OuterHeapMoment.heap
  rw [evalWithAnswerFn_bind]
  unfold OuterHeapMoment.finish
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,Array.size_set!]
  exact inner_size answers index coord pads

theorem auth_index_ge4 (selected level : Nat) (hs : selected<128) (hl : level<5) :
    4≤((128+selected)/2^level ^^^ 1) := by
  have hq : 8≤(128+selected)/2^level := by interval_cases level <;> norm_num <;> omega
  rcases Nat.even_or_odd ((128+selected)/2^level) with he | ho
  · rw [Nat.xor_one_of_even he];omega
  · rw [Nat.xor_one_of_odd ho];omega

theorem recover_inner (answers : A) (index coord : Nat) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) (values : Fin 6 → Digest) (path : Nat → Digest)
    (hv : ∀ i,values i=chainValue answers index coord (rawChild false selected.val) word i)
    (hp : ∀ level,level<5→path level=authAt (nodes answers index coord pads) selected.val level) :
    (evalWithAnswerFn answers (recoverSharedInner false index coord selected word values path (pads (selected.val/64)))).1=
      (nodes answers index coord pads).getD ((128+selected.val)/32) 0 := by
  have hh:=recoverSharedInner_honest answers false index coord selected word pads values path hv (fun level hl => ?_)
  · exact hh.trans (nodes_agree answers index coord pads _ (by have := selected.isLt;omega)).symm
  · rw [hp level hl]
    unfold authAt
    exact nodes_agree answers index coord pads _ (auth_index_ge4 selected.val level selected.isLt hl)

theorem outer_path_zero (answers : A) (index coord : Nat) (selected : Child) (pads : Nat → PairRoot)
    (h2 : OuterGroundCore.zeroOk coord ((nodes answers index coord pads).getD 2 0)=true)
    (h3 : OuterGroundCore.zeroOk coord ((nodes answers index coord pads).getD 3 0)=true) :
    OuterGroundCore.zeroOk coord (authAt (nodes answers index coord pads) selected.val 6)=true := by
  unfold authAt
  by_cases h : selected.val<64
  · have hq : (128+selected.val)/2^6=2 := by norm_num;omega
    rw [hq];exact h3
  · have hq : (128+selected.val)/2^6=3 := by have := selected.isLt;norm_num;omega
    rw [hq];exact h2

theorem nodes_inner_agree (answers : A) (index coord : Nat) (pads : Nat → PairRoot) (j : Nat) (hj : 4≤j) :
    (nodes answers index coord pads).getD j 0=(innerNodes answers index coord pads).getD j 0 :=
  (nodes_agree answers index coord pads j hj).trans (inner_agrees answers index coord pads j hj).symm

theorem nodes_eq (answers : A) (index coord : Nat) (pads : Nat → PairRoot) :
    nodes answers index coord pads=
      ((innerNodes answers index coord pads).set! 3
        (evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index 3
          ((innerNodes answers index coord pads).getD 6 0) ((innerNodes answers index coord pads).getD 7 0))).2).set! 2
        (evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index 2
          ((innerNodes answers index coord pads).getD 4 0) ((innerNodes answers index coord pads).getD 5 0))).2 := by
  unfold nodes OuterHeapMoment.heap OuterHeapMoment.finish
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  rfl

theorem top2 (answers : A) (index coord : Nat) (pads : Nat → PairRoot) :
    (nodes answers index coord pads).getD 2 0=
      (evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index 2
        ((nodes answers index coord pads).getD 4 0) ((nodes answers index coord pads).getD 5 0))).2 := by
  rw [nodes_inner_agree answers index coord pads 4 (by decide),nodes_inner_agree answers index coord pads 5 (by decide),nodes_eq]
  apply getD_set_self
  simp only [Array.size_set!,inner_size]
  decide

theorem top3 (answers : A) (index coord : Nat) (pads : Nat → PairRoot) :
    (nodes answers index coord pads).getD 3 0=
      (evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index 3
        ((nodes answers index coord pads).getD 6 0) ((nodes answers index coord pads).getD 7 0))).2 := by
  rw [nodes_inner_agree answers index coord pads 6 (by decide),nodes_inner_agree answers index coord pads 7 (by decide),nodes_eq]
  rw [getD_set_other _ 2 3 _ (by decide)]
  apply getD_set_self
  rw [inner_size]
  decide

#print axioms top2
#print axioms top3
#print axioms inner_size
#print axioms recover_inner
#print axioms outer_path_zero
#print axioms prelude_result
#print axioms inner_agrees
#print axioms nodes_agree
#print axioms build_result
end OuterCoordinateCorrectness
