import SigGolfCandidate.OuterPairModel
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterForestCorrectness
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
attribute [local irreducible] sharedNodes OuterCoordinateCorrectness.nodes

def recoverSingleton (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening) (prev : PairRoot) :
    M (PairRoot × Nat × Nat × Nat) :=
  OuterRecover.recover index 8 selected word opened.values (fun i => opened.path ⟨i%7,Nat.mod_lt _ (by decide)⟩) prev

theorem singleton_honest (answers : Answers) (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    let built:=evalWithAnswerFn answers (OuterForestMoment.singleton index selected word prev)
    (evalWithAnswerFn answers (recoverSingleton index selected word built.1 prev)).1=built.2 := by
  unfold OuterForestMoment.singleton
  simp only [OuterForestBudget.buildCoord,Bool.false_eq_true,↓reduceIte,evalWithAnswerFn_bind,
    OuterCoordinateCorrectness.build_result,evalWithAnswerFn_pure]
  unfold recoverSingleton
  apply OuterRecover.honest answers index 8 selected word (fun _ => prev)
  · intro i
    change (List.ofFn _).getD i.val 0=_
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn];exact i.isLt),List.getElem_ofFn]
  · intro level hl
    simp only [Nat.mod_eq_of_lt hl]

def recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    M (PairRoot × List Nat × List Nat × List Nat) := do
  let prev←(List.finRange 4).foldlM (fun (acc : PairRoot × List Nat × List Nat × List Nat) p => do
    let r←OuterPairModel.recover index p.val (selected.pairs p) (words.first p) (words.second p) (opened.pairs p) acc.1
    pure (r.1,acc.2.1++r.2.1,acc.2.2.1++r.2.2.1,acc.2.2.2++r.2.2.2)) (ftsStart,[],[],[])
  let last←recoverSingleton index selected.singleton words.singleton opened.singleton prev.1
  pure (last.1,prev.2.1++[last.2.1],prev.2.2.1++[last.2.2.1],prev.2.2.2++[last.2.2.2])

theorem forest_honest (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    let built:=evalWithAnswerFn answers (OuterForestMoment.forest index selected words)
    (evalWithAnswerFn answers (recoverForest index selected words built.1)).1=built.2 := by
  have hfour : List.finRange 4=[0,1,2,3] := by decide
  have hv0 : (0 : Fin 4).val=0 := rfl
  have hv1 : (1 : Fin 4).val=1 := rfl
  have hv2 : (2 : Fin 4).val=2 := rfl
  have hv3 : (3 : Fin 4).val=3 := rfl
  let r0:=OuterPairModel.expectedPairRoot answers index 0 ftsStart
  let r1:=OuterPairModel.expectedPairRoot answers index 1 r0
  let r2:=OuterPairModel.expectedPairRoot answers index 2 r1
  let r3:=OuterPairModel.expectedPairRoot answers index 3 r2
  simp only [OuterForestMoment.forest,hfour,List.foldlM_cons,List.foldlM_nil,evalWithAnswerFn_bind,
    evalWithAnswerFn_pure,OuterPairModel.build_result]
  simp only [recoverForest,hfour,List.foldlM_cons,List.foldlM_nil,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  simp only [hv0,hv1,hv2,hv3,List.nil_append,List.append_assoc,List.cons_append,List.getD_cons_zero,
    List.getD_cons_succ,OuterPairModel.recover_expected]
  exact singleton_honest answers index selected.singleton words.singleton r3

#print axioms singleton_honest
#print axioms forest_honest
end OuterForestCorrectness
