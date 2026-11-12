import SigGolfCandidate.OuterFixedForest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterFixedForestReplay
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open OuterFixedForest

theorem eval_forest (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) :
    let r:=evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index selected words opened)
    evalWithAnswerFn answers (forest index selected words opened r.2.1 r.2.2.1 r.2.2.2)=r.1 := by
  unfold forest OuterForestCorrectness.recoverForest
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,show List.finRange 4=[0,1,2,3] from rfl,
    List.foldlM_cons,List.foldlM_nil]
  rw [eval_pair answers index (((0 : Fin 4)) : Nat) _ _ _ _ _ _ _ _
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])]
  rw [eval_pair answers index (((1 : Fin 4)) : Nat) _ _ _ _ _ _ _ _
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])]
  rw [eval_pair answers index (((2 : Fin 4)) : Nat) _ _ _ _ _ _ _ _
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])]
  rw [eval_pair answers index (((3 : Fin 4)) : Nat) _ _ _ _ _ _ _ _
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])
    (by simp [List.getD_eq_getElem?_getD,List.getElem?_append])]
  have hlast : ∀ (a b c d : List Nat) (e n : Nat),a.length=n→b.length=n→c.length=n→d.length=n→
      ([]++a++b++c++d++[e]).getD (4*n) 0=e := by
    intro a b c d e n ha hb hc hd
    simp [List.getD_eq_getElem?_getD,List.getElem?_append,ha,hb,hc,hd,
      show ¬4*n<n from by omega,show ¬3*n<n from by omega,show ¬2*n<n from by omega,
      show 4*n-n=3*n from by omega,show 3*n-n=2*n from by omega,show 2*n-n=n from by omega]
  rw [hlast _ _ _ _ _ 2 (by simp) (by simp) (by simp) (by simp),
    hlast _ _ _ _ _ 2 (by simp) (by simp) (by simp) (by simp),
    hlast _ _ _ _ _ 1 (by simp) (by simp) (by simp) (by simp)]
  unfold OuterFixedForest.singleton OuterForestCorrectness.recoverSingleton
  exact OuterFixedRecover.eval_recover answers index 8 _ _ _ _ _
#print axioms eval_forest
end OuterFixedForestReplay
