import SigGolfCandidate.OuterRecover
import SigGolfCandidate.OuterForestMoment
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterPairModel
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
def firstNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest :=
  sharedNodes answers true index (2 * pair) (fun _ => prev)

def secondNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest :=
  OuterCoordinateCorrectness.nodes answers index (2 * pair + 1) (nodesPair (firstNodes answers index pair prev))

def expectedPairOpening (answers : Answers) (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) : PairOpening where
  firstValues := fun i => (List.ofFn (fun j : Fin 6 =>
    chainValue answers index (2 * pair) (rawChild true (firstChild s).val) aWord j)).getD i.val 0
  firstPath := fun i => authAt (firstNodes answers index pair prev) (firstChild s).val i.val
  secondValues := fun i => (List.ofFn (fun j : Fin 6 =>
    chainValue answers index (2 * pair + 1) (rawChild false (secondChild s).val) bWord j)).getD i.val 0
  secondPath := fun i => authAt (secondNodes answers index pair prev) (secondChild s).val i.val

def expectedPairRoot (answers : Answers) (index pair : Nat) (prev : PairRoot) : PairRoot :=
  ((secondNodes answers index pair prev).getD 2 0, (secondNodes answers index pair prev).getD 3 0)


def recover (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : M (PairRoot × List Nat × List Nat × List Nat) := do
  let aChild:=firstChild s
  let bChild:=secondChild s
  let a←recoverSharedInner true index (2*pair) aChild aWord opened.firstValues
    (fun i => opened.firstPath ⟨i%6,Nat.mod_lt _ (by decide)⟩) prev
  let aPair:=if aChild.val/32%2=0 then (a.1,opened.firstPath 5) else (opened.firstPath 5,a.1)
  let b←OuterRecover.recover index (2*pair+1) bChild bWord opened.secondValues
    (fun i => opened.secondPath ⟨i%7,Nat.mod_lt _ (by decide)⟩) aPair
  pure (b.1,[a.2.1,b.2.1],[a.2.2,b.2.2.1],[b.2.2.2])

attribute [local irreducible] sharedNodes OuterCoordinateCorrectness.nodes

theorem build_result (answers : Answers) (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    evalWithAnswerFn answers (OuterForestMoment.pair index pair s aWord bWord prev)=
      (expectedPairOpening answers index pair s aWord bWord prev,expectedPairRoot answers index pair prev) := by
  simp only [OuterForestMoment.pair,OuterForestBudget.buildCoord,Bool.false_eq_true,↓reduceIte,OuterForestBudget.buildA_eq,
    evalWithAnswerFn_bind,buildSharedCoordinate_result,OuterCoordinateCorrectness.build_result,evalWithAnswerFn_pure]
  rfl

theorem recover_expected (answers : Answers) (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    (evalWithAnswerFn answers (recover index pair s aWord bWord
      (expectedPairOpening answers index pair s aWord bWord prev) prev)).1 =
      expectedPairRoot answers index pair prev := by
  let a := firstNodes answers index pair prev
  let b := secondNodes answers index pair prev
  let opened := expectedPairOpening answers index pair s aWord bWord prev
  have ha := recoverSharedInner_honest answers true index (2 * pair) (firstChild s) aWord
    (fun _ => prev) opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩)
    (by
      intro i
      change (List.ofFn _).getD i.val 0 = _
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn])
    (by
      intro level hl
      dsimp only [opened, expectedPairOpening, firstNodes]
      rw [Nat.mod_eq_of_lt (by omega)]
      )
  unfold recover
  rw [evalWithAnswerFn_bind, ha, evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_pure]
  change (evalWithAnswerFn answers
    (OuterRecover.recover index (2 * pair + 1) (secondChild s) bWord opened.secondValues
      (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩)
      (if (firstChild s).val / 32 % 2 = 0 then
        (a.getD ((128 + (firstChild s).val) / 32) 0, authAt a (firstChild s).val 5)
      else (authAt a (firstChild s).val 5, a.getD ((128 + (firstChild s).val) / 32) 0)))).1 = _
  rw [ordered_branch_pair a (firstChild s).val (firstChild s).isLt, selected_branch s]
  apply OuterRecover.honest answers index (2 * pair + 1) (secondChild s) bWord (nodesPair a)
  · intro i
    change (List.ofFn _).getD i.val 0 = _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  · intro level hl
    dsimp only [opened, expectedPairOpening, secondNodes, firstNodes]
    rw [Nat.mod_eq_of_lt hl]
    rfl

#print axioms build_result
#print axioms recover_expected
end OuterPairModel
