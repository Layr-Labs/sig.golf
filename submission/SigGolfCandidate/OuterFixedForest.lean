import SigGolfCandidate.OuterFixedRecover
import SigGolfCandidate.OuterForestCorrectness
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterFixedForest
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest

def pair (index p : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (ns3 ns2 ns5 : List Nat) (prev : PairRoot) : M PairRoot := do
  let aChild:=firstChild s
  let a←recoverSharedInnerN true index (2*p) aChild aWord opened.firstValues
    (fun i=>opened.firstPath ⟨i%6,Nat.mod_lt _ (by decide)⟩) (ns3.getD (2*p) 0) (ns2.getD (2*p) 0) prev
  let aPair:=if aChild.val/32%2=0 then (a,opened.firstPath 5) else (opened.firstPath 5,a)
  OuterFixedRecover.recover index (2*p+1) (secondChild s) bWord opened.secondValues
    (fun i=>opened.secondPath ⟨i%7,Nat.mod_lt _ (by decide)⟩)
    (ns3.getD (2*p+1) 0) (ns2.getD (2*p+1) 0) (ns5.getD p 0) aPair

def singleton (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening)
    (n3 n2 n5 : Nat) (prev : PairRoot) : M PairRoot:=
  OuterFixedRecover.recover index 8 selected word opened.values
    (fun i=>opened.path ⟨i%7,Nat.mod_lt _ (by decide)⟩) n3 n2 n5 prev

def forest (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening)
    (ns3 ns2 ns5 : List Nat) : M PairRoot := do
  let prev←(List.finRange 4).foldlM (fun acc p=>pair index p.val (selected.pairs p)
    (words.first p) (words.second p) (opened.pairs p) ns3 ns2 ns5 acc) ftsStart
  singleton index selected.singleton words.singleton opened.singleton (ns3.getD 8 0) (ns2.getD 8 0) (ns5.getD 4 0) prev

theorem eval_pair (answers : Answers) (index p : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (ns3 ns2 ns5 : List Nat) (prev : PairRoot)
    (h1 : ns3.getD (2*p) 0=(evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.1.getD 0 0)
    (h2 : ns3.getD (2*p+1) 0=(evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.1.getD 1 0)
    (h3 : ns2.getD (2*p) 0=(evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.2.1.getD 0 0)
    (h4 : ns2.getD (2*p+1) 0=(evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.2.1.getD 1 0)
    (h5 : ns5.getD p 0=(evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.2.2.getD 0 0) :
    evalWithAnswerFn answers (pair index p s aWord bWord opened ns3 ns2 ns5 prev)=
      (evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).1 := by
  unfold OuterPairModel.recover at h1 h2 h3 h4 h5 ⊢
  unfold pair
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at h1 h2 h3 h4 h5 ⊢
  rw [h1,h3,eval_recoverSharedInnerN,h2,h4,h5,OuterFixedRecover.eval_recover]

@[simp] theorem length3 (answers : Answers) (index p : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    (evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.1.length=2 := by
  unfold OuterPairModel.recover
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,List.length_cons,List.length_nil]
@[simp] theorem length2 (answers : Answers) (index p : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    (evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.2.1.length=2 := by
  unfold OuterPairModel.recover
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,List.length_cons,List.length_nil]
@[simp] theorem length5 (answers : Answers) (index p : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    (evalWithAnswerFn answers (OuterPairModel.recover index p s aWord bWord opened prev)).2.2.2.length=1 := by
  unfold OuterPairModel.recover
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,List.length_cons,List.length_nil]

#print axioms eval_pair
end OuterFixedForest
