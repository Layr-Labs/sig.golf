import SigGolfCandidate.OuterForestCorrectness
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterRecoverBudget
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest OuterGroundCore

theorem hashN_bound (coord index heap n : Nat) (left right : Digest) :
    CBound (fun _=>True) 1 (hashN coord index heap n left right) := by
  unfold hashN
  apply Bound.qry_bind (k:=0)
  · simp only [GoodQuery,trial_length];norm_num
  · intro a;exact Bound.pure _ 0 trivial
  · simp only [weight,trial_length];norm_num

theorem search_bound (coord index heap : Nat) (left right : Digest) : ∀ fuel n,
    CBound (fun _=>True) (fuel+1) (search coord index heap left right fuel n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n
    exact (hashN_bound coord index heap n left right).bind' (l:=0) (fun a _=>Bound.pure _ 0 trivial) (by omega)
  | succ fuel ih =>
    intro n
    unfold search
    refine (hashN_bound coord index heap n left right).bind' (l:=fuel+1) (fun a _=>?_) (by omega)
    split
    · exact Bound.pure _ (fuel+1) trivial
    · exact ih (n+1)

theorem node_bound (coord index heap : Nat) (left right : Digest) :
    CBound (fun _=>True) (cap coord) (nodeAt coord index heap left right) := by
  have hp : 0<cap coord := by unfold cap;positivity
  exact (search_bound coord index heap left right (cap coord-1) 0).mono_k (by omega)

theorem recover_bound (index coord : Nat) (hc : coord<9) (selected : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (prev : PairRoot) :
    CBound (fun _=>True) (29+ftsCapOf coord+ftsC16 coord+cap coord)
      (OuterRecover.recover index coord selected word values path prev) := by
  unfold OuterRecover.recover
  refine (bound_recoverSharedInner false index coord hc selected word values path prev).bind' (l:=cap coord)
    (fun inner _=>?_) (by omega)
  exact (node_bound coord index (2+selected.val/64) _ _).bind' (l:=0)
    (fun outer _=>Bound.pure _ 0 trivial) (by omega)

theorem pair_bound (index pair : Nat) (hp : pair<4) (selected : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) :
    CBound (fun _=>True) (58+ftsCapOf (2*pair)+ftsC16 (2*pair)+ftsCapOf (2*pair+1)+ftsC16 (2*pair+1)+cap (2*pair+1))
      (OuterPairModel.recover index pair selected aWord bWord opened prev) := by
  unfold OuterPairModel.recover
  refine (bound_recoverSharedInner true index (2*pair) (by omega) (firstChild selected) aWord opened.firstValues
    (fun i=>opened.firstPath ⟨i%6,Nat.mod_lt _ (by decide)⟩) prev).bind'
      (l:=29+ftsCapOf (2*pair+1)+ftsC16 (2*pair+1)+cap (2*pair+1)) (fun a _=>?_) (by omega)
  exact (recover_bound index (2*pair+1) (by omega) (secondChild selected) bWord opened.secondValues
    (fun i=>opened.secondPath ⟨i%7,Nat.mod_lt _ (by decide)⟩) _).bind' (l:=0)
      (fun b _=>Bound.pure _ 0 trivial) (by omega)

def pairCost (p : Nat) : Nat :=
  58+ftsCapOf (2*p)+ftsC16 (2*p)+ftsCapOf (2*p+1)+ftsC16 (2*p+1)+cap (2*p+1)
def singletonCost : Nat := 29+ftsCapOf 8+ftsC16 8+cap 8

theorem singleton_bound (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening) (prev : PairRoot) :
    CBound (fun _=>True) singletonCost (OuterForestCorrectness.recoverSingleton index selected word opened prev) := by
  exact recover_bound index 8 (by decide) selected word opened.values
    (fun i=>opened.path ⟨i%7,Nat.mod_lt _ (by decide)⟩) prev

theorem forest_bound (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    CBound (fun _=>True) 25866 (OuterForestCorrectness.recoverForest index selected words opened) := by
  unfold OuterForestCorrectness.recoverForest
  refine (Bound.foldlM_list (P:=GoodQuery) (List.finRange 4) _ (fun _ _=>True)
    pairCost (ftsStart,[],[],[]) trivial (fun i hi acc _=>?_)).bind' (l:=singletonCost) (fun prev _=>?_) ?_
  · have hival : ((List.finRange 4)[i]).val=i := by simp
    have hb:=pair_bound index ((List.finRange 4)[i]).val ((List.finRange 4)[i]).isLt
      (selected.pairs ((List.finRange 4)[i])) (words.first ((List.finRange 4)[i]))
      (words.second ((List.finRange 4)[i])) (opened.pairs ((List.finRange 4)[i])) acc.1
    exact hb.bind' (l:=0) (fun r _=>Bound.pure _ 0 trivial) (by simp only [hival,pairCost,Nat.add_zero];exact le_rfl)
  · exact (singleton_bound index selected.singleton words.singleton opened.singleton prev.1).bind' (l:=0)
      (fun last _=>Bound.pure _ 0 trivial) (by omega)
  · decide +kernel

theorem forest_cost (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : SigGolfCandidate.T3.SearchCost.cost answers
      (OuterForestCorrectness.recoverForest index selected words opened)≤25866 :=
  SigGolfCandidate.T3.SearchCost.cost_bound answers (forest_bound index selected words opened)

theorem extra : 25866=SigGolfCandidate.Research.SharedForest.ftsRecoverWorst+20475 := by decide +kernel

#print axioms forest_bound
#print axioms forest_cost

#print axioms hashN_bound
#print axioms search_bound
#print axioms node_bound
#print axioms recover_bound
#print axioms pair_bound
end OuterRecoverBudget
