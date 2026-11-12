import SigGolfCandidate.OuterSourceCoordinate
import SigGolfCandidate.OuterForestCorrectness
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSourceForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest

def pair (index : Nat) (p : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aw bw : Rank)
    (opened : PairOpening) (prev : PairRoot) : M (PairRoot×List Nat×List Nat×List Nat) := do
  let a←OuterSourceCoordinate.source index ⟨2*p.val,by omega⟩ (rawOfPhysical true (firstChild s)) aw opened.firstValues
    (fun i=>opened.firstPath ⟨i%6,Nat.mod_lt _ (by decide)⟩) prev
  let b←OuterSourceCoordinate.source index ⟨2*p.val+1,by omega⟩ (rawOfPhysical false (secondChild s)) bw opened.secondValues
    (fun i=>opened.secondPath ⟨i%7,Nat.mod_lt _ (by decide)⟩) a.1
  pure (b.1,[a.2.1,b.2.1],[a.2.2.1,b.2.2.1],[b.2.2.2])

theorem pair_eq (index : Nat) (p : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aw bw : Rank)
    (opened : PairOpening) (prev : PairRoot) :
    pair index p s aw bw opened prev=OuterPairModel.recover index p.val s aw bw opened prev := by
  have hfirst : SharedV3.first (2*p.val)=true := by simp [SharedV3.first];omega
  have hsecond : SharedV3.first (2*p.val+1)=false := by simp [SharedV3.first]
  have ha : SharedV3.physical (2*p.val) (rawOfPhysical true (firstChild s)).val=(firstChild s).val := by
    simp only [SharedV3.physical,hfirst,physical_rawOfPhysical]
  have hb : SharedV3.physical (2*p.val+1) (rawOfPhysical false (secondChild s)).val=(secondChild s).val := by
    simp only [SharedV3.physical,hsecond,physical_rawOfPhysical]
  unfold pair OuterSourceCoordinate.source OuterCanonicalCoordinate.recover sourceCoordinate OuterPairModel.recover OuterRecover.recover
  simp only [ha,hb,hfirst,hsecond,Bool.false_eq_true,↓reduceIte,bind_assoc,bind_map_left,map_bind,map_pure,pure_bind,
    SharedV3.orderPair,SharedV3.direction,SharedV3.lastLevel]
  rfl

def singleton (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening) (prev : PairRoot) :
    M (PairRoot×Nat×Nat×Nat) :=
  OuterSourceCoordinate.source index 8 (rawOfPhysical false selected) word opened.values
    (fun i=>opened.path ⟨i%7,Nat.mod_lt _ (by decide)⟩) prev

theorem singleton_eq (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening) (prev : PairRoot) :
    singleton index selected word opened prev=OuterForestCorrectness.recoverSingleton index selected word opened prev := by
  have hf : SharedV3.first 8=false := by decide
  have hp : SharedV3.physical 8 (rawOfPhysical false selected).val=selected.val := by
    simp only [SharedV3.physical,hf,physical_rawOfPhysical]
  unfold singleton OuterSourceCoordinate.source OuterCanonicalCoordinate.recover OuterForestCorrectness.recoverSingleton
  simp only [show (8:Fin 9).val=8 from rfl,hf,Bool.false_eq_true,if_false,hp]

def grouped (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    M (PairRoot×List Nat×List Nat×List Nat) := do
  let prev←(List.finRange 4).foldlM (fun (acc : PairRoot×List Nat×List Nat×List Nat) p=>do
    let r←pair index p (selected.pairs p) (words.first p) (words.second p) (opened.pairs p) acc.1
    pure (r.1,acc.2.1++r.2.1,acc.2.2.1++r.2.2.1,acc.2.2.2++r.2.2.2)) (ftsStart,[],[],[])
  let last←singleton index selected.singleton words.singleton opened.singleton prev.1
  pure (last.1,prev.2.1++[last.2.1],prev.2.2.1++[last.2.2.1],prev.2.2.2++[last.2.2.2])

theorem grouped_eq (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    grouped index selected words opened=OuterForestCorrectness.recoverForest index selected words opened := by
  unfold grouped OuterForestCorrectness.recoverForest
  simp only [pair_eq,singleton_eq]

def nine (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    M (PairRoot×List Nat×List Nat×List Nat) :=
  (List.finRange 9).foldlM (fun (acc : PairRoot×List Nat×List Nat×List Nat) coord=>do
    let r←OuterSourceCoordinate.source index coord (coordinateRaw selected coord) (coordinateWord words coord)
      (coordinateValues opened coord) (coordinatePath opened coord) acc.1
    pure (r.1,acc.2.1++[r.2.1],acc.2.2.1++[r.2.2.1],
      if SharedV3.first coord.val then acc.2.2.2 else acc.2.2.2++[r.2.2.2])) (ftsStart,[],[],[])

theorem nine_eq_grouped (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    nine index selected words opened=grouped index selected words opened := by
  have hnine : List.finRange 9=[0,1,2,3,4,5,6,7,8] := by decide
  have hfour : List.finRange 4=[0,1,2,3] := by decide
  simp only [nine,grouped,hnine,hfour,List.foldlM_cons,List.foldlM_nil,pair,singleton,bind_assoc,pure_bind,
    List.nil_append,List.append_assoc,List.cons_append,List.singleton_append]
  simp only [coordinateRaw,coordinateChild,coordinateWord,coordinateValues,coordinatePath]
  norm_num [SharedV3.first]
  rfl

#print axioms pair_eq
#print axioms singleton_eq
#print axioms grouped_eq
#print axioms nine_eq_grouped
end OuterSourceForest
