import SigGolfCandidate.OuterVerifierCoordinate
import SigGolfCandidate.OuterFixedForest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifierForestSource
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical SigGolfCandidate.Research.SharedForest

def pair (index : Nat) (p : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (ns3 ns2 ns5 : List Nat) (prev : PairRoot) : M PairRoot := do
  let a←OuterVerifierCoordinate.source index ⟨2*p.val,by omega⟩ (rawOfPhysical true (firstChild s)) aWord
    opened.firstValues (fun i=>opened.firstPath ⟨i%6,Nat.mod_lt _ (by decide)⟩)
    (ns3.getD (2*p.val) 0) (ns2.getD (2*p.val) 0) (ns5.getD p.val 0) prev
  OuterVerifierCoordinate.source index ⟨2*p.val+1,by omega⟩ (rawOfPhysical false (secondChild s)) bWord
    opened.secondValues (fun i=>opened.secondPath ⟨i%7,Nat.mod_lt _ (by decide)⟩)
    (ns3.getD (2*p.val+1) 0) (ns2.getD (2*p.val+1) 0) (ns5.getD p.val 0) a

theorem pair_eq (index : Nat) (p : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (ns3 ns2 ns5 : List Nat) (prev : PairRoot) :
    pair index p s aWord bWord opened ns3 ns2 ns5 prev=OuterFixedForest.pair index p.val s aWord bWord opened ns3 ns2 ns5 prev := by
  have hf : SharedV3.first (2*p.val)=true:=by simp [SharedV3.first];omega
  have hs : SharedV3.first (2*p.val+1)=false:=by simp [SharedV3.first]
  have ha : SharedV3.physical (2*p.val) (rawOfPhysical true (firstChild s)).val=(firstChild s).val:=by
    simp only [SharedV3.physical,hf,physical_rawOfPhysical]
  have hb : SharedV3.physical (2*p.val+1) (rawOfPhysical false (secondChild s)).val=(secondChild s).val:=by
    simp only [SharedV3.physical,hs,physical_rawOfPhysical]
  unfold pair OuterVerifierCoordinate.source OuterFixedForest.pair OuterFixedRecover.recover
  simp only [ha,hb,hf,hs,Bool.false_eq_true,if_true,if_false,bind_assoc,pure_bind,
    SharedV3.orderPair,SharedV3.direction,SharedV3.lastLevel]
  rfl

def singleton (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening)
    (n3 n2 n5 : Nat) (prev : PairRoot) : M PairRoot:=
  OuterVerifierCoordinate.source index 8 (rawOfPhysical false selected) word opened.values
    (fun i=>opened.path ⟨i%7,Nat.mod_lt _ (by decide)⟩) n3 n2 n5 prev

theorem singleton_eq (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening)
    (n3 n2 n5 : Nat) (prev : PairRoot) :
    singleton index selected word opened n3 n2 n5 prev=OuterFixedForest.singleton index selected word opened n3 n2 n5 prev := by
  have hf : SharedV3.first 8=false:=by decide
  have hp : SharedV3.physical 8 (rawOfPhysical false selected).val=selected.val:=by
    simp only [SharedV3.physical,hf,physical_rawOfPhysical]
  unfold singleton OuterVerifierCoordinate.source OuterFixedForest.singleton OuterFixedRecover.recover
  simp only [show (8 : Fin 9).val=8 from rfl,hp,hf,Bool.false_eq_true,if_false,
    SharedV3.orderPair,SharedV3.direction,SharedV3.lastLevel]
  rfl

def nine (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening)
    (ns3 ns2 ns5 : List Nat) : M PairRoot:=
  (List.finRange 9).foldlM (fun acc coord=>OuterVerifierCoordinate.source index coord (coordinateRaw selected coord)
    (coordinateWord words coord) (coordinateValues opened coord) (coordinatePath opened coord)
    (ns3.getD coord.val 0) (ns2.getD coord.val 0) (ns5.getD (coord.val/2) 0) acc) ftsStart

attribute [local irreducible] OuterVerifierCoordinate.source rawOfPhysical

theorem nine_eq (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening)
    (ns3 ns2 ns5 : List Nat) :
    nine index selected words opened ns3 ns2 ns5=OuterFixedForest.forest index selected words opened ns3 ns2 ns5 := by
  have hnine : List.finRange 9=[0,1,2,3,4,5,6,7,8]:=by decide
  have hfour : List.finRange 4=[0,1,2,3]:=by decide
  simp only [nine,OuterFixedForest.forest,hnine,hfour,List.foldlM_cons,List.foldlM_nil,bind_assoc,pure_bind,bind_pure]
  simp only [←pair_eq,←singleton_eq]
  simp only [pair,singleton,bind_assoc,pure_bind,bind_pure]
  simp only [coordinateRaw,coordinateChild,coordinateWord,coordinateValues,coordinatePath]
  norm_num [SharedV3.first]
  rfl
#print axioms pair_eq
#print axioms singleton_eq
#print axioms nine_eq
end OuterVerifierForestSource
