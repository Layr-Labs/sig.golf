import SigGolfCandidate.OuterSourceForest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterForestModel
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest

def forest (w : SharedV3.WBytes) (index : Nat) (raw : Fin 9 → Child) (words : Fin 9 → Rank) :
    M (PairRoot×List Nat×List Nat×List Nat) :=
  (List.finRange 9).foldlM (fun (acc : PairRoot×List Nat×List Nat×List Nat) coord=>do
    let r←OuterCoordinateModel.coordinate w index coord (raw coord) (words coord) acc.1
    pure (r.1,acc.2.1++[r.2.1],acc.2.2.1++[r.2.2.1],
      if SharedV3.first coord.val then acc.2.2.2 else acc.2.2.2++[r.2.2.2])) (SharedV3.initialPair w,[],[],[])

theorem forest_canonical (w : SharedV3.WBytes) (index : Nat) (hi : index<2^31)
    (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening)
    (hstart : SharedV3.initialPair w=ftsStart)
    (hc : ∀ coord,ChainReadout w coord (coordinateWord words coord) (coordinateValues opened coord))
    (hp : ∀ coord,∃ p3 p2,OuterReadout.Path w coord (coordinateRaw selected coord) (coordinatePath opened coord) p3 p2 ∧
      (4≤coord.val → p2=0)) :
    forest w index (coordinateRaw selected) (coordinateWord words)=OuterForestCorrectness.recoverForest index selected words opened := by
  rw [←OuterSourceForest.grouped_eq,←OuterSourceForest.nine_eq_grouped]
  unfold forest OuterSourceForest.nine
  rw [hstart]
  apply foldlM_congr_mem
  intro acc coord _
  obtain ⟨p3,p2,hp3,hp2⟩:=hp coord
  rw [OuterSourceCoordinate.coordinate_eq_source w index coord _ _ _ _ acc.1 p3 p2 hi (hc coord) hp3 hp2]

#print axioms forest_canonical
end OuterForestModel
