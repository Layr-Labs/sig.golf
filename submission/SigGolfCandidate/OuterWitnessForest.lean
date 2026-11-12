import SigGolfCandidate.OuterWitnessReadout
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterWitnessForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest

theorem forest (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (index : Nat) (hi : index<2^31) :
    OuterForestModel.forest (OuterExpand.witEncOuter output w nonces) index (rawChildFromOutput output)
      (fun k=>forestRank output k.val)=
      OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest := by
  have hp : ∀ k,∃ p3 p2,OuterReadout.Path (OuterExpand.witEncOuter output w nonces) k
      (coordinateRaw (forestSelectionFromOutput output) k) (coordinatePath w.signature.forest k) p3 p2 ∧ (4≤k.val → p2=0) := by
    intro k
    rw [coordinateRaw_output]
    refine ⟨nDig (w.ftsNonces.getD k.val 0),pad16 k.val (w.ftsNonces16.getD k.val 0),OuterWitnessReadout.path output w nonces k,?_⟩
    intro hk
    unfold pad16
    rw [if_neg (by omega)]
  have h:=OuterForestModel.forest_canonical (OuterExpand.witEncOuter output w nonces) index hi
    (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest
    (OuterWitnessReadout.initialPair output w nonces)
    (fun k=>OuterWitnessReadout.chain output w nonces k _ _
      (chainReadout_witEncF16 output w k _ _ (chainReadout_witEncF output w k _ _
        (chainReadout_witEncG output w k _ _ (chainReadout_witEnc output w k _))))) hp
  have hw : coordinateWord (forestWordsFromOutput output)=(fun k=>forestRank output k.val) := by
    funext k
    exact coordinateWord_output output k
  simpa only [coordinateRaw_output,hw] using h

#print axioms forest
end OuterWitnessForest
