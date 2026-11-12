import SigGolfCandidate.OuterWitnessForest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPlainForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M

theorem forest (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (index : Nat) (hi : index<2^31) :
    OuterForestModel.forest (Paired.witEnc output w) index (rawChildFromOutput output)
      (fun k=>forestRank output k.val)=
      OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest := by
  have hp : ∀ k,∃ p3 p2,OuterReadout.Path (Paired.witEnc output w) k
      (coordinateRaw (forestSelectionFromOutput output) k) (coordinatePath w.signature.forest k) p3 p2 ∧ (4≤k.val → p2=0) := by
    intro k
    rw [coordinateRaw_output]
    refine ⟨_,0,OuterReadout.of_old (pathReadout_witEnc output w k),fun _=>rfl⟩
  have h:=OuterForestModel.forest_canonical (Paired.witEnc output w) index hi
    (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest
    (by simpa only [ftsStart] using PairedReadout.initialPair_witEnc output w)
    (fun k=>chainReadout_witEnc output w k _) hp
  have hw : coordinateWord (forestWordsFromOutput output)=(fun k=>forestRank output k.val) := by
    funext k
    exact coordinateWord_output output k
  simpa only [coordinateRaw_output,hw] using h

#print axioms forest
end OuterPlainForest
