import SigGolfCandidate.OuterVerifierForestSource
import SigGolfCandidate.OuterWitnessOuterPad
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifierForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired

theorem outer_coord : ∀c : Fin 9,SharedV3.first c.val=false→OuterExpand.outerCoord (c.val/2)=c.val := by decide +kernel

theorem forest (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (index : Nat) (hi : index<2^31) :
    SharedV3.forest (OuterExpand.witEncOuter output w ns5) index (rawChildFromOutput output)
      (fun k=>embed (forestRank output k.val))=
      OuterFixedForest.forest index (forestSelectionFromOutput output) (forestWordsFromOutput output)
        w.signature.forest w.ftsNonces w.ftsNonces16 ns5 := by
  rw [←OuterVerifierForestSource.nine_eq]
  unfold SharedV3.forest OuterVerifierForestSource.nine
  rw [OuterWitnessReadout.initialPair]
  apply foldlM_congr_mem
  intro prev coord _
  simp only [coordinateRaw_output,coordinateWord_output]
  have hc : ChainReadout (OuterExpand.witEncOuter output w ns5) coord (forestRank output coord.val)
      (W9Drv.SharedCanonical.coordinateValues w.signature.forest coord) :=
    OuterWitnessReadout.chain output w ns5 coord _ _ (chainReadout_witEncF16 output w coord _ _
      (chainReadout_witEncF output w coord _ _ (chainReadout_witEncG output w coord _ _
        (chainReadout_witEnc output w coord _))))
  have hp:=OuterWitnessReadout.path output w ns5 coord
  cases hf : SharedV3.first coord.val with
  | true=>exact OuterVerifierCoordinate.first _ index coord _ _ _ _ _ _ _ prev hi hc hp hf
  | false=>
    apply OuterVerifierCoordinate.second _ index coord _ _ _ _ _ _ _ prev hi hc hp hf
    let k : Fin 5:=⟨coord.val/2,by omega⟩
    have he : OuterWitnessOuterPad.coord k=coord:=by
      apply Fin.ext
      exact outer_coord coord hf
    have h:=OuterWitnessOuterPad.pad output w ns5 k (SharedV3.physical coord.val (rawChildFromOutput output coord).val)
    simpa only [he] using h
#print axioms forest
end OuterVerifierForest
