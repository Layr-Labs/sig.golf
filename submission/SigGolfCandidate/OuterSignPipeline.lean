import SigGolfCandidate.OuterSignCompleted
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignPipeline
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign.SharedSearches
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedSerializer
open ClaudeWCT.W9.T3M.SharedCodec
theorem search_serialize {sk : SecretKey} {cache : Bytes 131072} {W : Nat}
    {rho : Digest} {forest : ForestOpening} {pair : Digest×Digest}
    {index : Nat} {p : PreparedRoots} {s : MachineState}
    (hsearch : TBSim OuterImages.signImage sk s W (OuterSigning.searchPreparedLayers (cacheDec cache) index p pair) (OuterSignSearchSource.FramedLayersPost OuterImages.signImage index p s))
    (hfields : ForestFields rho forest s) :
    TBSim OuterImages.signImage sk s (W+(8549+34)) (do
      let layers ← OuterSigning.searchPreparedLayers (cacheDec cache) index p pair
      pure (layers.map (assemble rho forest))) (OuterSignCompleted.FinalPost) := by
  refine TBSim.bind hsearch (W₂:=(8549+34)) ?_
  intro layers t ht
  cases layers with
  | none => exact (TBSim.pure (a:=none) (s:=t) (Q:=OuterSignCompleted.FinalPost) ht).mono (by omega) (fun _ _ h=>h)
  | some layers =>
    rcases ht with ⟨⟨a,top,rfl,ha⟩,hf⟩
    exact OuterSignCompleted.completed_serialize ha (hfields.frame (layers_lowFrame hf))

theorem prepared_serialize {sk : SecretKey} {cache : Bytes 131072} {Wr Ws : Nat}
    {rho : Digest} {forest : ForestOpening} {pair : Digest×Digest}
    {index : Nat} {s : MachineState} {P : PreparedRoots→MachineState→Prop}
    (hroot : TBSim OuterImages.signImage sk s Wr (prepareRoots index) P)
    (hsearch : ∀p t,P p t → TBSim OuterImages.signImage sk t Ws (OuterSigning.searchPreparedLayers (cacheDec cache) index p pair)
      (OuterSignSearchSource.FramedLayersPost OuterImages.signImage index p t))
    (hframe : ∀p t,P p t → Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)))
    (hfields : ForestFields rho forest s) :
    TBSim OuterImages.signImage sk s (Wr+(Ws+(8549+34))) (do
      let prepared ← prepareRoots index
      let layers ← OuterSigning.searchPreparedLayers (cacheDec cache) index prepared pair
      pure (layers.map (assemble rho forest))) (OuterSignCompleted.FinalPost) := by
  refine TBSim.bind hroot (W₂:=Ws+(8549+34)) ?_
  intro p t hp
  exact search_serialize (hsearch p t hp) (hfields.frame (hframe p t hp))

#print axioms search_serialize
#print axioms prepared_serialize
end OuterSignPipeline
