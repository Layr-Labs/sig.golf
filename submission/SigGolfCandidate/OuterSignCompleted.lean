import SigGolfCandidate.OuterLayerFields
import SigGolfCandidate.OuterSignPackFinal
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignCompleted
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign.SharedSearches
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedSerializer
open ClaudeWCT.W9.T3M.SharedCodec

def FinalPost : Option SharedSignature→MachineState→Prop
  | none,t=>SearchError OuterImages.signImage t
  | some sig,t=>t.pc=pcOf 26240 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t SIG 5183=OuterLooseCodec.compress (sigBC sig) ∧ fetch OuterImages.signImage t=some (.base .ECALL)

theorem completed_serialize {sk : SecretKey}
    {rho : Digest} {forest : ForestOpening} {index : Nat} {p : PreparedRoots}
    {a : OuterSignSearchSource.Choices} {top : Pieces} {s : MachineState}
    (hs : OuterSignSearchSource.Completed index p a top s) (hforest : ForestFields rho forest s) :
    TBSim OuterImages.signImage sk s (8549+34)
      (pure (some (assemble rho forest (OuterSignSearchSource.layersValue index p a top)))) FinalPost := by
  have hr:=assembled_raw s rho (OuterSignSearchSource.layersValue index p a top).policyHints forest _
    hforest.rho hforest.values hforest.paths (OuterLayerFields.completed_layer_fields hs)
  have hl : (OuterSignSearchSource.layersValue index p a top).policyHints.toNat=a.hints index := by
    simp only [OuterSignSearchSource.layersValue,BitVec.toNat_ofNat,Nat.reducePow]
    have :=hs.hintsLt
    omega
  have hh : s.getMem (BitVec.ofNat 64 417792)=BitVec.ofNat 64 (OuterSignSearchSource.layersValue index p a top).policyHints.toNat:=by
    rw [hl]
    exact hs.hints
  obtain ⟨n,c,hn,t,st,pt,h5,h10,hbytes,hw,ht⟩:=OuterSerializeWords.serialize_good
    OuterSerializerCode.code s hs.pc _ hr hh (by rw [hl];exact hs.hintsOK)
  obtain ⟨u,tu,up,u5,u10,ub,uf⟩:=OuterSignPackFinal.run _ t pt h5 h10 hw ht
  have hpost : FinalPost (some (assemble rho forest (OuterSignSearchSource.layersValue index p a top))) u:=
    ⟨up,u5,u10,ub,uf⟩
  exact (TBSim.pure_steps' (st.trans tu) hpost).mono (by omega) (fun _ _ h=>h)
#print axioms completed_serialize
end OuterSignCompleted
