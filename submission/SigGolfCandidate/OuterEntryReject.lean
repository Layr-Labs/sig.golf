import SigGolfCandidate.OuterEntry
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterEntryReject
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Expand.PrePass
open OuterSignatureCodec

theorem reject (sig : NewSig) (s0 : MachineState) (hpc : s0.pc=pcOf 0)
    (hw : ∀ i,i<648→s0.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (hz : s0.getMem 33856=0) (hc : ¬SharedCodec.nOfB (OuterSignatureCodec.expand sig)<nCanon) :
    ∃ u,Steps OuterImages.expandImage s0 341 341 u ∧ u.pc=pcOf 354 := by
  obtain ⟨v,sv,vp,vm,vr,vz,vf⟩:=OuterEntry.unpack_entry sig s0 hpc hw hz
  obtain ⟨u,vu,up,uz,ur,um,uf⟩:=OuterDecode.pre_entry v _ vp vm
  obtain ⟨t,ut,tp⟩:=OuterPrePass.dec_bad u up (by rw [nOfM_eq um,nOfB_unpack];exact hc)
  exact ⟨t,sv.trans (vu.trans ut),tp⟩
#print axioms reject
end OuterEntryReject
