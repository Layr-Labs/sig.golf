import SigGolfCandidate.OuterSignRoots
import SigGolfCandidate.OuterSignLayers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignBuilt
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches

theorem from_built_framed {sk : SecretKey} {cache : Bytes 131072}
    {index : Nat} (hi : index<2^31) {p : PreparedRoots} {forest : Digest×Digest}
    {s t : MachineState} (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t)
    (hc32 : ∃c<2^32,s.getMem (BitVec.ofNat 64 (Sign.ENC+32))=BitVec.ofNat 64 c) :
    TBSim OuterImages.signImage sk t (prefixCost+335006)
      (OuterSigning.searchPreparedLayers (cacheDec cache) index p forest)
      (OuterSignSearchSource.FramedLayersPost OuterImages.signImage index p t) := by
  apply OuterSignLayers.layers index hi p forest t h.pc (built_stable h)
    (base_stateBase h.base) h.hintZero
  obtain ⟨c,hc,hv⟩:=hc32
  exact ⟨c,hc,h.counterMem.trans hv⟩
#print axioms from_built_framed
end OuterSignBuilt
