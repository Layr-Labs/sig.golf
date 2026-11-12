import SigGolfCandidate.OuterRecoveryCodes
import SigGolfCandidate.OuterSearchCodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLayerRecovery
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest M)
open SigGolfCandidate.Research ClaudeWCT

theorem run {sk : BitVec 256} {sig : SharedForest.Signature} {index : Nat}
    {msg : WCT9.LayerMsg} {vin : Digest} {s : MachineState}
    (hI : SigGolfCandidate.T3M.Expand.SharedLayers.LInv (SharedForest.mainSignature sig) sig.policyHints index 4 msg s) :
    TBSim OuterImages.expandImage sk s 3790000000
      (SharedForest.recoverHintedLayers sig index (WCT9.topSib (SharedForest.mainSignature sig)) 4 msg)
      (SigGolfCandidate.T3M.Expand.SharedLayers.Post OuterImages.expandImage s (SharedForest.mainSignature sig) sig.policyHints index 4 vin []) := by
  letI := OuterRecoveryCodes.Entry.code
  letI := OuterRecoveryCodes.Core.code
  letI := OuterRecoveryCodes.BC.code
  letI := OuterRecoveryCodes.Packed.code
  letI := OuterRecoveryCodes.Copy.code
  exact SigGolfCandidate.T3M.Expand.SharedLayers.recover_good
    (fun _ _ hp=>Search.CanonicalExpand.counterSearch_good OuterSearchCodes.code hp) hI

#print axioms run
end OuterLayerRecovery
