import SigGolfCandidate.OuterSignRootCodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignRoots
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Sign
open ClaudeWCT.W9.Machine.Sign.SharedRootBridge

theorem roots_good {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) {forest : BitVec 128×BitVec 128} {s : MachineState}
    (h : Ready sk cache index forest s) :
    TBSim OuterImages.signImage sk s (28+(2*Packed.btCost+3*47)) (SigGolfCandidate.Research.SharedForest.prepareRoots index)
      (fun p t=>SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t ∧ SharedRootControl.LowFrame s t) :=
  SharedRootControl.entry_roots_framed OuterSignSearchBindings.rootControl
    OuterSignRootCodes.extra OuterSignRootCodes.low OuterSignRootCodes.levels
    OuterSignTopLeaf.leaf OuterSignRootCodes.copy OuterSignTopLeaf.chain OuterSignTopLeaf.prefixCode
    OuterSignTopLeaf.seed OuterSignTopLeaf.seedHook
    hi forest s h.pc h.indexMem h.base h.rootLeft h.rootRight
#print axioms roots_good
end OuterSignRoots
