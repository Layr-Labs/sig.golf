import SigGolfCandidate.OuterTopCodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterDigestCodes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.T3M.Verify
instance digestLabelCode : DigestLabel.Code OuterImages.expandImage true where
  hook_at := OuterImageTransfers.code (b:=45070) (words:=[0x7552506f]) (by decide +kernel) SharedDigestCode.digestLabelCode.hook_at
  prefix_at := OuterImageTransfers.code (b:=83939) (words:=DigestLabel.prefixWords) (by decide +kernel) SharedDigestCode.digestLabelCode.prefix_at
  hash_at := OuterImageTransfers.code (b:=83945) (words:=[0x73]) (by decide +kernel) SharedDigestCode.digestLabelCode.hash_at
  back_at := OuterImageTransfers.code (b:=83946) (words:=[0x894da06f]) (by decide +kernel) SharedDigestCode.digestLabelCode.back_at

theorem look : LookOK OuterImages.expandImage (look true) :=
  look_of_code true (SharedDigestCode.of_driver OuterTopCodes.driver)

theorem front_tail : CodeAt OuterImages.expandImage (pcOf 1) frontTail :=
  OuterImageTransfers.code (b:=1) (words:=frontTail) (by decide +kernel) SharedFront.installed_tail

theorem front_zero : CodeAt OuterImages.expandImage (pcOf 42719) zeroBlk :=
  OuterImageTransfers.code (b:=42719) (words:=zeroBlk) (by decide +kernel) SharedFront.installed_zero

theorem front_jump : CodeAt OuterImages.expandImage (pcOf 30) [0x7892b06f] :=
  OuterImageTransfers.code (b:=30) (words:=[0x7892b06f]) (by decide +kernel) SharedFront.installed_jump
#print axioms digestLabelCode
#print axioms look
#print axioms front_tail
#print axioms front_zero
#print axioms front_jump
end OuterDigestCodes
