import SigGolfCandidate.OuterSignRebindNested
import SigGolfCandidate.OuterSignLook
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignFrontCodes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign

theorem front : Sign.Boundary.Generic.FrontCodeAt OuterImages.signImage := by
  have old:=Sign.Boundary.Generic.sign_frontCodeAt
  expose_sign_code
  close_sign_code
theorem mac : FullCache.Generic.MacCodeAt OuterImages.signImage true := by
  have old:=FullCache.Generic.sign_macCodeAt
  expose_sign_code
  close_sign_code
theorem label : DigestLabel.Code OuterImages.signImage false := by
  have old:=SharedDigest.digestLabelCode
  constructor
  · exact OuterSignTransfers.code (b:=22614) (words:=[0x80306f]) (by decide +kernel) old.hook_at
  · exact OuterSignTransfers.code (b:=25688) (words:=DigestLabel.prefixWords) (by decide +kernel) old.prefix_at
  · exact OuterSignTransfers.code (b:=25694) (words:=[0x73]) (by decide +kernel) old.hash_at
  · exact OuterSignTransfers.code (b:=25695) (words:=[0xfe1fc06f]) (by decide +kernel) old.back_at
theorem look : LookOK OuterImages.signImage (SharedDigest.look false) :=
  OuterSignLook.transfer _ SharedDigest.installed_sign_look (OuterSignLook.gap0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem success : CodeAt OuterImages.signImage (pcOf 22754) SharedDigestBoundary.signCode :=
  OuterSignTransfers.code (by decide +kernel) SharedDigestBoundary.installed_sign_success
theorem failureJump : CodeAt OuterImages.signImage (pcOf 22764) [0xcccea06f] :=
  OuterSignTransfers.code (by decide +kernel) SharedDigestBoundary.installed_sign_failure_jump
theorem failure : CodeAt OuterImages.signImage (pcOf 543) SharedDigestBoundary.failureCode :=
  OuterSignTransfers.code (by decide +kernel) SharedDigestBoundary.installed_sign_failure
theorem halt : CodeAt OuterImages.signImage (pcOf 545) [0x73] :=
  OuterSignTransfers.code (by decide +kernel) SharedDigestBoundary.installed_sign_failure_ecall
theorem jump : CodeAt OuterImages.signImage (pcOf 153) SharedNonceJump.words :=
  OuterSignTransfers.code (by decide +kernel) SharedNonceJump.installed_code
#print axioms front
#print axioms mac
#print axioms label
#print axioms look
#print axioms success
#print axioms failureJump
#print axioms failure
#print axioms halt
#print axioms jump
end OuterSignFrontCodes
