import SigGolfCandidate.OuterSignTopLeaf
import SigGolfCandidate.OuterSignSearchBindings
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignRootCodes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Sign

theorem extra : SharedRootControl.ExtraCode OuterImages.signImage := by
  have old:=SharedRootControl.installed_extraCode
  expose_sign_code
  close_sign_code
theorem low : SharedLowCode.Code OuterImages.signImage := by
  have old:=SharedLowCode.installed_code
  expose_sign_code
  close_sign_code
theorem levels : SharedTreeCode.Code OuterImages.signImage 1013 := by
  have old:=SharedTreeCode.installed_code
  expose_sign_code
  close_sign_code
theorem copy : CodeAt OuterImages.signImage (pcOf (1013+61)) Seed.sub61 := by
  exact OuterSignTransfers.code (b:=1074) (by decide +kernel) SharedLeaf.installed_copy
#print axioms extra
#print axioms low
#print axioms levels
#print axioms copy
end OuterSignRootCodes
