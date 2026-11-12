import SigGolfCandidate.OuterSignRebindNested
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignSearchBindings
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Sign

theorem hints : SharedHints.Code OuterImages.signImage := by
  have old:=SharedHints.installed_code
  expose_sign_code
  close_sign_code
#print axioms hints

theorem lowerRegisters : SharedLowerRegisters.Code OuterImages.signImage := by
  have old:=SharedLowerRegisters.installed_code
  expose_sign_code
  close_sign_code
#print axioms lowerRegisters

theorem floor : SharedFloor.DispatchCode OuterImages.signImage := by
  have old:=SharedFloor.installed_dispatch
  expose_sign_code
  close_sign_code
#print axioms floor

theorem topResidual : LocalSignResidual.TopFullCode OuterImages.signImage := by
  have old:=SharedResidual.installed22230
  expose_sign_code
  close_sign_code
#print axioms topResidual

theorem lowerResidual : LocalSignResidual.LowerFullCode OuterImages.signImage := by
  have old:=SharedResidual.installed22448
  expose_sign_code
  close_sign_code
#print axioms lowerResidual

theorem revealSetup : SharedReveal.SetupCode OuterImages.signImage := by
  have old:=SharedReveal.installed_setupCode
  expose_sign_code
  close_sign_code
#print axioms revealSetup

theorem topBlocks : SharedTopBlocks.Code OuterImages.signImage := by
  have old:=SharedTopBlocks.installed_code
  expose_sign_code
  close_sign_code
#print axioms topBlocks

theorem rootControl : SharedRootControl.Code OuterImages.signImage := by
  have old:=SharedRootControl.installed_code
  expose_sign_code
  close_sign_code
#print axioms rootControl
end OuterSignSearchBindings
