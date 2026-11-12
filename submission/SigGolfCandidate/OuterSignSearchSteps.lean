import SigGolfCandidate.OuterSignSearchSource
import SigGolfCandidate.OuterSignKernel
import SigGolfCandidate.OuterSignSearchBindings
import SigGolfCandidate.OuterSignResidualInit
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignSearchSteps
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Search
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign.SharedSearches

theorem searchCalls (sk : BitVec 256) : SearchCalls OuterImages.signImage sk :=
  ⟨fun _ _ hp=>Canonical.counterSearch_good OuterSignKernel.code hp⟩
theorem topSetup : TopSetupSteps OuterImages.signImage :=
  ⟨SharedTopSetup.steps OuterSignRebind.topSetup⟩
theorem topTail : OuterSignSearchSource.TopTailSteps OuterImages.signImage :=
  ⟨SharedTopDigits.save_steps (OuterSignTransfers.code (by decide +kernel) SharedTopDigits.installed_save),
   OuterSignResidualInit.installed,
   (fun s hp index r c hi hr hc hidx hrm hcm=>by
     simpa only [← LocalRoute.ownSave_one_div] using
       LocalSignResidual.residualTop_steps OuterSignSearchBindings.topResidual s hp index r c hi hr hc hrm hcm hidx),
   SharedControlTail.firstLayer_steps (OuterSignTransfers.code (by decide +kernel) SharedControlTail.installed_firstLayer)⟩
theorem lowerSetup : LowerSetupSteps OuterImages.signImage :=
  ⟨SharedLowerSetup.call_steps OuterSignSearchBindings.floor OuterSignSearchBindings.hints OuterSignSearchBindings.lowerRegisters⟩
theorem lowerTail : LowerTailSteps OuterImages.signImage :=
  ⟨SharedReveal.prepared_steps
     (OuterSignTransfers.code (by decide +kernel) SharedReveal.installed_stepCode)
     (OuterSignTransfers.code (by decide +kernel) SharedReveal.installed_byteCode)
     OuterSignSearchBindings.revealSetup,
   (fun s hp index lay r c hi hl hr hc h8 hidx hrm hcm=>by
     simpa only [lowerSaved_source index lay hl] using
       LocalSignResidual.residualLower_steps OuterSignSearchBindings.lowerResidual s hp index lay r c hi hl hr hc h8 hrm hcm hidx),
   SharedControlTail.nextLayer_steps (OuterSignTransfers.code (by decide +kernel) SharedControlTail.installed_nextLayer)⟩
theorem finish : FinishSteps OuterImages.signImage :=
  ⟨SharedTopDigits.restore_steps (OuterSignTransfers.code (by decide +kernel) SharedTopDigits.installed_restore),
   SharedControlTail.topProduce_steps (OuterSignTransfers.code (by decide +kernel) SharedControlTail.installed_topProduce)⟩
#print axioms searchCalls
#print axioms topSetup
#print axioms topTail
#print axioms lowerSetup
#print axioms lowerTail
#print axioms finish
end OuterSignSearchSteps
