import SigGolfCandidate.OuterRoutePool
import SigGolfCandidate.OuterImagePatchWindows
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInstalledPool
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M

theorem sign : CodeAt OuterImages.signImage (pcOf 1970) OuterRoutePool.signCode := by
  have old:=OuterImagePatchWindows.slice (by decide : 1970<2^40) SigGolfCandidate.T3M.Sign.SharedControlTail.installed_poolHelper
  change (Images.signCode.drop 1970).take 11=TopRoutePool.signCode at old
  apply codeAt_slice (image:=OuterImages.signImage) (b:=1970) (code:=OuterRoutePool.signCode) (by decide +kernel)
  change (OuterImages.signCode.drop 1970).take 11=OuterRoutePool.signCode
  rw [OuterImagePatchWindows.sign_window 1970 11 (by decide),old]
  decide +kernel

theorem expand : CodeAt OuterImages.expandImage (pcOf 54324) OuterRoutePool.expandIndexCode := by
  have old:=OuterImagePatchWindows.slice (by decide : 54324<2^40) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_poolHelper
  change (Images.expandCode.drop 54324).take 14=TopRoutePool.expandIndexCode at old
  apply codeAt_slice (image:=OuterImages.expandImage) (b:=54324) (code:=OuterRoutePool.expandIndexCode) (by decide +kernel)
  change (OuterImages.expandCode.drop 54324).take 14=OuterRoutePool.expandIndexCode
  rw [OuterImagePatchWindows.expand_window 54324 14 (by decide),old]
  decide +kernel

#print axioms sign
#print axioms expand
end OuterInstalledPool
