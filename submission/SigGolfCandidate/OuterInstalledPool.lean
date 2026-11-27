import SigGolfCandidate.OuterRoutePool
import SigGolfCandidate.OuterImagePatchWindows
import SigGolfCandidate.OuterSignTransfers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInstalledPool
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M

theorem sign : OuterRoutePool.SignAt OuterImages.signImage := by
  have old:=SigGolfCandidate.T3M.Sign.SharedControlTail.installed_poolHelper
  refine And.intro ?_ (OuterSignTransfers.code_tail (b:=26415) (by decide) (by decide +kernel) old.2)
  have old1:=OuterImagePatchWindows.slice (by decide : 1970<2^40) old.1
  change (Images.signCode.drop 1970).take 11=TopRoutePool.signCode at old1
  apply codeAt_slice (image:=OuterImages.signImage) (b:=1970) (code:=TopRoutePool.signCode) (by decide +kernel)
  change (OuterImages.signCode.drop 1970).take 11=TopRoutePool.signCode
  rw [OuterImagePatchWindows.sign_window 1970 11 (by decide),old1]
  decide +kernel

theorem expand : OuterRoutePool.ExpandAt OuterImages.expandImage := by
  have old:=ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_poolHelper
  refine And.intro ?_ ?_
  · have old1:=OuterImagePatchWindows.slice (by decide : 54324<2^40) old.1
    change (Images.expandCode.drop 54324).take 14=TopRoutePool.expandIndexCode at old1
    apply codeAt_slice (image:=OuterImages.expandImage) (b:=54324) (code:=TopRoutePool.expandIndexCode) (by decide +kernel)
    change (OuterImages.expandCode.drop 54324).take 14=TopRoutePool.expandIndexCode
    rw [OuterImagePatchWindows.expand_window 54324 14 (by decide),old1]
    decide +kernel
  · exact codeAt_of_window_eq (source:=Images.expandImage) (target:=OuterImages.expandImage) (start:=88339)
      (count:=147437) (by decide) (by decide +kernel) (by decide)
      (OuterImageWindows.high_window 88339 147437 (by decide) (by decide)).symm old.2

#print axioms sign
#print axioms expand
end OuterInstalledPool
