import SigGolfCandidate.OuterValidate
import SigGolfCandidate.OuterImageTransfers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInstalledValidate
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open LocalRouteResiduals

theorem code : OuterValidate.Code OuterImages.expandImage := by
  constructor
  · exact OuterImageTransfers.code (b:=46929) (words:=initCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.init
  · exact OuterInstalledPool.expand
  · constructor
    · exact OuterImageTransfers.code (b:=46933) (words:=pre0Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r0.pre
    · exact OuterImageTransfers.code (b:=88060) (words:=LocalRouteMachineHelpers.expand1Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r0.helper
    · exact OuterImageTransfers.code (b:=46936) (words:=test0Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r0.test
    · exact OuterImageTransfers.code (b:=46937) (words:=LocalRouteResiduals.zero0Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r0.zero
    · exact OuterImageTransfers.code (b:=46939) (words:=LocalRouteResiduals.sub0Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r0.sub
  · constructor
    · exact OuterImageTransfers.code (b:=46949) (words:=pre1Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r1.pre
    · exact OuterImageTransfers.code (b:=88072) (words:=LocalRouteMachineHelpers.expand2Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r1.helper
    · exact OuterImageTransfers.code (b:=46952) (words:=test1Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r1.test
    · exact OuterImageTransfers.code (b:=46953) (words:=LocalRouteResiduals.zero1Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r1.zero
    · exact OuterImageTransfers.code (b:=46955) (words:=LocalRouteResiduals.sub1Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r1.sub
  · constructor
    · exact OuterImageTransfers.code (b:=46966) (words:=pre2Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r2.pre
    · exact OuterImageTransfers.code (b:=88084) (words:=LocalRouteMachineHelpers.expand3Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r2.helper
    · exact OuterImageTransfers.code (b:=46969) (words:=test2Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r2.test
    · exact OuterImageTransfers.code (b:=46970) (words:=LocalRouteResiduals.zero2Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r2.zero
    · exact OuterImageTransfers.code (b:=46972) (words:=LocalRouteResiduals.sub2Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.r2.sub
  · exact OuterImageTransfers.code (b:=46940) (words:=range1Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.range1
  · exact OuterImageTransfers.code (b:=46956) (words:=range2Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.range2
  · exact OuterImageTransfers.code (b:=46973) (words:=range3Code) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.range3
  · exact OuterImageTransfers.code (b:=46942) (words:=lookup1PreCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.lookup1Pre
  · exact OuterImageTransfers.code (b:=46945) (words:=lookup1LoadCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.lookup1Load
  · exact OuterImageTransfers.code (b:=46946) (words:=lookup1PostCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.lookup1Post
  · exact OuterImageTransfers.code (b:=46958) (words:=lookup2PreCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.lookup2Pre
  · exact OuterImageTransfers.code (b:=46961) (words:=lookup2LoadCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.lookup2Load
  · exact OuterImageTransfers.code (b:=46962) (words:=lookup2PostCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.lookup2Post
  · exact OuterImageTransfers.code (b:=46975) (words:=lastCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.last
  · exact OuterImageTransfers.code (b:=87800) (words:=l3eCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.l3e
  · exact OuterImageTransfers.code (b:=88160) (words:=l3HelperCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.l3Helper
  · exact OuterImageTransfers.code (b:=87812) (words:=l3OkCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.l3Ok
  · exact OuterImageTransfers.code (b:=87813) (words:=l3BadCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.l3Bad
  · exact OuterImageTransfers.code (b:=46978) (words:=goodCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.good
  · exact OuterImageTransfers.code (b:=46979) (words:=badCode) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.SharedValidateV6.installed_code.bad

#print axioms code
end OuterInstalledValidate
