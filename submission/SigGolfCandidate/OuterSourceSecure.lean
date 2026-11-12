import SigGolfCandidate.OuterSecurityFrozen3
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSourceSecure
 theorem secure : OuterSecurityGame.Secure :=
   OuterLifted3.ClaudeWCT.W9.T3.Secc.Paired.t3_securityP_layout_split
#print axioms secure
end OuterSourceSecure
