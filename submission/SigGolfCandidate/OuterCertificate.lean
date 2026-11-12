import SigGolfCandidate.OuterConditionalCertificate
import SigGolfCandidate.OuterSecurityBridgeMain
import SigGolfCandidate.OuterSourceSecure
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCertificate
open SigGolfCandidate.Transfer

theorem secure : OuterImageValidity.sub.Secure :=
  OuterSecurityBridge.submission_secure
    (OuterSecurityBridge.pending ClaudeWCT.W9.Machine.ExpandLink.I0) OuterSourceSecure.secure

theorem legacy : SigGolfCandidate.Legacy.Certificate OuterImageValidity.sub 6958 :=
  OuterConditionalCertificate.of_security secure

def submission : SigGolf.Submission := currentOf OuterImageValidity.sub

theorem certificate : SigGolf.Certificate submission 6958 := by
  have hL : SigGolfCandidate.Legacy.Certificate (legacyOf submission) 6958 := by
    rw [submission,legacyOf_currentOf]
    exact legacy
  have hrun : RunAgrees submission:=runAgrees_of_admissible submission hL.admissible
  exact { admission:=admission_of_legacy submission hL.admissible
          completeness:=completeness_of_legacy submission hrun hL.completeness
          compressionBudgets:=compressionBudgets_of_legacy submission hrun hL.compressionBounds
          verificationCycles:=verificationCycles_of_legacy submission hrun _ hL.verificationBound
          security:=security_of_legacy submission hrun hL.security
          termination:=termination_of_legacy submission hrun hL.termination }
#print axioms secure
#print axioms certificate
end OuterCertificate
