import SigGolfCandidate.W9Fin.V7.Final
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.ExpandLink.Link
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.ExpandLink.SignLink
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Conditional
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.Final
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCert

namespace SigGolfCandidate.Packaging
open ClaudeWCT.W9.Machine.ExpandLink (I0)
open ClaudeWCT.W9.T3M.Final.Paired

theorem paired_submission_eq : submission I0=SigGolfCandidate.T3M.Paired.submission := rfl

theorem paired_admissible : (submission I0).Admissible := by
  rw [paired_submission_eq]
  exact SigGolfCandidate.T3M.Paired.submission_admissible

theorem paired_sign_refines : SignRefines I0 := by
  intro sk cache message
  exact ClaudeWCT.W9.Machine.Sign.SharedController.sign_refines sk cache message

theorem paired_sign_terminates : SignTerminates I0 := by
  intro hash sk cache message
  exact ClaudeWCT.W9.Machine.Sign.SharedController.sign_terminates hash sk cache message

theorem paired_verify_inputs : VerifyRefines I0 ∧ VerifyTerminates I0 ∧ VerifyAcceptCycles I0 :=
  W9Fin.V7.Canonical.Runtime.installed_verify_inputs I0 rfl paired_admissible

theorem paired_machineFacts : MachineFacts I0 where
  admissible := paired_admissible
  sign_refines := paired_sign_refines
  sign_terminates := paired_sign_terminates
  expand_refines := ClaudeWCT.W9.Machine.ExpandLink.paired_expand_pending.1
  expand_terminates := ClaudeWCT.W9.Machine.ExpandLink.paired_expand_pending.2
  verify_refines := paired_verify_inputs.1
  verify_terminates := paired_verify_inputs.2.1
  verify_accept_cycles := paired_verify_inputs.2.2

theorem certificate_ready :
    SigGolf.Certificate (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission) 6990 := by
  change SigGolf.Certificate (submissionNew I0) 6990
  exact certificate_of_security ClaudeWCT.W9.T3.Secc.Paired.t3_securityP paired_machineFacts
end SigGolfCandidate.Packaging

#print axioms SigGolfCandidate.Packaging.paired_machineFacts
#print axioms SigGolfCandidate.Packaging.certificate_ready
