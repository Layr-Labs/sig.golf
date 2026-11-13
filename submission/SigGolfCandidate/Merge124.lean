import SigGolfCandidate.Merge094
import SigGolfCandidate.Merge096
import SigGolfCandidate.Merge098
import SigGolfCandidate.Merge109
import SigGolfCandidate.Merge112T
import SigGolfCandidate.Merge123
set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from Packaging_Ready ====
section

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] ClaudeWCT.W9.T3M.Paired.submission SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {I : Images}
theorem submission_verificationBound_tight (E : EncodingFacts) (F : SourceQueries) (P : Pending I) :
    (submission I).VerificationBound 6959 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨pk,s,w,he,hacc,hcyc⟩:=Credit.honest_success_verify_cf (submission I) hash sk m h
  obtain ⟨sig,output,wt,hx,rfl⟩:=Credit.Paired.expand_witness E F P hash m pk s w he
  obtain ⟨floors,hfloors,hagree⟩:=Credit.Paired.agree_verifyP hash m pk sig output wt hx
  have heq:=Credit.Paired.verify_run_agree E F P hash (okHashBy floors wt.topHigh hash) m pk _ hagree
  rw [hcyc,witnessCycles_eq,heq]
  rw [heq] at hacc
  have hok : HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh (ClaudeWCT.W9.T3M.Paired.witEncF16 output wt))
      (okHashBy floors wt.topHigh hash) := by
    rw [ClaudeWCT.W9.T3M.Paired.wtopHigh_witEncF16]; exact hashOkBy_okHashBy floors wt.topHigh hash
  have hc:=P.verify_accept_cycles floors hfloors (okHashBy floors wt.topHigh hash) m pk _
    hok (Credit.Paired.digestCap_okHashBy floors wt.topHigh hash m pk sig output wt hx) hacc
  unfold verifyCycleBound at hc
  omega
end ClaudeWCT.W9.T3M.Final.Paired

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
    SigGolf.Certificate (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission) 6959 := by
  change SigGolf.Certificate (submissionNew I0) 6959
  have previous := certificate_of_security (SigGolfCandidate.Research.SharedExpansionClosure.expandV6_facts
      SigGolfCandidate.Research.SharedExpansionV6.expandExcessNumeric19_holds)
    ClaudeWCT.W9.T3.Secc.Paired.t3_securityP_layout_split (fun secret => ClaudeWCT.W9.T3.TopMoment.keygen_moment_v6 secret)
    paired_machineFacts
  have hL : (SigGolfCandidate.Transfer.legacyOf (submissionNew I0)).VerificationBound 6959 := by
    rw [legacyOf_submissionNew]
    exact submission_verificationBound_tight encodingFacts sourceQueries_holds (pending_of_machine paired_machineFacts)
  have hrun : SigGolfCandidate.Transfer.RunAgrees (submissionNew I0) :=
    SigGolfCandidate.Transfer.runAgrees_of_admissible (submissionNew I0) (by
      rw [legacyOf_submissionNew]
      exact paired_admissible)
  exact { admission := previous.admission
          completeness := previous.completeness
          compressionBudgets := previous.compressionBudgets
          verificationCycles := SigGolfCandidate.Transfer.verificationCycles_of_legacy (submissionNew I0) hrun _ hL
          security := previous.security
          termination := previous.termination }
end SigGolfCandidate.Packaging
end
