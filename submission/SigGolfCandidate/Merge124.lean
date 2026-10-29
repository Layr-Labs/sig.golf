import SigGolfCandidate.Merge094
import SigGolfCandidate.Merge096
import SigGolfCandidate.Merge098
import SigGolfCandidate.Merge109
import SigGolfCandidate.Merge112
import SigGolfCandidate.Merge123

-- ==== merged from Packaging_Ready ====
section

namespace SigGolfCandidate.Packaging
open ClaudeWCT.W9.Machine.ExpandLink (I0)
open ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest (conditionalExtra)

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

/-- The canonical recovered witness carries exactly the extra path credit
needed to offset its accepted digest tier. -/
theorem paired_verificationBound_tier :
    (submission I0).VerificationBound 7003 := by
  let P : Pending I0 := pending_of_machine paired_machineFacts
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨pk,s,w,he,hacc,hcyc⟩ :=
    Credit.honest_success_verify_cf (submission I0) hash sk m h
  obtain ⟨sig,output,wt,hx,rfl⟩ :=
    Credit.Paired.expand_witness encodingFacts sourceQueries_holds P hash m pk s w he
  obtain ⟨floors,hbound,hsum,hagree⟩ :=
    Credit.Paired.agree_verifyP_tier hash m pk sig output wt hx
  have heq := Credit.Paired.verify_run_agree encodingFacts sourceQueries_holds P hash
    (okHashBy floors wt.topHigh hash) m pk _ hagree
  rw [hcyc,witnessCycles_eq,heq]
  rw [heq] at hacc
  have hok : HashOkBy floors
      (ClaudeWCT.W9.T3M.wtopHigh (ClaudeWCT.W9.T3M.Paired.witEncN output wt))
      (okHashBy floors wt.topHigh hash) := by
    rw [ClaudeWCT.W9.T3M.Paired.wtopHigh_witEncN]
    exact hashOkBy_okHashBy floors wt.topHigh hash
  obtain ⟨hextra,hcost⟩ := Credit.Paired.digestTier_okHashBy
    floors wt.topHigh hash m pk sig output wt hx
  have hc := W9Fin.V7.Canonical.Runtime.verify_accept_cycles_tier_of
    I0 rfl paired_admissible W9Fin.V7.Canonical.Runtime.installed_inputs_tier
    (conditionalExtra output) hextra floors hbound hsum
    (okHashBy floors wt.topHigh hash) m pk _ hok hcost hacc
  calc
    _ ≤ 6917 + 86 := Nat.add_le_add_right hc 86
    _ = 7003 := by decide

theorem certificate_ready :
    SigGolf.Certificate (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission) 7003 := by
  change SigGolf.Certificate (submissionNew I0) 7003
  have hbase := certificate_of_security (SigGolfCandidate.Research.SharedExpansionClosure.expandV6_facts
      SigGolfCandidate.Research.SharedExpansionV6.expandExcessNumeric19_holds)
    ClaudeWCT.W9.T3.Secc.Paired.t3_securityP_layout (fun secret => ClaudeWCT.W9.T3.TopMoment.keygen_moment_v6 secret)
    paired_machineFacts
  have hrun : SigGolfCandidate.Transfer.RunAgrees (submissionNew I0) :=
    SigGolfCandidate.Transfer.runAgrees_of_admissible (submissionNew I0)
      (by simpa [legacyOf_submissionNew] using paired_admissible)
  refine { admission := hbase.admission
           completeness := hbase.completeness
           compressionBudgets := hbase.compressionBudgets
           verificationCycles := ?_
           security := hbase.security
           termination := hbase.termination }
  exact SigGolfCandidate.Transfer.verificationCycles_of_legacy
    (submissionNew I0) hrun 7003
    (by simpa [legacyOf_submissionNew] using paired_verificationBound_tier)
end SigGolfCandidate.Packaging
end
