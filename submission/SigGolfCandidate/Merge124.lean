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

end SigGolfCandidate.Packaging
end
