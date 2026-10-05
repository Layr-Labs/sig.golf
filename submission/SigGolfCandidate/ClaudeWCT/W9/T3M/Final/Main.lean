import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Budgets
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.BridgeMain
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.CreditBridge

open OracleComp OracleSpec
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3M.Final (honest_success_verify)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] ClaudeWCT.W9.T3M.submission SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000 in
theorem qfacts (S : SourceFacts) : QFacts where
  hashOnly_keygen := S.hashOnly_keygen
  hashOnly_sign := S.hashOnly_sign
  hashOnly_expandB := hashOnly_expandB
  hashOnly_verifyP := hashOnly_verifyP
  public_expandB := publicOnly_expandB
  public_verifyP := publicOnly_verifyP
  good_keygen := SigGolfCandidate.T3M.goodQ_keygen
  good_sign := goodQ_sign
  good_expandB := goodQ_expandB
  good_verifyP := goodQ_verifyP
variable {I : Images}
theorem submission_terminates (P : Pending I) : (submission I).Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    rw [P.keygen_runWith hash input]
    exact ⟨rfl, show (53919407 : ℕ) < 2 ^ 32 by norm_num⟩
  | sign =>
    obtain ⟨sk, cache, m⟩ := input
    exact P.sign_terminates hash sk cache m
  | expand =>
    obtain ⟨m, pk, s⟩ := input
    exact P.expand_terminates hash m pk s
  | verify =>
    obtain ⟨m, pk, w⟩ := input
    exact P.verify_terminates hash m pk w
theorem witnessCycles_eq : witnessCycles (submission I).sizes.witness = 90 := by
  rw [ClaudeWCT.W9.T3M.submission_sizes]
  decide
theorem claimedC_eq : claimedC = verifyCycleBound + witnessCycles (submission I).sizes.witness := by
  rw [witnessCycles_eq]
  decide
/-- The honest verify run under `hash` is the run under `okHash hash` (`Credit`), which satisfies `HashOk`. -/
theorem submission_verificationBound (P : Pending I) : (submission I).VerificationBound 7643 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨pk, s, w, he, hacc, hcyc⟩ := Credit.honest_success_verify_cf (submission I) hash sk m h
  obtain ⟨N, wt, hx, rfl⟩ := Credit.expand_witness P hash m pk s w he
  have heq := Credit.verify_run_ok P hash m pk _ (Credit.agree_verifyP hash m pk _ N wt hx)
  rw [hcyc, witnessCycles_eq, heq]
  rw [heq] at hacc
  have := P.verify_accept_cycles (SigGolfCandidate.T3M.Verify.okHash hash) m pk _
    (SigGolfCandidate.T3M.Verify.hashOk_okHash hash) hacc
  unfold verifyCycleBound at this
  omega
theorem certificate_of (P : Pending I) (S : SourceFacts) : Certificate (submission I) 7643 where
  admissible := P.admissible
  termination := submission_terminates P
  completeness := submission_complete P S
  compressionBounds := submission_compressionBounds P S
  security := submission_secure (qfacts S) P S.securityP
  verificationBound := submission_verificationBound P
end ClaudeWCT.W9.T3M.Final
