import SigGolfCandidate.ClaudeWCT_W9_T3M_Final_BridgeMain
import SigGolfCandidate.ClaudeWCT_W9_T3M_Final_CreditBridge

open OracleComp OracleSpec

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] ClaudeWCT.W9.T3M.Paired.submission SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {I : Images}

theorem submission_terminates (P : Pending I) : (submission I).Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    exact ⟨(P.keygen_runWith hash input).2.1, (P.keygen_runWith hash input).2.2.1⟩
  | sign => obtain ⟨sk,cache,m⟩:=input;exact P.sign_terminates hash sk cache m
  | expand => obtain ⟨m,pk,s⟩:=input;exact P.expand_terminates hash m pk s
  | verify => obtain ⟨m,pk,w⟩:=input;exact P.verify_terminates hash m pk w

theorem witnessCycles_eq : witnessCycles (submission I).sizes.witness=86 := by
  change witnessCycles 22012=86
  decide

theorem claimedC_eq : claimedC=verifyCycleBound+witnessCycles (submission I).sizes.witness := by
  rw [witnessCycles_eq];decide

theorem submission_verificationBound (E : EncodingFacts) (F : SourceQueries) (P : Pending I) :
    (submission I).VerificationBound 6966 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨pk,s,w,he,hacc,hcyc⟩:=Credit.honest_success_verify_cf (submission I) hash sk m h
  obtain ⟨sig,output,wt,hx,rfl⟩:=Credit.Paired.expand_witness E F P hash m pk s w he
  obtain ⟨floors,hfloors,hagree⟩:=Credit.Paired.agree_verifyP hash m pk sig output wt hx
  have heq:=Credit.Paired.verify_run_agree E F P hash (okHashBy floors wt.topHigh hash) m pk _ hagree
  rw [hcyc,witnessCycles_eq,heq]
  rw [heq] at hacc
  have hok : HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh (ClaudeWCT.W9.T3M.Paired.witEncN output wt))
      (okHashBy floors wt.topHigh hash) := by
    rw [ClaudeWCT.W9.T3M.Paired.wtopHigh_witEncN]; exact hashOkBy_okHashBy floors wt.topHigh hash
  have hc:=P.verify_accept_cycles floors hfloors (okHashBy floors wt.topHigh hash) m pk _
    hok (Credit.Paired.digestCap_okHashBy floors wt.topHigh hash m pk sig output wt hx) hacc
  unfold verifyCycleBound at hc
  omega
end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.Legacy
open ClaudeWCT.W9.T3M (Images)
variable {I : Images}

theorem certificate_of (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) :
    Certificate (submission I) 6966 where
  admissible := P.admissible
  termination := submission_terminates P
  completeness := submission_complete E F P S
  compressionBounds := submission_compressionBounds E F P S
  security := submission_secure E F P S.securityP
  verificationBound := submission_verificationBound E F P
end ClaudeWCT.W9.T3M.Final.Paired
