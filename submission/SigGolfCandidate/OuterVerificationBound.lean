import SigGolfCandidate.OuterRunValues
import SigGolfCandidate.OuterExpandedAgreement
import SigGolfCandidate.OuterExpandedCap
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterVerificationBound
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.T3M.Final
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.Legacy.Submission.run SigGolfCandidate.T3M.Verify.Agree

theorem run_agree (f g : Hash) (m : Message) (pk : PublicKey) (w : Bytes 21756)
    (hagree : Agree f g (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP m pk w))) :
    sub.runWith f .verify (m,pk,w)=sub.runWith g .verify (m,pk,w) := by
  have hm : Agree f g ((fun r=>r.value.isSome) <$> sub.run .verify (m,pk,w)) :=
    Eq.mpr (congrArg (Agree f g) (OuterRunValues.verify m pk w)) hagree
  have ha : Agree f g (sub.run .verify (m,pk,w)) :=
    (agree_map_iff (fun r=>r.value.isSome) (sub.run .verify (m,pk,w))).mp hm
  exact agree_eval ha

#print axioms run_agree
theorem expand_witness (hash : Hash) (m : Message) (pk : PublicKey)
    (s : Bytes 5184) (w : Bytes 21756) (he : (sub.runWith hash .expand (m,pk,s)).value=some w) :
    ∃sig output wt ns,evalWithAnswerFn (machineAnswers hash 0) (OuterExpand.expandN m pk sig)=some (output,wt,ns) ∧
      w=OuterExpand.witEncOuter output wt ns := by
  have h:=congrArg (evalWithAnswerFn hash) (OuterRunValues.expand m pk s)
  simp only [evalWithAnswerFn_map] at h
  conv_rhs at h => rw [eval_mrealize]
  conv_rhs at h => rw [OuterExpand.expandCompact,evalWithAnswerFn_map]
  unfold Submission.runWith at he
  rw [h] at he
  cases hx : evalWithAnswerFn (machineAnswers hash 0) (OuterExpand.expandN m pk
    (ClaudeWCT.W9.T3M.SharedCodec.sigDecC (OuterSignatureCodec.expand s))) with
  | none=>rw [hx] at he;cases he
  | some p=>
    rw [hx] at he
    exact ⟨_,p.1,p.2.1,p.2.2,hx,(Option.some.inj he).symm⟩

#print axioms expand_witness
theorem bound : sub.VerificationBound 6958 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨pk,s,w,he,hacc,hcyc⟩:=ClaudeWCT.W9.T3M.Final.Credit.honest_success_verify_cf sub hash sk m h
  obtain ⟨sig,output,wt,ns,hx,rfl⟩:=expand_witness hash m pk s w he
  obtain ⟨floors,hfloors,hagree⟩:=OuterExpandedAgreement.agree hash m pk sig output wt ns hx
  have heq:=run_agree hash (okHashBy floors wt.topHigh hash) m pk _ hagree
  have hw : witnessCycles sub.sizes.witness=85:=by decide
  rw [hcyc,hw,heq]
  rw [heq] at hacc
  have hok : HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh (OuterExpand.witEncOuter output wt ns))
      (okHashBy floors wt.topHigh hash) := by
    rw [OuterVerifierLayers.topHigh];exact hashOkBy_okHashBy floors wt.topHigh hash
  have hc:=OuterVerifyRun.accept_cycles floors hfloors (okHashBy floors wt.topHigh hash) m pk _
    hok (OuterExpandedCap.cap floors wt.topHigh hash m pk sig output wt ns hx) hacc
  omega
#print axioms bound
end OuterVerificationBound
