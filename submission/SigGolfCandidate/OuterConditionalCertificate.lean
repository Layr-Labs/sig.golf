import SigGolfCandidate.OuterKeygenBudget
import SigGolfCandidate.OuterPhaseBudget
import SigGolfCandidate.OuterRuntimeComplete
import SigGolfCandidate.OuterVerificationBound
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterConditionalCertificate
open OracleComp OracleSpec OracleComp.EvalDist SigGolfCandidate.Legacy
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.Legacy.Submission.run

theorem terminates : sub.Terminates := by
  intro hash phase input
  cases phase with
  | keygen=>
    rw [OuterKeygenRun.runWith_eq]
    exact ⟨(SigGolfCandidate.T3M.Keygen.keygen_runWith hash input).2.1,
      (SigGolfCandidate.T3M.Keygen.keygen_runWith hash input).2.2.1⟩
  | sign=>obtain ⟨sk,cache,m⟩:=input;exact OuterSignRun.terminates hash sk cache m
  | expand=>obtain ⟨m,pk,s⟩:=input;exact OuterExpandRun.terminates hash m pk s
  | verify=>obtain ⟨m,pk,w⟩:=input;exact OuterVerifyRun.terminates hash m pk w

theorem compressionBounds : sub.CompressionBounds := by
  intro sk phase hphase
  unfold Submission.honestWorkload
  refine expectedValue_bind_le_of_le fun m=>?_
  simp only [Phase.budgeted,List.mem_cons,List.not_mem_nil,or_false] at hphase
  rcases hphase with rfl|rfl|rfl
  · exact OuterKeygenBudget.keygen_bound sk m
  · exact OuterPhaseBudget.sign_bound sk m
  · exact OuterPhaseBudget.expand_bound sk m

/-- All remaining obligations are discharged; security is an explicit, unproved premise. -/
theorem of_security (security : sub.Secure) : Certificate sub 6953 where
  admissible:=OuterAdmissible.admissible
  termination:=terminates
  completeness:=OuterRuntimeComplete.complete
  compressionBounds:=compressionBounds
  security:=security
  verificationBound:=OuterVerificationBound.bound
#print axioms terminates
#print axioms compressionBounds
#print axioms of_security
end OuterConditionalCertificate
