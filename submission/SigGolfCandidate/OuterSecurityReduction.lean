import SigGolfCandidate.OuterPaddedGame
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterSecurityReduction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open OuterSecurityGame
attribute [local instance] Classical.propDecidable

theorem large_budget (adversary : OuterSecurityGame.Adversary) (q : Nat) (hq : 2^127≤q) :
    Pr[fun r=>r.1=true ∧ r.2≤q | experiment adversary]≤(q:ENNReal)/2^127 := by
  apply probEvent_le_one.trans
  have hcast : (2:ENNReal)^127≤(q:ENNReal):=by exact_mod_cast hq
  calc
    (1:ENNReal)=(2:ENNReal)^127/(2:ENNReal)^127:=(ENNReal.div_self (by positivity) (by finiteness)).symm
    _≤_:=ENNReal.div_le_div_right hcast _

/-- The clean-trace probability bound is an explicit remaining premise. -/
theorem of_clean_bound
    (hclean : ∀(adversary : OuterSecurityGame.Adversary)(q : Nat),1≤q→∀hq:q≤2^127,
      Pr[QueryRecorded.CleanWin q | OuterPaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+((2:ENNReal)^152)⁻¹+q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127) : OuterSecurityGame.Secure := by
  intro adversary q hpositive
  by_cases hq : 2^127≤q
  · exact large_budget adversary q hq
  · have hs : q≤2^127:=by omega
    exact (OuterPaddedGame.real_to_clean_trace adversary q hs).trans (hclean adversary q hpositive hs)
#print axioms of_clean_bound
end OuterSecurityReduction
