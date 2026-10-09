import SigGolfCandidate.T3.Secc.LargeCouplingKeygen
import SigGolfCandidate.T3.Secc.SeccSufRoute

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingShort : DecidableEq T3.Cache := Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem publicHash_respects (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    Wots.Ref.ShortRespects (publicHash input) := by
  intro A' T' hAT'
  unfold publicHash
  change A' (.inl (.inr (pad64 input))) = T' (.inl (.inr (pad64 input)))
  exact hAT'.public _ h
end Short
end SigGolfCandidate.T3.Security.LargeCoupling
