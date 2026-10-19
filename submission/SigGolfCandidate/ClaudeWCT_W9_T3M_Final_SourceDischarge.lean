import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Queries
import SigGolfCandidate.ClaudeWCT_W9_T3M_Final_Pending
import SigGolfCandidate.ClaudeWCT_W9_T3M_Final_CompletenessV6

namespace ClaudeWCT.W9.T3M.Final
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
end ClaudeWCT.W9.T3M.Final

namespace ClaudeWCT.W9.T3M.Final.Paired
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem sourceFacts_of_securityP (expandV6 : SigGolfCandidate.Research.SharedExpansionClosure.ExpandV6Facts)
    (security : SecurityP) (keygenMoment : KeygenMoment) : SourceFacts where
  honest_keygen_exponential_budget := keygenMoment
  source_completeness := ClaudeWCT.W9.T3.Completeness.Paired.source_completeness
  honest_sign_exponential_budget :=
    SigGolfCandidate.Research.SharedSigningBudget.honest_sign_exponential_budget
      SigGolfCandidate.Research.SharedSigningBudget.schemeFixedCostV6_holds
  honest_expand_exponential_budget :=
    SigGolfCandidate.Research.SharedExpansionClosure.honest_expand_exponential_budget expandV6
  hashOnly_keygen := SigGolfCandidate.T3.SourceReplay.hashOnly_keygen
  hashOnly_sign := SigGolfCandidate.Research.SharedForest.hashOnly_sign
  hashOnly_expand := SigGolfCandidate.Research.SharedForest.hashOnly_expand
  hashOnly_verify := SigGolfCandidate.Research.SharedForest.hashOnly_verify
  securityP := security
end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (isPublic isHash allQ_mono)

private theorem public_is_hash (q : Spec.Domain) (h : isPublic q) : isHash q := by
  rcases q with (tag|input)|coord
  · exact h.elim
  · trivial
  · exact h.elim

theorem sourceQueries_holds : SourceQueries where
  good_sign := SigGolfCandidate.Research.SharedForest.good_sign
  good_expand := SigGolfCandidate.Research.SharedForest.good_expand
  good_verify := SigGolfCandidate.Research.SharedForest.good_verify
  good_expandN := ClaudeWCT.W9.T3M.Paired.goodQ_expandN
  good_verifyP := ClaudeWCT.W9.T3M.Paired.goodQ_verifyP
  public_expandN := ClaudeWCT.W9.T3M.Paired.publicOnly_expandN
  public_expandB := ClaudeWCT.W9.T3M.Paired.publicOnly_expandB
  public_verifyP := ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP
  hashOnly_expandB := fun _ _ _=>allQ_mono (ClaudeWCT.W9.T3M.Paired.publicOnly_expandB ..) public_is_hash
  hashOnly_verifyP := fun _ _ _=>allQ_mono (ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP ..) public_is_hash
end ClaudeWCT.W9.T3M.Final.Paired
