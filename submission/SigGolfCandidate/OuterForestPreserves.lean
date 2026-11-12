import SigGolfCandidate.OuterForestDomains
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterForestPreserves
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Freshness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.PairRows

theorem avoids_forest (secret : BitVec 256) (target : HashInput) (ht : SigGolfCandidate.T3.Freshness.SearchQ target)
    (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Avoids secret target (OuterForestMoment.forest index selected words) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (OuterForestDomains.forest_queries index selected words)
    (fun q hq => ClaudeWCT.W9.T3.Freshness.Paired.avoidsQuery secret target ht index q hq)

theorem forest_preserves_rows (secret : BitVec 256) (index stage : Nat) (selected : ForestSelection)
    (words : ForestWords) (cache : RCache) (hfresh : RowsFreshFrom stage cache)
    (result : (ForestOpening × PairRoot) × RCache)
    (hr : result∈support (roRun secret (OuterForestMoment.forest index selected words) cache)) :
    RowsFreshFrom stage result.2 := by
  intro lay hl tree leaf left right counter hc
  rw [preserves secret _ _ (avoids_forest secret _ (rowQ_pairTrial ..).searchQ index selected words) cache result hr]
  exact hfresh lay hl tree leaf left right counter hc

theorem forest_allGFresh (secret : BitVec 256) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (cache : RCache) (hc : ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.AllGFresh cache)
    (result : (ForestOpening × PairRoot) × RCache)
    (hr : result∈support (roRun secret (OuterForestMoment.forest index selected words) cache)) :
    ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.AllGFresh result.2 :=
  ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.preserves_allG secret _
    (fun target lay tree heap ht hp => ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono
      (OuterForestDomains.forest_queries index selected words)
      (fun q hq => ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.gav_ftsQuery secret target lay tree heap ht hp index q hq))
    cache hc result hr

#print axioms forest_preserves_rows
#print axioms forest_allGFresh
end OuterForestPreserves
