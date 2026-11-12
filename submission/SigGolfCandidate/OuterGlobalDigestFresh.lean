import SigGolfCandidate.OuterGlobalFresh
import SigGolfCandidate.Merge054
set_option debug.skipKernelTC false
set_option backward.isDefEq.respectTransparency false
namespace OuterGlobalFresh
open OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.QuerySpace
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh (fTrial_header)
theorem AllFFresh.cacheQuery_digest {cache : RCache} (h : AllFFresh cache)
    (rho : Digest) (message : Message) (counter : Nat) (answer : HashOutput) :
    AllFFresh (cache.cacheQuery (digestTrial rho message counter) answer) := by
  intro coord index heap hp n left right
  rw [QueryCache.cacheQuery_of_ne]
  · exact h coord index heap hp n left right
  · exact (fq_ne (queryHeader_digest rho message counter) (digestHeader_ne_fts _ hp)
      (fTrial_header coord index heap n left right)).symm
#print axioms AllFFresh.cacheQuery_digest
end OuterGlobalFresh
