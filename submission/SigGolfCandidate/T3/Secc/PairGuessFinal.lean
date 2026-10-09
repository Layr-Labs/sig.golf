import SigGolfCandidate.T3.Secc.PairGuessEager

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem uniform_congr {X : Type} [Fintype X] (I J : SampleableType X) :
    𝒮[(@uniformSample X I : ProbComp X)] = 𝒮[(@uniformSample X J : ProbComp X)] := by
  apply evalSPMF_ext
  intro x
  rw [@probOutput_uniformSample X I _ x, @probOutput_uniformSample X J _ x]
theorem bind_uniform_congr {X β : Type} [Fintype X] (I J : SampleableType X) (f : X → ProbComp β) :
    𝒮[(@uniformSample X I : ProbComp X) >>= f] = 𝒮[(@uniformSample X J : ProbComp X) >>= f] := by
  rw [evalSPMF_bind, evalSPMF_bind, uniform_congr I J]
end SigGolfCandidate.T3.Security.BPair
