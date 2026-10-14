import SigGolfCandidate.T3.Secc.LargeCouplingSwap

section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open OracleComp
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open LargeResidual
attribute [local instance] Classical.propDecidable
noncomputable scoped instance (priority := high) fintypeCoordinate : Fintype Coordinate := coordinateFintype
noncomputable scoped instance (priority := high) samplerFull : SampleableType FullGame.FullTable :=
  Derivation.outputSampler Coordinate
noncomputable scoped instance (priority := high) samplerPublic (U : Finset HashInput) :
    SampleableType (U → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerCell (U : Finset HashInput) :
    SampleableType (Cell U → LargeResidual.HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerNonces : SampleableType (Message → Digest) :=
  SampleableType.ofFintype _
end SigGolfCandidate.T3.Security.LargeCoupling.Samplers
end
