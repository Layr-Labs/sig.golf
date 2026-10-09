import SigGolfCandidate.T3.Secc.LargeCouplingSwap

section
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
theorem nonce_not_secret (m : Message) :
    (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) ∉ Set.range secretCoordinate := by
  rintro ⟨s, hs⟩
  have hp := congrArg Prod.fst hs
  cases s <;> cases hp
def nonceHalf (m : Message) : OtherHalf := ⟨((.inr (.inl m) : Coordinate), 0), nonce_not_secret m⟩
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open OracleComp
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open LargeResidual CanonGraph CanonEncoding
attribute [local instance] Classical.propDecidable
noncomputable scoped instance (priority := high) fintypeCoordinate : Fintype Coordinate := coordinateFintype
noncomputable scoped instance (priority := high) samplerFull : SampleableType FullGame.FullTable :=
  Derivation.outputSampler Coordinate
noncomputable scoped instance (priority := high) samplerLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerOthers : SampleableType OtherHalves :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerPublic (U : Finset HashInput) :
    SampleableType (U → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerCell (U : Finset HashInput) :
    SampleableType (Cell U → LargeResidual.HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerLow : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerNonces : SampleableType (Message → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerVals : SampleableType (Coord → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerWorld : SampleableType (WCoord → LargeResidual.Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRows :
    SampleableType (EncLeaf → Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRowsFlat :
    SampleableType (EncLeaf × Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) decEqNonceOutside :
    DecidableEq (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Classical.decEq _
noncomputable scoped instance (priority := high) fintypeNonceOutside :
    Fintype (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Subtype.fintype _
noncomputable scoped instance (priority := high) samplerNonceOutside :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf → Digest) := SampleableType.ofFintype _
end SigGolfCandidate.T3.Security.LargeCoupling.Samplers
end
