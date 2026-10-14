import SigGolfCandidate.T3.Secc.LargeCouplingQuery
import SigGolfCandidate.T3.Secc.LargeContactMonitor

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
noncomputable local instance instDecidableEqCache_largeCouplingSigning : DecidableEq T3.Cache := Classical.decEq _
section Search
theorem digestRow_isDigest (rho : Digest) (m : Message) (c : BitVec 32) : IsDigestRow (pad64 (digestInput rho m c)) :=
  ⟨rho, m, c, rfl⟩
end Search
section Coherent
theorem digestRow_mem {U : Finset HashInput} (hUpub : SeccLaw.publicUniverse ⊆ U) (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) ∈ U := by
  apply hUpub
  apply SeccLaw.mem_publicUniverse
  have h := Wots.Ref.pad64_length_le (digestInput rho m c)
  have hl : (digestInput rho m c).length = 64 := by
    simp only [digestInput, List.length_append, SphincsSecurity.bytesLE_length]
  unfold SeccLaw.maxInputLength
  omega
end Coherent
end SigGolfCandidate.T3.Security.LargeCoupling
