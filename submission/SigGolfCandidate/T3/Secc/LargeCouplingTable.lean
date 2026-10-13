import SigGolfCandidate.T3.Secc.LargeCouplingShort

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
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_largeCouplingTable : DecidableEq T3.Cache := Classical.decEq _
section Table
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
theorem keygen_record (T : Answers) :
    Wots.Ref.pureRecord T keygen (∅, ∅) ∈ support (FirstHit.record keygen (∅, ∅)) ∧
      Wots.Ref.Agrees T (Wots.Ref.pureRecord T keygen (∅, ∅)).state := by
  apply Wots.Ref.fixedRecord_mem_record T keygen (∅, ∅) (Wots.Ref.agrees_empty T)
  rw [Wots.Ref.fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
end Table
end SigGolfCandidate.T3.Security.LargeCoupling
