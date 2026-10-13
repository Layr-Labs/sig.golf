import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Extract.Normalize

/-! Legacy T3 extraction helpers still used by the WCT9 proof (campaign S1: the legacy T3 padded-game extraction was
dead code and has been removed). -/
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open SphincsSecurity (bytesLE)
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  T3.leafInput lay tree leaf ends
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
theorem height_le (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem queried_map {α β : Type} (answers : Correctness.Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
end SigGolfCandidate.T3M.Extract
