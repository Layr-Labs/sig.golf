import SigGolfCandidate.T3.Secc.WotsEncodingMarker
import SigGolfCandidate.T3.Secc.WotsContacts
import SigGolfCandidate.T3.Secc.WotsTransportCount

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
noncomputable def contacts (T : Answers) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ ContactAt T trace (chainAt p)).card
theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp
end Enc
end SigGolfCandidate.T3.Security.Wots
