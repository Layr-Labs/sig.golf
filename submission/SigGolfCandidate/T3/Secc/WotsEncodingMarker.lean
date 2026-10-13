import SigGolfCandidate.T3.Secc.WotsEncodingE1

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
theorem unit_neighbors_le_53 (lay : Layer) (word : Encoding lay) (i : ChainIndex lay) :
    (MixedCode.unitNeighbors word i).card ≤ 53 :=
  (MixedCode.unitNeighbors_card_le word i).trans (Nat.sub_le_sub_right (chainCount_le_54 lay) 1)
end Enc
end SigGolfCandidate.T3.Security.Wots
