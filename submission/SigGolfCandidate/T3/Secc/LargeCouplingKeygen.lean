import SigGolfCandidate.T3.Secc.LargeCouplingInteraction

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_largeCouplingKeygen : DecidableEq T3.Cache := Classical.decEq _
theorem cacheRegion_congr (f g : Nat → Nat → Digest)
    (h : ∀ level node, 0 ≤ level → level < 12 → node < 2 ^ (12 - level) → f level node = g level node) :
    Correctness.cacheRegion f = Correctness.cacheRegion g := by
  have hw : Correctness.cacheWordList f = Correctness.cacheWordList g := by
    unfold Correctness.cacheWordList
    apply List.flatMap_congr
    intro level hlevel
    rw [List.mem_range'_1] at hlevel
    apply List.map_congr_left
    intro node hnode
    exact h level node (by omega) (by omega) (List.mem_range.mp hnode)
  unfold Correctness.cacheRegion
  rw [hw]
section Keygen
end Keygen
end SigGolfCandidate.T3.Security.LargeCoupling
