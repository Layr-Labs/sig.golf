import SigGolfCandidate.T3.Secc.WotsMaskChain

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Mask
variable (answers : Answers) (a : ChainAddr)
end Mask
namespace Mask
variable (answers : Answers) (a : ChainAddr)
theorem eval_buildLeaf_sig (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    evalWithAnswerFn T (buildLeaf lay tree leaf digits true) =
      (0, (List.range (chainCount lay)).map (leafValue T lay tree leaf digits)) := by
  have h2 := Correctness.eval_buildLeaf_values T hlay tree leaf digits hvalid true
  have h1 : (evalWithAnswerFn T (buildLeaf lay tree leaf digits true)).1 = 0 := by
    rw [Correctness.buildLeaf_eq]
    simp only [evalWithAnswerFn_bind, ↓reduceIte, evalWithAnswerFn_pure]
  exact Prod.ext h1 h2
def routeLeaf (index : Nat) (lay : Layer) : LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩
theorem route_tree_succ (index m : Nat) (hm : m < 3) :
    (route index (Fin.ofNat 4 (m + 1))).2 =
      (route index (Fin.ofNat 4 m)).2 * 2 ^ height (Fin.ofNat 4 m) + (route index (Fin.ofNat 4 m)).1 := by
  interval_cases m
  · change index / 2 ^ (12 + 7) = index / 2 ^ (19 + 12) * 2 ^ 12 + index / 2 ^ 19 % 2 ^ 12
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
  · change index / 2 ^ (6 + 6) = index / 2 ^ (12 + 7) * 2 ^ 7 + index / 2 ^ 12 % 2 ^ 7
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
  · change index / 2 ^ (0 + 6) = index / 2 ^ (6 + 6) * 2 ^ 6 + index / 2 ^ 6 % 2 ^ 6
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
theorem route_top_index (index : Nat) : (route index 3).2 * 2 ^ height 3 + (route index 3).1 = index := by
  change index / 2 ^ (0 + 6) * 2 ^ 6 + index / 2 ^ 0 % 2 ^ 6 = index
  simp only [Nat.reducePow, Nat.reduceAdd]; omega
theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) : (route index lay).2 < 2 ^ 40 := by
  have : (route index lay).2 ≤ index := Nat.div_le_self _ _
  have : (2 : Nat) ^ 31 < 2 ^ 40 := by decide
  omega
theorem route_leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h := route_leaf_bound index lay
  have : 2 ^ height lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide)
  omega
end Mask
end SigGolfCandidate.T3.Security.Wots
