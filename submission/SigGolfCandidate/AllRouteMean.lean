import SigGolfCandidate.AllRouteMeanGeneric
set_option debug.skipKernelTC false
open scoped BigOperators
namespace ClaudeWCT.Numerics.AllRouteMean
open Finset SigGolfCandidate.T3 SigGolfCandidate.AllRoute
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.CanonicalSearch
open ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.TopZero
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] Finset.univ initBySavings
set_option Elab.async false
 theorem actual_sum_eq :
    (∑ i : Fin (2^31), AllRoute.initialValue (saveClass i.val) (poolClass i.val)) = allWeight initBySavings := by
  have h1 : (∑ i : Fin (2^31), AllRoute.initialValue (saveClass i.val) (poolClass i.val)) =
      ∑ i : Fin (2^31), initBySavings (ClaudeWCT.Numerics.TopRoute.pathSave (i.val/524288))
        (lowerSave 1 (i.val/4096%128)) (lowerSave 2 (i.val/64%64)) :=
    sum_congr rfl (fun i _ => actual_initial i.val)
  exact h1.trans (sum_route_savings initBySavings)
 theorem index_initial_sum :
    (∑ i : Fin (2^31), AllRoute.initialValue (saveClass i.val) (poolClass i.val)) ≤ 2^31 * meanInitial := by
  have h : allWeight initBySavings ≤ 2^31 * meanInitial := by
    simpa only [allWeight,oneWeight,pairWeight,byOne,byPair] using reduced_checked
  exact actual_sum_eq.trans_le h
 theorem envelope_ratio_le_two :
    (((fixedBoundU16 : ℝ) / scale) * ((groundBound : ℝ) / scale)) *
      (((ftsBound : ℝ) / scale) * ((meanInitial : ℝ) / scale)) ≤ 2 := by
  have hm := mulUp_ratio_ge fixedBoundU16 groundBound
  have hn : mulUp (mulUp (mulUp fixedBoundU16 groundBound) ftsBound) meanInitial * 100000 < 199999 * scale := by
    simpa only [meanInitial] using ClaudeWCT.Numerics.AllRoute.full_moment_checked
  have he := ClaudeWCT.Numerics.TopRoute.envelope_from_integer
    (mulUp fixedBoundU16 groundBound) meanInitial 199999 (by norm_num)
    hn
  have h0 : (0 : ℝ) ≤ ((ftsBound : ℝ) / scale) * ((meanInitial : ℝ) / scale) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_right hm h0).trans he
#print axioms actual_sum_eq
#print axioms index_initial_sum
#print axioms envelope_ratio_le_two
end ClaudeWCT.Numerics.AllRouteMean
