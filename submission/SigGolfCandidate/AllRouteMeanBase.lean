import SigGolfCandidate.AllRouteWeight
import SigGolfCandidate.Merge053
set_option debug.skipKernelTC false
open scoped BigOperators
namespace ClaudeWCT.Numerics.AllRouteMean
open Finset SigGolfCandidate.T3 SigGolfCandidate.AllRoute
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.CanonicalSearch
open ClaudeWCT.Numerics.AllRoute
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
attribute [local irreducible] Finset.univ


 theorem sum_index_digits (f : Nat → Nat → Nat → Nat) :
    (∑ i : Fin (2^31), f (i.val/524288) (i.val/4096%128) (i.val/64%64)) =
    64 * ∑ x : Fin 4096, ∑ y : Fin 128, ∑ z : Fin 64, f x.val y.val z.val := by
  have hrew : (∑ i : Fin (2^31), f (i.val/524288) (i.val/4096%128) (i.val/64%64)) =
      ∑ i : Fin (4096*524288), f (i.val/524288) (i.val%524288/4096) (i.val%524288%4096/64) := by
    apply sum_congr rfl
    intro i hi
    congr 1 <;> omega
  rw [hrew]
  rw [sum_split 4096 524288 (by decide) (fun x y => f x (y/4096) (y%4096/64))]

  calc
    (∑ x : Fin 4096, ∑ y : Fin 524288, f x.val (y.val/4096) (y.val%4096/64)) =
      ∑ x : Fin 4096, ∑ y : Fin 128, ∑ z : Fin 4096, f x.val y.val (z.val/64) := by
        apply sum_congr rfl
        intro x hx
        exact sum_split 128 4096 (by decide) (fun y z => f x.val y (z/64))
    _ = ∑ x : Fin 4096, ∑ y : Fin 128, ∑ z : Fin 64, ∑ t : Fin 64, f x.val y.val z.val := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      exact sum_split 64 64 (by decide) (fun z _ => f x.val y.val z)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_sum]

def initBySavings (s0 s1 s2 : Nat) : Nat :=
  (([initial_000,initial_010,initial_100,initial_110,initial_200,initial_210].getD (2*s1+s2) #[])[2-s0]?).getD 0

def meanInitial : Nat := ClaudeWCT.Numerics.AllRoute.meanInitial

 theorem actual_initial (index : Nat) :
    AllRoute.initialValue (saveClass index) (poolClass index) =
      initBySavings (ClaudeWCT.Numerics.TopRoute.pathSave (index/524288))
        (lowerSave 1 (index/4096%128)) (lowerSave 2 (index/64%64)) := by
  have hs : ClaudeWCT.WCT9.CanonicalPolicy.topPathSave (route index 0).1 ≤ 2 := by
    unfold ClaudeWCT.WCT9.CanonicalPolicy.topPathSave ClaudeWCT.WCT9.CanonicalPolicy.topPairSave
    split_ifs <;> omega
  have hp : (poolClass index).val = 2-ClaudeWCT.Numerics.TopRoute.pathSave (index/524288) := by
    unfold poolClass requiredCredit ClaudeWCT.WCT9.CanonicalPolicy.routePool
    change max 72 (74-ClaudeWCT.WCT9.CanonicalPolicy.topPathSave (route index 0).1)-72 = _
    have hr : (route index 0).1 = index/524288%4096 := rfl
    have ht : ClaudeWCT.WCT9.CanonicalPolicy.topPathSave (route index 0).1 =
        ClaudeWCT.Numerics.TopRoute.pathSave (index/524288) := by
      rw [hr]
      have hmod : (index/524288%4096)%4 = index/524288%4 := by omega
      have hdiv : (index/524288%4096)/64%4 = index/524288/64%4 := by omega
      simp only [ClaudeWCT.WCT9.CanonicalPolicy.topPathSave, ClaudeWCT.WCT9.CanonicalPolicy.topPairSave,
        ClaudeWCT.Numerics.TopRoute.pathSave, ClaudeWCT.Numerics.TopRoute.pairSave, hmod, hdiv]

    rw [ht] at hs ⊢
    omega
  simp only [AllRoute.initialValue, AllRoute.initialRow, initBySavings,
    Array.getD_eq_getD_getElem?, hp]
  congr 3

 def byPair (s0 s1 : Nat) : Nat := 32*initBySavings s0 s1 0 + 32*initBySavings s0 s1 1
 def byOne (s0 : Nat) : Nat := 49*byPair s0 0 + 64*byPair s0 1 + 15*byPair s0 2

 theorem reduced_checked :
    64 * (1024*byOne 0 + 2048*byOne 1 + 1024*byOne 2) ≤ 2^31 * meanInitial := by decide +kernel


#print axioms sum_index_digits
#print axioms actual_initial
#print axioms reduced_checked
end ClaudeWCT.Numerics.AllRouteMean
