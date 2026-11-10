import SigGolfCandidate.AllRouteSavings
import SigGolfCandidate.TopRouteWeight
open scoped BigOperators
namespace SigGolfCandidate.AllRoute
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
lemma l1_sum (f : Nat → Nat) :
    (∑ i : Fin 128, f (lowerSave 1 i.val)) = 49 * f 0 + 64 * f 1 + 15 * f 2 := by
  have h0 : (Finset.univ.filter (fun i : Fin 128 => lowerSave 1 i.val = 0)).card = 49 := by decide +kernel
  have h1 : (Finset.univ.filter (fun i : Fin 128 => lowerSave 1 i.val = 1)).card = 64 := by decide +kernel
  have h2 : (Finset.univ.filter (fun i : Fin 128 => lowerSave 1 i.val = 2)).card = 15 := by decide +kernel
  have hx (i : Fin 128) : f (lowerSave 1 i.val) =
      (if lowerSave 1 i.val = 0 then f 0 else 0) +
      (if lowerSave 1 i.val = 1 then f 1 else 0) +
      (if lowerSave 1 i.val = 2 then f 2 else 0) := by
    have hb := l1_bounds i
    have hc : lowerSave 1 i.val = 0 ∨ lowerSave 1 i.val = 1 ∨ lowerSave 1 i.val = 2 := by omega
    rcases hc with h | h | h <;> simp [h]
  simp_rw [hx]
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul, h0, h1, h2]
#print axioms l1_sum
lemma root_sum (f : Nat → Nat) :
    (∑ i : Fin 4096, f (ClaudeWCT.Numerics.TopRoute.pathSave i.val)) = 1024 * f 0 + 2048 * f 1 + 1024 * f 2 := by
  have h0 : (Finset.univ.filter (fun i : Fin 4096 => ClaudeWCT.Numerics.TopRoute.pathSave i.val = 0)).card = 1024 := by decide +kernel
  have h1 : (Finset.univ.filter (fun i : Fin 4096 => ClaudeWCT.Numerics.TopRoute.pathSave i.val = 1)).card = 2048 := by decide +kernel
  have h2 : (Finset.univ.filter (fun i : Fin 4096 => ClaudeWCT.Numerics.TopRoute.pathSave i.val = 2)).card = 1024 := by decide +kernel
  have hx (i : Fin 4096) : f (ClaudeWCT.Numerics.TopRoute.pathSave i.val) =
      (if ClaudeWCT.Numerics.TopRoute.pathSave i.val = 0 then f 0 else 0) +
      (if ClaudeWCT.Numerics.TopRoute.pathSave i.val = 1 then f 1 else 0) +
      (if ClaudeWCT.Numerics.TopRoute.pathSave i.val = 2 then f 2 else 0) := by
    have hb : ClaudeWCT.Numerics.TopRoute.pathSave i.val ≤ 2 := by
      unfold ClaudeWCT.Numerics.TopRoute.pathSave ClaudeWCT.Numerics.TopRoute.pairSave
      split_ifs <;> omega
    have hc : ClaudeWCT.Numerics.TopRoute.pathSave i.val = 0 ∨ ClaudeWCT.Numerics.TopRoute.pathSave i.val = 1 ∨ ClaudeWCT.Numerics.TopRoute.pathSave i.val = 2 := by omega
    rcases hc with h | h | h <;> simp [h]
  simp_rw [hx]
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul, h0, h1, h2]

lemma pair_sum_two (f : Nat → Nat) :
  (∑ i : Fin 64, f (lowerSave 2 i.val)) = 32 * f 0 + 32 * f 1 := by
  have h0 : (Finset.univ.filter (fun i : Fin 64 => lowerSave 2 i.val = 0)).card = 32 := by decide +kernel
  have h1 : (Finset.univ.filter (fun i : Fin 64 => lowerSave 2 i.val = 1)).card = 32 := by decide +kernel
  have hx (i : Fin 64) : f (lowerSave 2 i.val) =
      (if lowerSave 2 i.val = 0 then f 0 else 0) + (if lowerSave 2 i.val = 1 then f 1 else 0) := by
    unfold lowerSave
    split_ifs <;> simp_all
  simp_rw [hx]
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul, h0, h1]

lemma pair_sum (f : Nat → Nat) (lay : Nat) (hlay : lay = 2 ∨ lay = 3) :
    (∑ i : Fin 64, f (lowerSave lay i.val)) = 32 * f 0 + 32 * f 1 := by
  rcases hlay with rfl | rfl <;> simpa [lowerSave] using pair_sum_two f

lemma sum_split (a b : Nat) (hb : 0 < b) (f : Nat → Nat → Nat) :
    (∑ i : Fin (a*b), f (i.val / b) (i.val % b)) =
      ∑ x : Fin a, ∑ y : Fin b, f x.val y.val := by
  rw [← (finProdFinEquiv : Fin a × Fin b ≃ Fin (a*b)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  change f ((y.val+b*x.val)/b) ((y.val+b*x.val)%b) = _
  rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt y.isLt, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
#print axioms root_sum
#print axioms pair_sum
#print axioms sum_split
end SigGolfCandidate.AllRoute
