import SigGolfCandidate.TopRouteNumerics
open scoped BigOperators
open Finset
namespace ClaudeWCT.Numerics.TopRoute
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000

def pairSave (leaf : Nat) : Nat := if leaf % 4 = 1 ∨ leaf % 4 = 2 then 1 else 0
def pathSave (leaf : Nat) : Nat := pairSave leaf + pairSave (leaf / 64)
def rootPool (leaf : Nat) : Nat := 73 - pathSave leaf

theorem sum_root_nat (f : Nat → Nat) :
    (∑ i : Fin (2^31), f (i.val / 2^19)) =
      2^19 * ∑ leaf : Fin 4096, f leaf.val := by
  change (∑ i : Fin (4096*524288), f (i.val / 524288)) =
    524288 * ∑ leaf : Fin 4096, f leaf.val
  rw [← (finProdFinEquiv : Fin 4096 × Fin 524288 ≃ Fin (4096*524288)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hdiv (leaf : Fin 4096) (suffix : Fin 524288) :
      (finProdFinEquiv (leaf,suffix)).val / 524288 = leaf.val := by
    change (suffix.val + 524288 * leaf.val) / 524288 = leaf.val
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt suffix.isLt, Nat.zero_add]
  simp_rw [hdiv]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.mul_sum]

theorem leaf_initial_sum_checked :
    (∑ leaf : Fin 4096, initialFor (rootPool leaf.val)) ≤ 4096 * meanInitial := by
  decide +kernel

theorem index_initial_sum :
    (∑ i : Fin (2^31), initialFor (rootPool (i.val / 2^19))) ≤ 2^31 * meanInitial := by
  rw [sum_root_nat (fun n => initialFor (rootPool n))]
  calc
    2^19 * (∑ leaf : Fin 4096, initialFor (rootPool leaf.val)) ≤ 2^19 * (4096 * meanInitial) := Nat.mul_le_mul_left _ leaf_initial_sum_checked
    _ = 2^31 * meanInitial := by rw [← Nat.mul_assoc]; rfl

#print axioms sum_root_nat
#print axioms leaf_initial_sum_checked
#print axioms index_initial_sum
end ClaudeWCT.Numerics.TopRoute
