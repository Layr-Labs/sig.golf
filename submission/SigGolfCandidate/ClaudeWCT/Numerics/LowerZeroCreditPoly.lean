import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace ClaudeWCT.Numerics.LowerZeroCreditPoly
open Finset Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The checksum-inclusive count's payload-zero marker. Kept standalone so the
box can isolate polynomial transport from the expensive legacy dependencies. -/
def wtZ (a : ℕ) : ℕ := 64*a + (if a=6 then 1 else 0) + 32768*(if a=0 then 1 else 0)
noncomputable def basePolyZ : ℕ[X] := ∑ b : Fin 8, X ^ wtZ b.val
noncomputable def nonzeroPolyZ : ℕ[X] := ∑ b : Fin 7, X ^ wtZ (b.val+1)
def nonzeroEvalZ (B : ℕ) : ℕ := B^64+B^128+B^192+B^256+B^320+B^385+B^448

theorem basePolyZ_split : basePolyZ = X^32768 + nonzeroPolyZ := by
  unfold basePolyZ
  rw [Fin.sum_univ_succ]
  apply congrArg₂ (fun p q : ℕ[X] => p + q)
  · apply congrArg (fun n : ℕ => (X : ℕ[X]) ^ n)
    norm_num [wtZ]
  · unfold nonzeroPolyZ
    apply sum_congr rfl
    intro b _
    apply congrArg (fun n : ℕ => (X : ℕ[X]) ^ n)
    rfl

theorem eval_nonzeroPolyZ (B : ℕ) : nonzeroPolyZ.eval B = nonzeroEvalZ B := by
  simp [nonzeroPolyZ, nonzeroEvalZ, Fin.sum_univ_succ, wtZ, Nat.add_assoc]

theorem nonzeroPolyZ_degree : nonzeroPolyZ.natDegree ≤ 448 := by
  apply natDegree_sum_le_of_forall_le
  intro b _
  fin_cases b <;> norm_num [wtZ]

theorem coeff_splitZ {z R : ℕ} (hz : z ≤ 42) (hR : R < 32768) :
    (basePolyZ^42).coeff (32768*z+R) = Nat.choose 42 z * (nonzeroPolyZ^(42-z)).coeff R := by
  rw [basePolyZ_split, add_pow, finsetSum_coeff]
  rw [Finset.sum_eq_single z]
  · rw [coeff_mul_natCast, ← pow_mul, coeff_X_pow_mul']
    simp [Nat.mul_comm]
  · intro i hi hne
    simp only [mem_range] at hi
    rw [coeff_mul_natCast, ← pow_mul, coeff_X_pow_mul']
    by_cases hiz : i ≤ z
    · rw [if_pos (by omega)]
      have hdeg : (nonzeroPolyZ^(42-i)).natDegree ≤ (42-i)*448 :=
        natDegree_pow_le.trans (Nat.mul_le_mul_left _ nonzeroPolyZ_degree)
      rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by omega)), zero_mul]
    · rw [if_neg (by omega), zero_mul]
  · intro h
    exact (h (mem_range.mpr (by omega))).elim

#print axioms basePolyZ_split
#print axioms eval_nonzeroPolyZ
#print axioms nonzeroPolyZ_degree
#print axioms coeff_splitZ
end ClaudeWCT.Numerics.LowerZeroCreditPoly
