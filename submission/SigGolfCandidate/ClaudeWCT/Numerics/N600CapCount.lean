import SigGolfCandidate.ClaudeWCT.Numerics.CoverW1
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.Numerics.N600Cap
open Finset Polynomial
set_option maxRecDepth 100000
open ClaudeWCT.WCT9 (routineCost routineCosts routineCosts_length jointCap Coord Child Rank)
def rankCost (r : Fin 9 → Fin 600) : ℕ := ∑ k, routineCost (r k)
def capRanks : Finset (Fin 9 → Fin 600) := univ.filter fun r => rankCost r ≤ jointCap
theorem mem_capRanks (r : Fin 9 → Fin 600) : r ∈ capRanks ↔ rankCost r ≤ jointCap := by
  simp only [capRanks, mem_filter, mem_univ, true_and]
def J : ℕ := 9919426655269015159460024
noncomputable def costPoly : ℕ[X] := ∑ r : Fin 600, X ^ routineCost r
theorem sum_routineCost {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ r : Fin 600, f (routineCost r) = (routineCosts.map f).sum := by
  have h : ∀ (l : List ℕ) (n : ℕ) (hl : l.length = n),
      ∑ r : Fin n, f (l[r.val]'(by omega)) = (l.map f).sum := by
    intro l n hl
    subst hl
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  exact h routineCosts 600 routineCosts_length
theorem card_rankCost_eq (t : ℕ) : #{r : Fin 9 → Fin 600 | rankCost r = t} = (costPoly ^ 9).coeff t := by
  have h := ClaudeWCT.Numerics.card_pi_sum_eq_coeff (fun _ : Fin 9 => (univ : Finset (Fin 600))) routineCost t
  rw [Fintype.piFinset_univ, prod_const, card_univ, Fintype.card_fin] at h
  exact h
theorem rankCost_le (r : Fin 9 → Fin 600) : rankCost r ≤ 720 := by
  unfold rankCost
  calc ∑ k, routineCost (r k) ≤ ∑ _k : Fin 9, 80 := sum_le_sum fun k _ => (ClaudeWCT.WCT9.routineCost_bounds _).2
    _ = 720 := by simp
def costEval (B : ℕ) : ℕ := (routineCosts.map fun c => B ^ c).sum
theorem eval_costPoly (B : ℕ) : costPoly.eval B = costEval B := by
  rw [costPoly, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact sum_routineCost (fun c => B ^ c)
theorem costEval_one : costEval 1 = 600 := by decide +kernel
theorem eval_one_costPoly : costPoly.eval 1 = 600 := by
  rw [eval_costPoly, costEval_one]
def capCheck : Bool :=
  Nat.beq ((List.range 701).foldr (fun t s => costEval (2 ^ 100) ^ 9 / (2 ^ 100) ^ t % 2 ^ 100 + s) 0) J
theorem capCheck_ok : capCheck = true := by decide +kernel
theorem range_foldr_eq_sum' (h : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldr (fun r s => h r + s) 0 = ∑ r ∈ Finset.range n, h r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
    have hshift : ∀ (l : List ℕ) (c : ℕ), l.foldr (fun r s => h r + s) c = l.foldr (fun r s => h r + s) 0 + c := by
      intro l c
      induction l with
      | nil => simp
      | cons a l ihl => simp only [List.foldr_cons, ihl]; omega
    rw [hshift, ih]
theorem card_capRanks : capRanks.card = J := by
  have hB : 0 < 2 ^ 100 := by positivity
  have hcoeff : ∀ i, (costPoly ^ 9).coeff i < 2 ^ 100 := by
    intro i
    refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
    rw [eval_pow, eval_one_costPoly]
    norm_num
  have hext : ∀ t, (costPoly ^ 9).coeff t = costEval (2 ^ 100) ^ 9 / (2 ^ 100) ^ t % 2 ^ 100 := by
    intro t
    rw [← ClaudeWCT.Numerics.eval_div_pow_mod hB t _ hcoeff, eval_pow, eval_costPoly]
  have hsplit : capRanks.card = ∑ t ∈ range 701, #{r : Fin 9 → Fin 600 | rankCost r = t} := by
    rw [card_eq_sum_card_fiberwise (f := rankCost) (t := range 701)
      (fun r hr => mem_range.mpr (Nat.lt_succ_of_le ((mem_capRanks r).mp hr)))]
    unfold capRanks
    refine sum_congr rfl fun t ht => ?_
    rw [filter_filter]
    exact congrArg Finset.card (filter_congr fun r _ => ⟨fun h => h.2,
      fun h => ⟨by rw [h]; exact (Nat.le_of_lt_succ (mem_range.mp ht) : t ≤ 700), h⟩⟩)
  have hc := capCheck_ok
  unfold capCheck at hc
  rw [hsplit]
  simp_rw [card_rankCost_eq, hext]
  rw [← range_foldr_eq_sum']
  exact Nat.eq_of_beq_eq_true hc
def capSet : Finset (Coord → Child × Rank) := univ.filter fun c => rankCost (fun k => (c k).2) ≤ jointCap
theorem mem_capSet (c : Coord → Child × Rank) : c ∈ capSet ↔ rankCost (fun k => (c k).2) ≤ jointCap := by
  simp only [capSet, mem_filter, mem_univ, true_and]
theorem card_capSet : capSet.card = 128 ^ 9 * J := by
  have hprod : capSet.card = (univ ×ˢ capRanks : Finset ((Coord → Child) × (Coord → Rank))).card := by
    refine Finset.card_equiv (Equiv.arrowProdEquivProdArrow Coord (fun _ => Child) (fun _ => Rank)) fun c => ?_
    rw [mem_capSet, mem_product, mem_capRanks]
    simp only [mem_univ, true_and]
    exact Iff.rfl
  rw [hprod, card_product, card_capRanks, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
end ClaudeWCT.Numerics.N600Cap
