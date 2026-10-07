import SigGolfCandidate.ClaudeWCT.Numerics.CoverW1
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.Numerics.N600Cap
open Finset Polynomial
set_option maxRecDepth 100000
open ClaudeWCT.WCT9 (routineCost routineCosts routineCosts_length jointCap Coord Child Rank childExtra childSave maxChildSave)
def pairCost (c : Fin 9 → Child × Rank) : ℕ := ∑ k, (routineCost (c k).2 + childExtra (c k).1)
def J : ℕ := 91165211245290257558782579115354775751229440
noncomputable def costPoly : ℕ[X] := ∑ r : Fin 600, X ^ routineCost r
noncomputable def pairPoly : ℕ[X] := ∑ p : Child × Rank, X ^ (routineCost p.2 + childExtra p.1)
theorem sum_routineCost {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ r : Fin 600, f (routineCost r) = (routineCosts.map f).sum := by
  have h : ∀ (l : List ℕ) (n : ℕ) (hl : l.length = n),
      ∑ r : Fin n, f (l[r.val]'(by omega)) = (l.map f).sum := by
    intro l n hl
    subst hl
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  exact h routineCosts 600 routineCosts_length
theorem sum_childExtra {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ c : Child, f (childExtra c) = ((List.range 128).map fun c => f (maxChildSave - childSave c)).sum := by
  rw [← List.sum_ofFn]
  congr 1
theorem card_pairCost_eq (t : ℕ) : #{c : Fin 9 → Child × Rank | pairCost c = t} = (pairPoly ^ 9).coeff t := by
  have h := ClaudeWCT.Numerics.card_pi_sum_eq_coeff (fun _ : Fin 9 => (univ : Finset (Child × Rank)))
    (fun p => routineCost p.2 + childExtra p.1) t
  rw [Fintype.piFinset_univ, prod_const, card_univ, Fintype.card_fin] at h
  exact h
theorem pairCost_le (c : Fin 9 → Child × Rank) : pairCost c ≤ 738 := by
  unfold pairCost
  calc ∑ k, (routineCost (c k).2 + childExtra (c k).1) ≤ ∑ _k : Fin 9, 82 :=
        sum_le_sum fun k _ => by
          have h1 := (ClaudeWCT.WCT9.routineCost_bounds (c k).2).2
          have h2 : childExtra (c k).1 ≤ 2 := by unfold childExtra maxChildSave; omega
          omega
    _ = 738 := by simp
def costEval (B : ℕ) : ℕ := (routineCosts.map fun c => B ^ c).sum
def childEval (B : ℕ) : ℕ := ((List.range 128).map fun c => B ^ (maxChildSave - childSave c)).sum
def pairEval (B : ℕ) : ℕ := childEval B * costEval B
theorem eval_costPoly (B : ℕ) : costPoly.eval B = costEval B := by
  rw [costPoly, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact sum_routineCost (fun c => B ^ c)
theorem eval_pairPoly (B : ℕ) : pairPoly.eval B = pairEval B := by
  rw [pairPoly, eval_finsetSum]
  simp only [eval_pow, eval_X]
  rw [Fintype.sum_prod_type]
  simp only [pow_add]
  rw [show (∑ x : Child, ∑ y : Rank, B ^ routineCost y * B ^ childExtra x) =
      (∑ x : Child, B ^ childExtra x) * ∑ y : Rank, B ^ routineCost y by
    rw [Finset.sum_mul]; refine sum_congr rfl fun x _ => ?_; rw [Finset.mul_sum]
    refine sum_congr rfl fun y _ => ?_; ring]
  rw [sum_childExtra (fun e => B ^ e), sum_routineCost (fun c => B ^ c)]
  rfl
theorem pairEval_one : pairEval 1 = 76800 := by decide +kernel
theorem eval_one_pairPoly : pairPoly.eval 1 = 76800 := by
  rw [eval_pairPoly, pairEval_one]
def capCheck : Bool :=
  Nat.beq ((List.range 705).foldr (fun t s => pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 + s) 0) J
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
def capSet : Finset (Coord → Child × Rank) := univ.filter fun c => pairCost c ≤ jointCap
theorem mem_capSet (c : Coord → Child × Rank) : c ∈ capSet ↔ pairCost c ≤ jointCap := by
  simp only [capSet, mem_filter, mem_univ, true_and]
set_option linter.constructorNameAsVariable false in
theorem card_capSet : capSet.card = J := by
  have hB : 0 < 2 ^ 150 := by positivity
  have hcoeff : ∀ i, (pairPoly ^ 9).coeff i < 2 ^ 150 := by
    intro i
    refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
    rw [eval_pow, eval_one_pairPoly]
    norm_num
  have hext : ∀ t, (pairPoly ^ 9).coeff t = pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 := by
    intro t
    rw [← ClaudeWCT.Numerics.eval_div_pow_mod hB t _ hcoeff, eval_pow, eval_pairPoly]
  have hsplit : capSet.card = ∑ t ∈ range 705, #{c : Fin 9 → Child × Rank | pairCost c = t} := by
    have hmem : ∀ c ∈ capSet, pairCost c ∈ range 705 := by
      intro c hc
      rw [mem_capSet] at hc
      rw [mem_range]
      have h707 : ClaudeWCT.WCT9.jointCap = 704 := rfl
      omega
    rw [card_eq_sum_card_fiberwise hmem]
    unfold capSet
    refine sum_congr rfl fun t ht => ?_
    rw [filter_filter]
    exact congrArg Finset.card (filter_congr fun c _ => ⟨fun h => h.2,
      fun h => ⟨by rw [h]; have h2 := mem_range.mp ht; unfold ClaudeWCT.WCT9.jointCap; omega, h⟩⟩)
  have hc := capCheck_ok
  unfold capCheck at hc
  rw [hsplit]
  simp_rw [card_pairCost_eq, hext]
  rw [← range_foldr_eq_sum']
  exact Nat.eq_of_beq_eq_true hc
end ClaudeWCT.Numerics.N600Cap
