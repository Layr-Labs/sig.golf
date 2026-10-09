import SigGolfCandidate.ClaudeR3.P8

namespace ClaudeR3.Asm
open Finset Polynomial
set_option maxRecDepth 100000
open ClaudeWCT.Numerics.N600Cap (pairCost pairPoly pairEval card_pairCost_eq range_foldr_eq_sum' eval_pairPoly eval_one_pairPoly)

def J779 : ℕ := 50017003700803880389270367190751792644955136

def capCheck779 : Bool :=
  Nat.beq ((List.range 780).foldr (fun t s => pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 + s) 0) J779

theorem capCheck779_ok : capCheck779 = true := by decide +kernel

theorem mem_capS (cap : ℕ) (c : Coords) : c ∈ capS cap ↔ pairCost c ≤ cap := by
  simp only [capS, mem_filter, mem_univ, true_and]

set_option linter.constructorNameAsVariable false in
theorem card_capS779 : (capS 779).card = J779 := by
  have hB : 0 < 2 ^ 150 := by positivity
  have hcoeff : ∀ i, (pairPoly ^ 9).coeff i < 2 ^ 150 := by
    intro i
    refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
    rw [eval_pow, eval_one_pairPoly]
    norm_num
  have hext : ∀ t, (pairPoly ^ 9).coeff t = pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 := by
    intro t
    rw [← ClaudeWCT.Numerics.eval_div_pow_mod hB t _ hcoeff, eval_pow, eval_pairPoly]
  have hsplit : (capS 779).card = ∑ t ∈ range 780, #{c : Fin 9 → ClaudeWCT.WCT9.Child × ClaudeWCT.WCT9.Rank |
      pairCost c = t} := by
    have hmem : ∀ c ∈ capS 779, pairCost c ∈ range 780 := by
      intro c hc
      rw [mem_capS] at hc
      rw [mem_range]
      omega
    rw [card_eq_sum_card_fiberwise hmem]
    unfold capS
    refine sum_congr rfl fun t ht => ?_
    rw [filter_filter]
    exact congrArg Finset.card (filter_congr fun c _ => ⟨fun h => h.2,
      fun h => ⟨by rw [h]; have h2 := mem_range.mp ht; omega, h⟩⟩)
  have hc := capCheck779_ok
  unfold capCheck779 at hc
  rw [hsplit]
  simp_rw [card_pairCost_eq, hext]
  rw [← range_foldr_eq_sum']
  exact Nat.eq_of_beq_eq_true hc

theorem capS779_nonempty : (capS 779).Nonempty := by
  rw [← card_pos, card_capS779]; unfold J779; norm_num

end ClaudeR3.Asm
