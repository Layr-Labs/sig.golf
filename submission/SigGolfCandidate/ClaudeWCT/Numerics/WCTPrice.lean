import SigGolfCandidate.ClaudeWCT.Numerics.WCTEnvelope
import SigGolfCandidate.ClaudeWCT.Bank.WCTHonest

namespace ClaudeWCT.Numerics.WCTPrice
open Finset ENNReal
open ClaudeWCT.Numerics.Law (lawAvg marked)
open SphincsSecurity.Concrete (uniformWordAverage)
open ClaudeWCT.Bank.WCT (WProposal price ExcessBound)
open ClaudeWCT.WCT9 (wordDigit Coord Child Rank)
open ClaudeWCT.Numerics.WCTEnvelope
theorem theta_eq : SigGolfCandidate.T3.Security.CaseC.theta = 63 / 64 := rfl
theorem price_fun_eq : price = N600.priceN wordDigit := funext price_eq
section Window
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
include hT1 hT2
theorem wct_price_mean_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T price ≤ 3269 / 10000 := by
  rw [price_fun_eq]
  exact N600.law_price_mean_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit hlaw
theorem wct_price_excess_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (fun W : List WProposal => price W - 63 / 64) ≤
      15847 / 100000000 := by
  rw [price_fun_eq]
  exact N600.law_price_excess_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit w2Table_wordDigit hlaw
theorem wct_near_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (N600.nearPriceN (C := Child) wordDigit) ≤ 131 - 1 / 16 :=
  (N600.law_nearPrice_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit wfTable_wordDigit hlaw).trans
    N600.near_le_sub
theorem wct_price_mean_bound_window : uniformWordAverage T price ≤ 3269 / 10000 := by
  rw [price_fun_eq]
  exact N600.uniform_price_mean_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit
theorem wct_price_mean_bound_window' : uniformWordAverage T price ≤ 37 / 64 := by
  refine (wct_price_mean_bound_window hT1 hT2).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
theorem wct_excessBound_window : ExcessBound T (15847 / 100000000) :=
  ClaudeWCT.Bank.WCT.excessBound_of_honest (wct_price_excess_law hT1 hT2 N600Cap.lawOK_honest)
end Window
abbrev wctHorizon : ℕ := SigGolfCandidate.T3.BPORS.Numeric.proposalLength
theorem wctHorizon_eq : wctHorizon = 2 ^ 32 + 2 ^ 23 := by
  unfold wctHorizon SigGolfCandidate.T3.BPORS.Numeric.proposalLength
  norm_num
theorem wctHorizon_ge : 2 ^ 32 ≤ wctHorizon := by rw [wctHorizon_eq]; omega
theorem wctHorizon_le : wctHorizon ≤ 2 ^ 32 + 2 ^ 23 := wctHorizon_eq.le
theorem wct_excessBound_forall :
    ∀ T : ℕ, 2 ^ 32 ≤ T → T ≤ 2 ^ 32 + 2 ^ 23 → ExcessBound T (15847 / 100000000) :=
  fun _ h1 h2 => wct_excessBound_window h1 h2
theorem wct_excessBound : ExcessBound wctHorizon (15847 / 100000000) :=
  wct_excessBound_window wctHorizon_ge wctHorizon_le
theorem wct_excessBound_2_32 : ExcessBound (2 ^ 32) (15847 / 100000000) :=
  wct_excessBound_window le_rfl (by norm_num)
theorem wct_excess_honest_2_32 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32)
      (fun W : List WProposal => price W - 63 / 64) ≤ 15847 / 100000000 :=
  wct_price_excess_law le_rfl (by norm_num) N600Cap.lawOK_honest
theorem wct_excess_honest :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) wctHorizon
      (fun W : List WProposal => price W - 63 / 64) ≤ 15847 / 100000000 :=
  wct_price_excess_law wctHorizon_ge wctHorizon_le N600Cap.lawOK_honest
theorem wct_near_honest_2_32 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32) (N600.nearPriceN (C := Child) wordDigit) ≤
      131 - 1 / 16 :=
  wct_near_law le_rfl (by norm_num) N600Cap.lawOK_honest
theorem wct_near_honest :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) wctHorizon (N600.nearPriceN (C := Child) wordDigit) ≤
      131 - 1 / 16 :=
  wct_near_law wctHorizon_ge wctHorizon_le N600Cap.lawOK_honest
end ClaudeWCT.Numerics.WCTPrice
