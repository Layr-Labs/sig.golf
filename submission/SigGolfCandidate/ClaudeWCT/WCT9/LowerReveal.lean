import SigGolfCandidate.ClaudeWCT.WCT9.Cost

/-!
# Revealed seeds of a lower leaf (campaign X1, stage B)

A lower WOTS signature reveals the seed of chain `i` exactly when its digit is `0`. Lower digits are `≤ 7` and sum
to `target lay`, so for `target lay ≥ 197` at most 14 of the 43 digits are zero (`lower_zero_count_le`): with
17 coefficients per leaf family, every unrevealed seed keeps `17 - 14 = 3` degrees of freedom, which is what the
side-channel bound (`ClaudeWCT.Arith.SideChannel.family_side_channel`, `|R| + 3 ≤ 17`) needs. With
`target ≤ 196` the bound becomes 15 and the margin is lost (DESIGN-A-SEC §3, attack A1).
-/

namespace ClaudeWCT.WCT9
open SigGolfCandidate.T3 SigGolfCandidate.T3.Cost

/-- A list of digits `≤ 7` sums to at most `7` times the number of its nonzero entries. -/
theorem sum_le_seven_mul_nonzero (ds : List Nat) (h : ∀ d ∈ ds, d ≤ 7) :
    ds.sum ≤ 7 * (ds.length - (ds.filter (· = 0)).length) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd := h d List.mem_cons_self
      have ih' := ih fun x hx => h x (List.mem_cons_of_mem d hx)
      have hle : (ds.filter (· = 0)).length ≤ ds.length := List.length_filter_le _ _
      by_cases h0 : d = 0
      · subst h0
        have e : ((0 :: ds).filter (· = 0)).length = (ds.filter (· = 0)).length + 1 := by
          simp [List.filter_cons]
        rw [e, List.sum_cons, List.length_cons]
        omega
      · have e : ((d :: ds).filter (· = 0)).length = (ds.filter (· = 0)).length := by
          simp [List.filter_cons, h0]
        rw [e, List.sum_cons, List.length_cons]
        omega

/-- **At most 14 revealed seeds per lower leaf** (for lower targets `≥ 197`). -/
theorem lower_zero_count_le {lay : Layer} (hlay : lay ≠ 0) (htarget : 197 ≤ target lay) {value : Digest}
    {digits : List Nat} (h : decode lay value = some digits) : (digits.filter (· = 0)).length ≤ 14 := by
  obtain ⟨hlen, hsum⟩ := decode_length_sum h
  have hcc : chainCount lay = 43 := Cost.chainCount_lower hlay
  have hmax : ∀ d ∈ digits, d ≤ 7 := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    have := decode_digit_max h i (by omega)
    rw [List.getD_eq_getElem _ _ hi, Cost.maxDigit_lower hlay] at this
    exact this
  have hs := sum_le_seven_mul_nonzero digits hmax
  have hle : (digits.filter (· = 0)).length ≤ digits.length := List.length_filter_le _ _
  omega

/-- The current lower targets satisfy the hypothesis of `lower_zero_count_le`. -/
theorem lower_target_ge (lay : Layer) (hlay : lay ≠ 0) : 197 ≤ target lay := by
  revert hlay; fin_cases lay <;> decide

end ClaudeWCT.WCT9
