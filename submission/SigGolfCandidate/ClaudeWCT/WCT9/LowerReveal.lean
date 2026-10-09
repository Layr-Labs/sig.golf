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

/-! ### Revealed seeds of a top leaf (campaign T8D, TOP2 NF17)

The top WOTS has 51 radix-5 chains (digits `≤ 4`) and 3 radix-8 chains (digits `≤ 7`), capacity `51·4 + 3·7 = 225`.
A zero digit loses at least `4` from the capacity, so a top codeword with digit sum `T` has at most `(225 - T)/4`
zero digits: `≤ 20` for `T ≥ 142` (`top_zero_count_le`). With 24 coefficients per top leaf family every unrevealed
top seed keeps `24 - 20 ≥ 3` degrees of freedom (`|R| + 3 ≤ 24`). The dummy top codeword has no zero digit. -/

/-- Digits bounded entrywise by `ms`, every bound `≥ 4`: the sum plus `4` per zero digit is at most `ms.sum`. -/
theorem sum_add_four_zero_le : ∀ (ds ms : List Nat), ds.length = ms.length →
    (∀ i, ds.getD i 0 ≤ ms.getD i 0) → (∀ m ∈ ms, 4 ≤ m) →
    ds.sum + 4 * (ds.filter (· = 0)).length ≤ ms.sum
  | [], [], _, _, _ => by simp
  | d :: ds, m :: ms, hl, hle, hm => by
      have ih := sum_add_four_zero_le ds ms (by simpa using hl) (fun i => by simpa using hle (i + 1))
        (fun x hx => hm x (List.mem_cons_of_mem m hx))
      have hd : d ≤ m := by simpa using hle 0
      have h4 : 4 ≤ m := hm m List.mem_cons_self
      by_cases h0 : d = 0
      · subst h0; simp only [List.filter_cons, decide_true, if_true, List.length_cons, List.sum_cons]; omega
      · simp only [List.filter_cons, h0, decide_false, Bool.false_eq_true, if_false, List.sum_cons]; omega
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem top_capacity : ((List.range (chainCount 0)).map (maxDigit 0)).sum = 225 := by decide

theorem top_maxDigit_ge (i : Nat) : 4 ≤ maxDigit 0 i := by unfold maxDigit; split_ifs <;> omega

/-- **At most 20 revealed seeds per top leaf** (for top targets `≥ 142`). -/
theorem top_zero_count_le (htarget : 142 ≤ target 0) {value : Digest} {digits : List Nat}
    (h : decode 0 value = some digits) : (digits.filter (· = 0)).length ≤ 20 := by
  obtain ⟨hlen, hsum⟩ := decode_length_sum h
  have key := sum_add_four_zero_le digits ((List.range (chainCount 0)).map (maxDigit 0)) (by simp [hlen])
    (fun i => by
      by_cases hi : i < chainCount 0
      · have hm : ((List.range (chainCount 0)).map (maxDigit 0)).getD i 0 = maxDigit 0 i := by
          rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
        rw [hm]; exact decode_digit_max h i hi
      · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _)
    (by
      intro m hm
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hm
      exact top_maxDigit_ge i)
  rw [top_capacity] at key
  omega

/-- The current top target satisfies the hypothesis of `top_zero_count_le`. -/
theorem top_target_ge : 142 ≤ target 0 := by decide

/-- The dummy top codeword has no zero digit. -/
theorem dummyTop_zero : (dummyTop.filter (· = 0)).length = 0 := by decide

end ClaudeWCT.WCT9
