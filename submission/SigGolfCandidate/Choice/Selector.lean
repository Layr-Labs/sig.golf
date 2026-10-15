import SigGolfCandidate.Choice.Gated
import ToMathlib.Data.BitVec

/-! The exact RV64 selector used in the gated top-half prototype. -/
namespace SigGolfCandidate.Choice.Selector
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] Finset.univ

def group (low : BitVec 128) : BitVec 64 := low.extractLsb' 64 64 >>> 62
def offset (low : BitVec 128) (hint : BitVec 64) : BitVec 64 :=
  (group low * hint) &&& 16
def honestHint (low : BitVec 128) (high : Bool) : BitVec 64 :=
  if high then (if group low = 2 then 8 else 16) else 0
def blocked : Finset (BitVec 128) := Finset.univ.filter fun low => group low = 0

theorem group_toNat (low : BitVec 128) : (group low).toNat = low.toNat / 2 ^ 126 := by
  have hl := low.isLt
  have hdiv : low.toNat / 2 ^ 64 < 2 ^ 64 := by norm_num at *; omega
  simp only [group, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdiv, Nat.div_div_eq_div_mul]
  norm_num

theorem group_cases (low : BitVec 128) :
    group low = 0 ∨ group low = 1 ∨ group low = 2 ∨ group low = 3 := by
  have hl := low.isLt
  have hg := group_toNat low
  have hn : (group low).toNat = 0 ∨ (group low).toNat = 1 ∨
      (group low).toNat = 2 ∨ (group low).toNat = 3 := by norm_num at *; omega
  simp only [← BitVec.toNat_inj]
  exact hn

theorem group_zero_iff (low : BitVec 128) : group low = 0 ↔ low.toNat < 2 ^ 126 := by
  rw [← BitVec.toNat_inj, group_toNat]
  change low.toNat / 2 ^ 126 = 0 ↔ low.toNat < 2 ^ 126
  rw [Nat.div_eq_zero_iff]
  norm_num

theorem mask_cases (x : BitVec 64) : x &&& 16 = 0 ∨ x &&& 16 = 16 := by
  have hm : x.toNat &&& 16 < 2 ^ 5 := Nat.and_lt_two_pow _ (by decide)
  have he : (x &&& 16).toNat = (x.toNat % 32) &&& 16 := by
    change x.toNat &&& 16 = _
    rw [← Nat.mod_eq_of_lt hm, Nat.and_mod_two_pow]
  have hf : ∀ n : Fin 32, n.val &&& 16 = 0 ∨ n.val &&& 16 = 16 := by decide +kernel
  have h := hf ⟨x.toNat % 32, Nat.mod_lt _ (by decide)⟩
  rw [← he] at h
  simp only [← BitVec.toNat_inj]
  exact h

theorem offset_cases (low : BitVec 128) (hint : BitVec 64) :
    offset low hint = 0 ∨ offset low hint = 16 := mask_cases _

/-- The executable selector branches on the hint without arithmetic masking.
Both honest hints (0 and 16) are unchanged; every other hint still selects only
one of the same two permitted halves. -/
def branchOffset (low : BitVec 128) (hint : BitVec 64) : BitVec 64 :=
  if group low = 0 then 0 else if hint = 0 then 0 else 16

theorem branchOffset_cases (low : BitVec 128) (hint : BitVec 64) :
    branchOffset low hint = 0 ∨ branchOffset low hint = 16 := by
  unfold branchOffset
  split_ifs <;> simp

theorem branch_blocked_forces_low (low : BitVec 128) (hint : BitVec 64) (h : low ∈ blocked) :
    branchOffset low hint = 0 := by
  have hg := (Finset.mem_filter.mp h).2
  simp [branchOffset, hg]

theorem branch_honest_high (low : BitVec 128) (h : low ∉ blocked) :
    branchOffset low 16 = 16 := by
  have hn : group low ≠ 0 := by simpa [blocked] using h
  rw [branchOffset, if_neg hn]
  decide +kernel

def branchRead (a : BitVec 128 × BitVec 128) (hint : BitVec 64) : BitVec 128 :=
  if branchOffset a.1 hint = 16 then a.2 else a.1

theorem branchRead_eq_read (a : BitVec 128 × BitVec 128) (hint : BitVec 64) :
    branchRead a hint = Gated.read blocked (decide (hint ≠ 0)) a := by
  have hb : a.1 ∈ blocked ↔ group a.1 = 0 := by simp only [blocked, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hz : (0 : BitVec 64) ≠ 16 := by decide +kernel
  unfold branchRead branchOffset Gated.read
  simp only [hb, decide_eq_true_eq]
  by_cases hg : group a.1 = 0
  · rw [if_pos hg, if_neg hz]
    simp only [hg, not_true_eq_false, and_false, if_false]
  · rw [if_neg hg]
    simp only [hg, not_false_eq_true, and_true]
    by_cases hh : hint = 0 <;> simp [hh]

theorem branchRead_allowed (good : Finset (BitVec 128))
    (a : BitVec 128 × BitVec 128) (hint : BitVec 64) (h : branchRead a hint ∈ good) :
    a ∈ Gated.accepted good blocked := by
  rw [branchRead_eq_read] at h
  exact Gated.read_mem good blocked _ a h

theorem branchRead_canonical (good : Finset (BitVec 128)) (a : BitVec 128 × BitVec 128) :
    branchRead a (if a.1 ∈ good ∨ a.1 ∈ blocked then 0 else 16) =
      Gated.choose good blocked a := by
  rw [branchRead_eq_read]
  by_cases hg : a.1 ∈ good <;> by_cases hb : a.1 ∈ blocked <;>
    simp [Gated.read, Gated.choose, hg, hb]

theorem blocked_forces_low (low : BitVec 128) (hint : BitVec 64) (h : low ∈ blocked) :
    offset low hint = 0 := by
  have hg := (Finset.mem_filter.mp h).2
  simp [offset, hg]

theorem honest_low (low : BitVec 128) : offset low (honestHint low false) = 0 := by
  simp [offset, honestHint]

theorem honest_high (low : BitVec 128) (h : low ∉ blocked) :
    offset low (honestHint low true) = 16 := by
  have hn : group low ≠ 0 := by simpa [blocked] using h
  rcases group_cases low with hg | hg | hg | hg
  · exact absurd hg hn
  all_goals simp only [offset, honestHint, if_true, hg]; decide +kernel

theorem high_is_permitted (low : BitVec 128) (hint : BitVec 64) (h : offset low hint = 16) :
    low ∉ blocked := by
  intro hb
  have he := blocked_forces_low low hint hb
  rw [he] at h
  exact (by decide : (0 : BitVec 64) ≠ 16) h

theorem blocked_card : blocked.card = 2 ^ 126 := by
  have hc : blocked.card = (Finset.range (2 ^ 126)).card := by
    apply Finset.card_bij (fun v _ => v.toNat)
    · intro v hv
      exact Finset.mem_range.mpr ((group_zero_iff v).mp (Finset.mem_filter.mp hv).2)
    · intro a _ b _ h
      exact BitVec.eq_of_toNat_eq h
    · intro n hn
      have hn' := Finset.mem_range.mp hn
      have hb : n < 2 ^ 128 := hn'.trans (by norm_num)
      refine ⟨BitVec.ofNat 128 n, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, (group_zero_iff _).mpr ?_⟩
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] using hn'
      · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  simpa only [Finset.card_range] using hc

theorem accepted_upper (good : Finset (BitVec 128)) :
    (Gated.accepted good blocked).card ≤ good.card * (7 * 2 ^ 126) :=
  Gated.quarter_upper good blocked (2 ^ 126) (by norm_num) blocked_card

theorem accepted_lower (good : Finset (BitVec 128)) :
    good.card * (7 * 2 ^ 126 - good.card) ≤ (Gated.accepted good blocked).card :=
  Gated.quarter_lower good blocked (2 ^ 126) (by norm_num) blocked_card

/-- The witness function may depend on the complete hash answer. -/
theorem arbitrary_witness_card (good : Finset (BitVec 128))
    (hint : BitVec 128 × BitVec 128 → BitVec 64) :
    (Finset.univ.filter fun a => branchRead a (hint a) ∈ good).card ≤
      good.card * (7 * 2 ^ 126) := by
  apply (Finset.card_le_card ?_).trans (accepted_upper good)
  intro a ha
  exact branchRead_allowed good a (hint a) (Finset.mem_filter.mp ha).2

def splitEquiv : BitVec 256 ≃ BitVec 128 × BitVec 128 where
  toFun a := (a.extractLsb' 0 128, a.extractLsb' 128 128)
  invFun a := a.2 ++ a.1
  left_inv _ := BitVec.extractLsb'_append_extractLsb'
  right_inv _ := by simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

theorem arbitrary_hash_witness_card (good : Finset (BitVec 128))
    (hint : BitVec 256 → BitVec 64) :
    (Finset.univ.filter fun a => branchRead (splitEquiv a) (hint a) ∈ good).card ≤
      good.card * (7 * 2 ^ 126) := by
  have he : (Finset.univ.filter fun a => branchRead (splitEquiv a) (hint a) ∈ good).card =
      (Finset.univ.filter fun a => branchRead a (hint (splitEquiv.symm a)) ∈ good).card := by
    apply Finset.card_equiv splitEquiv
    intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  exact he.le.trans (arbitrary_witness_card good (hint ∘ splitEquiv.symm))

end SigGolfCandidate.Choice.Selector

#print axioms SigGolfCandidate.Choice.Selector.offset_cases
#print axioms SigGolfCandidate.Choice.Selector.honest_high
#print axioms SigGolfCandidate.Choice.Selector.blocked_card
#print axioms SigGolfCandidate.Choice.Selector.accepted_upper
#print axioms SigGolfCandidate.Choice.Selector.accepted_lower
#print axioms SigGolfCandidate.Choice.Selector.branchOffset_cases
#print axioms SigGolfCandidate.Choice.Selector.branchRead_allowed
#print axioms SigGolfCandidate.Choice.Selector.branchRead_canonical
#print axioms SigGolfCandidate.Choice.Selector.arbitrary_hash_witness_card
