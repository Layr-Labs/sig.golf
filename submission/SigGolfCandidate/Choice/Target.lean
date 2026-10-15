import SigGolfCandidate.Choice.Probability

/-! The residual probe must test every permitted witness opening. -/
namespace ClaudeWCT.WCT9
open SigGolfCandidate.T3 SigGolfCandidate.Choice
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def encodingTarget (lay : Layer) (target : Digest) (answer : HashOutput) : Digest :=
  if lay = 0 then
    if answer.extractLsb' 0 128 = target ∨ Selector.group (answer.extractLsb' 0 128) = 0
      then answer.extractLsb' 0 128 else answer.extractLsb' 128 128
  else encodingAnswer lay answer

theorem verificationAnswer_top_exists_iff (answer : HashOutput) (target : Digest) :
    (∃ hint : BitVec 64, verificationAnswer 0 hint answer = target) ↔
      answer.extractLsb' 0 128 = target ∨
        (Selector.group (answer.extractLsb' 0 128) ≠ 0 ∧ answer.extractLsb' 128 128 = target) := by
  constructor
  · rintro ⟨hint, hh⟩
    change (if (if Selector.group (answer.extractLsb' 0 128) = 0 then (0 : BitVec 64) else if hint = 0 then 0 else 16) = 16
      then answer.extractLsb' 128 128 else answer.extractLsb' 0 128) = target at hh
    by_cases hg : Selector.group (answer.extractLsb' 0 128) = 0
    · rw [if_pos hg, if_neg (by decide : (0 : BitVec 64) ≠ 16)] at hh
      exact Or.inl hh
    · rw [if_neg hg] at hh
      by_cases hz : hint = 0
      · simp only [if_pos hz, if_neg (by decide : (0 : BitVec 64) ≠ 16)] at hh
        exact Or.inl hh
      · simp only [if_neg hz, if_pos rfl] at hh
        exact Or.inr ⟨hg, hh⟩
  · rintro (hl | ⟨hg, hh⟩)
    · refine ⟨0, ?_⟩
      change (if (if Selector.group (answer.extractLsb' 0 128) = 0 then (0 : BitVec 64) else if (0 : BitVec 64) = 0 then 0 else 16) = 16
        then answer.extractLsb' 128 128 else answer.extractLsb' 0 128) = target
      simp only [ite_true, ite_self, if_neg (by decide : (0 : BitVec 64) ≠ 16)]
      exact hl
    · refine ⟨16, ?_⟩
      change (if (if Selector.group (answer.extractLsb' 0 128) = 0 then (0 : BitVec 64) else if (16 : BitVec 64) = 0 then 0 else 16) = 16
        then answer.extractLsb' 128 128 else answer.extractLsb' 0 128) = target
      rw [if_neg hg, if_neg (by decide : (16 : BitVec 64) ≠ 0), if_pos rfl]
      exact hh

theorem verificationAnswer_exists_iff_target (lay : Layer) (answer : HashOutput) (target : Digest) :
    (∃ hint : BitVec 64, verificationAnswer lay hint answer = target) ↔
      encodingTarget lay target answer = target := by
  by_cases hl : lay = 0
  · subst lay
    rw [verificationAnswer_top_exists_iff]
    by_cases ht : answer.extractLsb' 0 128 = target <;>
      by_cases hg : Selector.group (answer.extractLsb' 0 128) = 0 <;>
      simp only [encodingTarget, if_pos rfl, ht, hg, not_true_eq_false, not_false_eq_true, or_true, or_false,
        true_or, false_or, and_true, and_false, true_and, false_and, if_true, if_false] <;> simp_all
  · simp only [verificationAnswer_lower lay hl, exists_const, encodingTarget, if_neg hl]

theorem encodingCanDecode_iff_target (lay : Layer) (answer : HashOutput)
    (target : Digest) (digits : List Nat) (href : decode lay target = some digits) :
    encodingCanDecode lay answer digits ↔ encodingTarget lay target answer = target := by
  rw [← verificationAnswer_exists_iff_target]
  constructor
  · rintro ⟨hint, hh⟩
    exact ⟨hint, decode_some_injective hh href⟩
  · rintro ⟨hint, hh⟩
    exact ⟨hint, hh ▸ href⟩

end ClaudeWCT.WCT9

#print axioms ClaudeWCT.WCT9.verificationAnswer_exists_iff_target
#print axioms ClaudeWCT.WCT9.encodingCanDecode_iff_target
