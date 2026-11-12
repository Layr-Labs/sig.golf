import SigGolfCandidate.Merge011
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
/-! Stronger current-key credit policy. Kept separate so legacy policy libraries retain their statements. -/
namespace ClaudeWCT.WCT9.Policy75Safe23
open SigGolfCandidate.T3 CanonicalPolicy
def lowerOneThresholds : List Nat := [6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,11,11,11,11,11,14,14,14,16,16]
def lowerTwoThresholds : List Nat := [6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,10,10,10,12,12,12,14,14,16,16,16,18,18]
def lowerThreeFloor (r : Nat) : Nat :=
  if r ≤ 6 then 6 else if r ≤ 9 then 9 else if r = 10 then 11 else r
def lowerFloorMax : Nat := 23
def threshold (stage residual : Nat) : Nat :=
  if stage = 0 then max 18 (residual - 57)
  else if stage = 1 then lowerOneThresholds.getD residual 301
  else if stage = 2 then lowerTwoThresholds.getD residual 301
  else if stage = 3 ∧ residual ≤ 23 then lowerThreeFloor residual
  else 301

theorem threshold_top (residual : Nat) : threshold 0 residual = max 18 (residual - 57) := by
  simp [threshold]
theorem threshold_zero : threshold 1 0 = 6 ∧ threshold 2 0 = 6 ∧ threshold 3 0 = 6 := by decide

theorem lower_one_progress : ∀ r : Fin 58,
    threshold 1 r.val ≤ 19 ∧ r.val - threshold 1 r.val < 42 := by decide +kernel
theorem lower_one_floor_lt : ∀ r : Fin 58, threshold 1 r.val < 17 := by decide +kernel
theorem lower_two_progress : ∀ r : Fin 42,
    threshold 2 r.val ≤ 19 ∧ r.val - threshold 2 r.val < 24 := by decide +kernel
theorem lower_two_floor_le : ∀ r : Fin 42, threshold 2 r.val ≤ 18 := by decide +kernel
theorem lower_three_progress (r : Nat) (hr : r < 24) :
    threshold 3 r = lowerThreeFloor r := by simp [threshold, show r ≤ 23 by omega]
theorem lowerThreeFloor_ge (r : Nat) : r ≤ lowerThreeFloor r := by
  unfold lowerThreeFloor
  split_ifs <;> omega
theorem lowerThreeFloor_le (r : Nat) (hr : r < 24) : lowerThreeFloor r ≤ 23 := by
  unfold lowerThreeFloor
  split_ifs <;> omega

theorem accepted_top_residual_pool (pool : Nat) {low : Bool} {answer : Digest} {digits : List Nat}
    (h : producerDecodeAt 0 (max 18 (pool - 57)) low answer = some digits) :
    nextResidual pool 0 low digits < 58 := by
  have hc := producerDecodeAt_credit h
  have hm := Nat.le_max_right 18 (pool - 57)
  unfold nextResidual
  omega

theorem accepted_one_residual (r : Fin 58) {answer : Digest} {low : Bool} {digits : List Nat}
    (h : producerDecodeAt 1 (threshold 1 r.val) low answer = some digits) :
    nextResidual r.val 1 low digits < 42 := by
  have hc := producerDecodeAt_credit h
  have hp := (lower_one_progress r).2
  unfold nextResidual
  omega

theorem accepted_two_residual (r : Fin 42) {answer : Digest} {low : Bool} {digits : List Nat}
    (h : producerDecodeAt 2 (threshold 2 r.val) low answer = some digits) :
    nextResidual r.val 2 low digits < 24 := by
  have hc := producerDecodeAt_credit h
  have hp := (lower_two_progress r).2
  unfold nextResidual
  omega

theorem accepted_three_residual (r : Fin 24) {answer : Digest} {low : Bool} {digits : List Nat}
    (h : producerDecodeAt 3 (threshold 3 r.val) low answer = some digits) :
    nextResidual r.val 3 low digits = 0 := by
  have hc := producerDecodeAt_credit h
  rw [lower_three_progress r.val r.isLt] at hc
  exact Nat.sub_eq_zero_of_le ((lowerThreeFloor_ge _).trans hc)

#print axioms lower_one_progress
#print axioms lower_two_progress
#print axioms accepted_three_residual
end ClaudeWCT.WCT9.Policy75Safe23
