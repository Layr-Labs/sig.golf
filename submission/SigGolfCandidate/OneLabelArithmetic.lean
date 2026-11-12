import Mathlib.Data.BitVec
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.OneLabelArithmetic
/-- Remap root label one without introducing a data-dependent branch. -/
def arithmetic (x : BitVec 64) : BitVec 64 :=
  x + ((0#64-(if BitVec.ult (x+18446744073709551615#64) 1#64 then 1#64 else 0#64)) &&& 856063#64)
 theorem arithmetic_eq (x : BitVec 64) : arithmetic x = if x=1#64 then 856064#64 else x := by
  have hz : x+18446744073709551615#64=0#64 ↔ x=1#64 := by
    have hk : 18446744073709551615#64 = -(1#64) := by decide
    rw [hk,←BitVec.sub_eq_add_neg,BitVec.sub_eq_iff_eq_add]
    rfl
  by_cases h:x=1#64
  · subst x;decide
  · simp [arithmetic,BitVec.ult_eq_decide_lt,BitVec.lt_one_iff (by decide : 0<64),hz,h]
 theorem arithmetic_seven (x : BitVec 64) : arithmetic x = 7#64 ↔ x = 7#64 := by
  rw [arithmetic_eq]
  split_ifs with h
  · subst x;decide
  · rfl
end SigGolfCandidate.T3M.OneLabelArithmetic
