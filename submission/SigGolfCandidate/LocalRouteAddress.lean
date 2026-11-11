import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace ClaudeWCT.WCT9.CanonicalPolicy

def lowerPathSave (lay leaf : Nat) : Nat :=
  if lay=1 then (46 / 2^(leaf%8))%2
  else if (lay=2 ∨ lay=3) ∧ (leaf%4=1 ∨ leaf%4=2) then 1 else 0

theorem lowerPathSave_le_one (lay leaf : Nat) : lowerPathSave lay leaf ≤ 1 := by
  unfold lowerPathSave
  split_ifs
  · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  all_goals omega

theorem lowerPathSave_mod8 (lay a b : Nat) (h : a%8=b%8) :
    lowerPathSave lay a = lowerPathSave lay b := by
  have h4 : a%4=b%4 := by omega
  unfold lowerPathSave
  simp only [h,h4]

theorem lowerPathSave_top (leaf : Nat) : lowerPathSave 0 leaf=0 := by simp [lowerPathSave]
#print axioms lowerPathSave_mod8

/-- Gate a one-credit increment so it cannot wrap a bounded machine word. -/
def guardedCredit (r c saved : Nat) : Nat := c + if c<r then saved else 0

theorem guardedCredit_lt (r c saved bound : Nat) (hr : r<bound) (hc : c<bound) (hs : saved≤1) :
    guardedCredit r c saved<bound := by
  unfold guardedCredit
  split_ifs <;> omega

theorem residual_guardedCredit (r c saved : Nat) :
    r-guardedCredit r c saved = r-c-saved := by
  unfold guardedCredit
  split_ifs <;> omega
#print axioms residual_guardedCredit
end ClaudeWCT.WCT9.CanonicalPolicy
