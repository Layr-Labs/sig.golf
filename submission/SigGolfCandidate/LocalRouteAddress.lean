import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace ClaudeWCT.WCT9.CanonicalPolicy

/-- Layer-1 path transitions: bit `k` is set when leaf bits `k` and `k+1` differ (`k < 6`). -/
def l1Diff (leaf : Nat) : Nat := ((leaf % 128) ^^^ ((leaf % 128) / 2)) % 64

/-- L1 replan: a layer-1 copy omits one `addi a2` for its highest differing transition and one more for
transition 0 when it differs and some transition `≥ 2` differs. -/
def lowerPathSave (lay leaf : Nat) : Nat :=
  if lay=1 then (if l1Diff leaf = 0 then 0 else 1) + (if l1Diff leaf % 2 = 1 ∧ 4 ≤ l1Diff leaf then 1 else 0)
  else if (lay=2 ∨ lay=3) ∧ (leaf%4=1 ∨ leaf%4=2) then 1 else 0

theorem lowerPathSave_le_two (lay leaf : Nat) : lowerPathSave lay leaf ≤ 2 := by
  unfold lowerPathSave
  split_ifs <;> omega

theorem lowerPathSave_le_one_of (lay leaf : Nat) (h : lay ≠ 1) : lowerPathSave lay leaf ≤ 1 := by
  unfold lowerPathSave
  split_ifs <;> omega

theorem l1Diff_mod128 (a b : Nat) (h : a%128=b%128) : l1Diff a = l1Diff b := by
  unfold l1Diff; rw [h]

theorem lowerPathSave_mod128 (lay a b : Nat) (h : a%128=b%128) :
    lowerPathSave lay a = lowerPathSave lay b := by
  have h4 : a%4=b%4 := by omega
  unfold lowerPathSave
  simp only [l1Diff_mod128 a b h,h4]

theorem lowerPathSave_mod8_of (lay a b : Nat) (hlay : lay ≠ 1) (h : a%8=b%8) :
    lowerPathSave lay a = lowerPathSave lay b := by
  have h4 : a%4=b%4 := by omega
  unfold lowerPathSave
  simp only [hlay,if_false,h4]

theorem lowerPathSave_top (leaf : Nat) : lowerPathSave 0 leaf=0 := by simp [lowerPathSave]
#print axioms lowerPathSave_mod128

/-- Gate a (at most two-credit) increment so it cannot wrap a bounded machine word. -/
def guardedCredit (r c saved : Nat) : Nat := c + if c<r then saved else 0

theorem guardedCredit_lt (r c saved bound : Nat) (hr : r+2≤bound) (hc : c<bound) (hs : saved≤2) :
    guardedCredit r c saved<bound := by
  unfold guardedCredit
  split_ifs <;> omega

theorem residual_guardedCredit (r c saved : Nat) :
    r-guardedCredit r c saved = r-c-saved := by
  unfold guardedCredit
  split_ifs <;> omega
#print axioms residual_guardedCredit
end ClaudeWCT.WCT9.CanonicalPolicy
