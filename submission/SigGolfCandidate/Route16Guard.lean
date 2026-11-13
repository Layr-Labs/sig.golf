import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace SigGolfCandidate.Route16Guard
def pairSave (leaf : Nat) : Nat := if leaf % 4 = 1 ∨ leaf % 4 = 2 then 1 else 0
def pathSave (leaf : Nat) : Nat := pairSave leaf + pairSave (leaf / 64)
def floor (_leaf : Nat) : Nat := 16
def guardWord (_leaf : Nat) : BitVec 64 := 16
def words : List (BitVec 32) := [0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x01000e93]
theorem guard_checked : ∀ n : Fin 4096, guardWord n.val = BitVec.ofNat 64 (floor n.val) := by intro n;rfl
theorem pathSave_le_two (leaf : Nat) : pathSave leaf ≤ 2 := by unfold pathSave pairSave;split_ifs <;> omega
theorem floor_eq_threshold (leaf : Nat) : floor leaf = max 16 ((73-pathSave leaf)-57) := by unfold floor;omega
end SigGolfCandidate.Route16Guard
