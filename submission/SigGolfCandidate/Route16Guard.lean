import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace SigGolfCandidate.Route16Guard
def pairSave (leaf : Nat) : Nat := if leaf % 4 = 1 ∨ leaf % 4 = 2 then 1 else 0
def pathSave (leaf : Nat) : Nat := pairSave leaf + pairSave (leaf / 64)
def floor (leaf : Nat) : Nat := if pathSave leaf = 0 then 17 else 16
def guardWord (leaf : Nat) : BitVec 64 :=
  let x := BitVec.ofNat 64 leaf
  16 + if ((x ^^^ x >>> 1) &&& 65).ult 1 = true then 1 else 0
def words : List (BitVec 32) := [0x195e93,0x12eceb3,0x41efe93,0x1ebe93,0x10e8e93,0x13,0x13,0x13]
def chk : Nat → Bool
  | 0 => true
  | k+1 => (guardWord k == BitVec.ofNat 64 (floor k)) && chk k
theorem chk_spec : ∀ n, chk n = true → ∀ k < n, guardWord k = BitVec.ofNat 64 (floor k)
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n+1, h, k, hk => by
    simp only [chk, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact chk_spec n h.2 k hk
    · exact h.1
set_option maxRecDepth 100000 in
theorem chk_4096 : chk 4096 = true := by decide +kernel
theorem guard_checked : ∀ n : Fin 4096, guardWord n.val = BitVec.ofNat 64 (floor n.val) :=
  fun n => chk_spec 4096 chk_4096 n.val n.isLt
theorem pathSave_le_two (leaf : Nat) : pathSave leaf ≤ 2 := by unfold pathSave pairSave;split_ifs <;> omega
theorem floor_eq_threshold (leaf : Nat) : floor leaf = max 16 ((74-pathSave leaf)-57) := by
  have := pathSave_le_two leaf
  unfold floor;split_ifs <;> omega
end SigGolfCandidate.Route16Guard
