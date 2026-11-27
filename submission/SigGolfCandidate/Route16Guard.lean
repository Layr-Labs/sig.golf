import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace SigGolfCandidate.Route16Guard
def pairSave (leaf : Nat) : Nat := if leaf % 4 = 1 ∨ leaf % 4 = 2 then 1 else 0
def pathSave (leaf : Nat) : Nat := pairSave leaf + pairSave (leaf / 64)
/-- Top floor `max 16 (pool-57)` for the 74-credit root pool: 17 iff the top path saves nothing. -/
def floor (leaf : Nat) : Nat := if pathSave leaf = 0 then 17 else 16
/-- `x29` after `srli x29,x18,1; xor x29,x29,x18; andi x29,x29,65; sltiu x29,x29,1; addi x29,x29,16`
with `x18 = leaf`: bit 0 and bit 6 of the Gray code are `pairSave leaf` and `pairSave (leaf/64)`. -/
def guardWord (leaf : Nat) : BitVec 64 :=
  (if BitVec.ult (((BitVec.ofNat 64 leaf >>> 1) ^^^ BitVec.ofNat 64 leaf) &&& 65#64) 1#64 then 1#64 else 0#64) + 16#64
/-- `srli x29,x18,1; xor x29,x29,x18; andi x29,x29,65; sltiu x29,x29,1; addi x29,x29,16; nop; nop; nop`. -/
def words : List (BitVec 32) := [0x195e93,0x12eceb3,0x41efe93,0x1ebe93,0x10e8e93,0x13,0x13,0x13]
theorem guard_all : (List.range 4096).all (fun n => guardWord n == BitVec.ofNat 64 (floor n)) = true := by decide +kernel
theorem guard_checked : ∀ n : Fin 4096, guardWord n.val = BitVec.ofNat 64 (floor n.val) := by
  intro n
  exact beq_iff_eq.mp ((List.all_eq_true.mp guard_all) n.val (List.mem_range.mpr n.isLt))
theorem pathSave_le_two (leaf : Nat) : pathSave leaf ≤ 2 := by unfold pathSave pairSave;split_ifs <;> omega
theorem floor_eq_threshold (leaf : Nat) : floor leaf = max 16 ((74-pathSave leaf)-57) := by
  have h := pathSave_le_two leaf
  unfold floor;split_ifs <;> omega
#print axioms guard_checked
end SigGolfCandidate.Route16Guard
