import SigGolfCandidate.OuterNodeMachinePost
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeRecordBounds
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachinePost

theorem bounds (s : MachineState) : 2^22 ≤ (recordAddr s).toNat ∧ (recordAddr s).toNat < 2^23 ∧
    (recordAddr s).toNat % 8=0 := by
  let n : Word := (s.getMem (s.getReg .x10+16#64) >>> 16) &&& 15#64
  have hn : n.toNat<16 := by
    dsimp only [n]
    rw [BitVec.toNat_and]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  have he : n=BitVec.ofNat 64 n.toNat := by simp
  have hv : n ||| 2032#64=BitVec.ofNat 64 (2032+n.toNat) := by
    conv_lhs => rw [he,BitVec.or_comm]
    exact ofNat_or_add _ 127 4 hn
  have hr : recordAddr s=BitVec.ofNat 64 ((2032+n.toNat)*4096) := by
    change (n ||| 2032#64) <<< 12=_
    rw [hv,ofNat_shl]
    rfl
  rw [hr,BitVec.toNat_ofNat]
  have hbig : (2032+n.toNat)*4096<2^64 := by omega
  rw [Nat.mod_eq_of_lt hbig]
  omega

#print axioms bounds
end OuterNodeRecordBounds
