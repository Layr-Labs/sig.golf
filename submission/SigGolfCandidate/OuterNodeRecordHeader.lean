import SigGolfCandidate.OuterHeaderFields
import SigGolfCandidate.OuterNodeRecordBounds
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeRecordHeader
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachinePost
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem nibble (coord index : Nat) (hc : 1 ≤ coord) (hc9 : coord < 9) (hi : index < 2^31) :
    ((ftsNodeWord coord index >>> 11) &&& 15#64).toNat=15-coord := by
  simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  change ((ftsNodeWord coord index).toNat/2048) &&& (2^4-1)=15-coord
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := OuterHeaderFields.coordField coord index hc9
  omega

theorem record_word (coord index : Nat) (hc : 1 ≤ coord) (hc9 : coord < 9) (hi : index < 2^31) :
    ((((ftsNodeWord coord index >>> 11) &&& 15#64) ||| 2032#64) <<< 12)=
      BitVec.ofNat 64 (8323072+(15-coord)*4096) := by
  have hn : ((ftsNodeWord coord index >>> 11) &&& 15#64)=BitVec.ofNat 64 (15-coord) := by
    apply BitVec.eq_of_toNat_eq
    rw [nibble coord index hc hc9 hi,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [hn,BitVec.or_comm]
  change (BitVec.ofNat 64 (127*2^4) ||| BitVec.ofNat 64 (15-coord)) <<< 12=_
  rw [ofNat_or_add _ 127 4 (by omega),ofNat_shl]
  congr 1
  omega

theorem record_address (s : MachineState) (coord index : Nat) (hc : 1 ≤ coord) (hc9 : coord < 9) (hi : index < 2^31)
    (hword : s.getMem (s.getReg .x10+16#64)=ftsNodeWord coord index) :
    recordAddr s=BitVec.ofNat 64 (8323072+(15-coord)*4096) := by
  unfold recordAddr
  rw [hword]
  exact record_word coord index hc hc9 hi

#print axioms record_address
end OuterNodeRecordHeader
