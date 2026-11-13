import SigGolfCandidate.OuterCodecBits
import SigGolfCandidate.OuterCodecPacket
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCodecMemory
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterCodecValues OuterSignatureCodec

theorem byte_extract {n : Nat} (v : BitVec n) (i b : Nat) (hb : b<8) :
    extractByte (v.extractLsb' (64*i) 64) b=v.extractLsb' (64*i+8*b) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [extractByte,BitVec.truncate,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  have h : b*8+j<64 := by omega
  try simp only [h,decide_true,Bool.true_and]
  congr 1
  omega

theorem carriers (sig : NewSig) (s : MachineState)
    (hw : ∀ i,i<648→s.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64) :
    OuterCodecPacket.readCarriers s=OuterTailBytes.readNew (bytes 5183 sig) := by
  apply OuterTailPacket.Four.ext
  all_goals
    simp only [OuterCodecPacket.readCarriers,OuterTailBytes.readNew,OuterSignatureCodec.bytes]
  · rw [show (29080 : Word)=BitVec.ofNat 64 (28672+8*51) from rfl,hw 51 (by decide),byte_extract _ _ _ (by decide)]
    rfl
  · rw [show (29480 : Word)=BitVec.ofNat 64 (28672+8*101) from rfl,hw 101 (by decide),byte_extract _ _ _ (by decide)]
    rfl
  · rw [show (29880 : Word)=BitVec.ofNat 64 (28672+8*151) from rfl,hw 151 (by decide),byte_extract _ _ _ (by decide)]
    rfl
  · rw [show (30280 : Word)=BitVec.ofNat 64 (28672+8*201) from rfl,hw 201 (by decide),byte_extract _ _ _ (by decide)]
    rfl

theorem unpack_tail_zero (s : MachineState) (hz : s.getMem 33856=0) :
    (unpackBlock.res.toState s).getMem 33856=(OuterTailPacket.unpack (OuterCodecPacket.readCarriers s)).2.setWidth 64 := by
  rw [unpack_tail_word,hz]
  try simp only [BitVec.zero_and,BitVec.zero_or]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;> simp [replaceHalfword,unpackedTail,joinedWord,OuterTailPacket.unpack,OuterCodecPacket.readCarriers,extractByte]

#print axioms byte_extract
#print axioms carriers
#print axioms unpack_tail_zero
end OuterCodecMemory
