import SigGolfCandidate.OuterCodecMemory
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCodecInput
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterSignatureCodec

theorem words (sig : NewSig) (s : MachineState)
    (hw : ∀ i,i<648→s.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (hz : s.getMem 33856=0) :
    ∀ i,i<649→(unpackBlock.res.toState s).getMem (BitVec.ofNat 64 (28672+8*i))=
      (OuterSignatureCodec.expand sig).extractLsb' (64*i) 64 := by
  intro i hi
  by_cases ht : i=648
  · subst i
    change (unpackBlock.res.toState s).getMem 33856=_
    rw [OuterCodecMemory.unpack_tail_zero s hz,OuterCodecMemory.carriers sig s hw,OuterCodecBits.tail_word]
  by_cases h0 : i=51
  · subst i
    have hc:=OuterCodecBits.carrier_word sig ⟨0,by decide⟩
    simp only [OuterCodecBits.carrierWord,OuterCodecBits.carrierMask] at hc
    rw [show (BitVec.ofNat 64 (28672+8*51))=(29080 : Word) from rfl,OuterCodecValues.unpack_first_word]
    rw [show (29080 : Word)=BitVec.ofNat 64 (28672+8*51) from rfl,hw 51 (by decide)]
    exact hc.symm
  by_cases h1 : i=101
  · subst i
    have hc:=OuterCodecBits.carrier_word sig ⟨1,by decide⟩
    simp only [OuterCodecBits.carrierWord,OuterCodecBits.carrierMask] at hc
    rw [show (BitVec.ofNat 64 (28672+8*101))=(29480 : Word) from rfl,OuterCodecValues.unpack_second_word]
    rw [show (29480 : Word)=BitVec.ofNat 64 (28672+8*101) from rfl,hw 101 (by decide)]
    exact hc.symm
  by_cases h2 : i=151
  · subst i
    have hc:=OuterCodecBits.carrier_word sig ⟨2,by decide⟩
    simp only [OuterCodecBits.carrierWord,OuterCodecBits.carrierMask] at hc
    rw [show (BitVec.ofNat 64 (28672+8*151))=(29880 : Word) from rfl,OuterCodecValues.unpack_third_word]
    rw [show (29880 : Word)=BitVec.ofNat 64 (28672+8*151) from rfl,hw 151 (by decide)]
    exact hc.symm
  by_cases h3 : i=201
  · subst i
    have hc:=OuterCodecBits.carrier_word sig ⟨3,by decide⟩
    simp only [OuterCodecBits.carrierWord,OuterCodecBits.carrierMask] at hc
    rw [show (BitVec.ofNat 64 (28672+8*201))=(30280 : Word) from rfl,OuterCodecValues.unpack_fourth_word]
    rw [show (30280 : Word)=BitVec.ofNat 64 (28672+8*201) from rfl,hw 201 (by decide)]
    exact hc.symm
  by_cases h4 : i=227
  · subst i
    have hc:=OuterCodecBits.carrier_word sig ⟨4,by decide⟩
    simp only [OuterCodecBits.carrierWord,OuterCodecBits.carrierMask] at hc
    rw [show (BitVec.ofNat 64 (28672+8*227))=(30488 : Word) from rfl,OuterCodecValues.unpack_fifth_word]
    rw [show (30488 : Word)=BitVec.ofNat 64 (28672+8*227) from rfl,hw 227 (by decide)]
    exact hc.symm
  have hi' : i<648 := by omega
  rw [OuterCodecFrame.unpack_frame]
  · rw [hw i hi',OuterCodecBits.regular_word sig i hi' h0 h1 h2 h3 h4]
  · simp only [OuterCodecFrame.carrierWords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro he
    rcases he with (he|he|he|he|he)|he
    all_goals
      have he' := congrArg BitVec.toNat he
      have ha : (BitVec.ofNat 64 (28672+8*i)).toNat=28672+8*i := Nat.mod_eq_of_lt (by omega)
      rw [ha] at he'
      first
      | change 28672+8*i=29080 at he'
      | change 28672+8*i=29480 at he'
      | change 28672+8*i=29880 at he'
      | change 28672+8*i=30280 at he'
      | change 28672+8*i=30488 at he'
      | change 28672+8*i=33856 at he'
      omega
#print axioms words
end OuterCodecInput
