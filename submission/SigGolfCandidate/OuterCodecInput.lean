import SigGolfCandidate.OuterCodecMemory
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCodecInput
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterCodecValues OuterSignatureCodec

theorem words (sig : NewSig) (s : MachineState)
    (hw : ∀ i,i<648→s.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (hz : s.getMem 33856=0) :
    ∀ i,i<649→(unpackBlock.res.toState s).getMem (BitVec.ofNat 64 (28672+8*i))=
      (OuterSignatureCodec.expand sig).extractLsb' (64*i) 64 := by
  have w0 : s.getMem 29080=sig.extractLsb' (64*51) 64 := hw 51 (by decide)
  have w1 : s.getMem 29480=sig.extractLsb' (64*101) 64 := hw 101 (by decide)
  have w2 : s.getMem 29880=sig.extractLsb' (64*151) 64 := hw 151 (by decide)
  have w3 : s.getMem 30280=sig.extractLsb' (64*201) 64 := hw 201 (by decide)
  have w4 : s.getMem 30488=sig.extractLsb' (64*227) 64 := hw 227 (by decide)
  have w5 : s.getMem 33848=sig.extractLsb' (64*647) 64 := hw 647 (by decide)
  intro i hi
  by_cases ht : i=648
  · subst i
    change (unpackBlock.res.toState s).getMem 33856=_
    rw [OuterCodecMemory.unpack_tail_zero s hz,OuterCodecMemory.carriers sig s hw,OuterCodecBits.tail_word]
  by_cases h0 : i=51
  · subst i
    change (unpackBlock.res.toState s).getMem 29080=_
    rw [unpack_first_word,w0]
    have hc:=OuterCodecBits.carrier_word sig ⟨0,by decide⟩
    change (OuterSignatureCodec.expand sig).extractLsb' (64*51) 64=replaceByte (sig.extractLsb' (64*51) 64) 7 (OuterCodecBits.decodedByte sig ⟨0,by decide⟩) at hc
    rw [hc]
    change replaceByte (sig.extractLsb' (64*51) 64) 7 _=replaceByte (sig.extractLsb' (64*51) 64) 7 _
    congr 1
    simp only [joinedWord,w0,w1,w2,w3]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterCodecBits.decodedByte,OuterTailPacket.unpack,OuterTailBytes.readNew,OuterSignatureCodec.bytes,BitVec.getLsbD_extractLsb']
  by_cases h1 : i=101
  · subst i
    change (unpackBlock.res.toState s).getMem 29480=_
    rw [unpack_second_word,w1]
    have hc:=OuterCodecBits.carrier_word sig ⟨1,by decide⟩
    change (OuterSignatureCodec.expand sig).extractLsb' (64*101) 64=replaceByte (sig.extractLsb' (64*101) 64) 7 (OuterCodecBits.decodedByte sig ⟨1,by decide⟩) at hc
    rw [hc]
    change replaceByte (sig.extractLsb' (64*101) 64) 7 _=replaceByte (sig.extractLsb' (64*101) 64) 7 _
    congr 1
    simp only [joinedWord,w0,w1,w2,w3]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterCodecBits.decodedByte,OuterTailPacket.unpack,OuterTailBytes.readNew,OuterSignatureCodec.bytes,BitVec.getLsbD_extractLsb']
  by_cases h2 : i=151
  · subst i
    change (unpackBlock.res.toState s).getMem 29880=_
    rw [unpack_third_word,w2]
    have hc:=OuterCodecBits.carrier_word sig ⟨2,by decide⟩
    change (OuterSignatureCodec.expand sig).extractLsb' (64*151) 64=replaceByte (sig.extractLsb' (64*151) 64) 7 (OuterCodecBits.decodedByte sig ⟨2,by decide⟩) at hc
    rw [hc]
    change replaceByte (sig.extractLsb' (64*151) 64) 7 _=replaceByte (sig.extractLsb' (64*151) 64) 7 _
    congr 1
    simp only [joinedWord,w0,w1,w2,w3]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterCodecBits.decodedByte,OuterTailPacket.unpack,OuterTailBytes.readNew,OuterSignatureCodec.bytes,BitVec.getLsbD_extractLsb']
  by_cases h3 : i=201
  · subst i
    change (unpackBlock.res.toState s).getMem 30280=_
    rw [unpack_fourth_word,w3]
    have hc:=OuterCodecBits.carrier_word sig ⟨3,by decide⟩
    change (OuterSignatureCodec.expand sig).extractLsb' (64*201) 64=replaceByte (sig.extractLsb' (64*201) 64) 7 (OuterCodecBits.decodedByte sig ⟨3,by decide⟩) at hc
    rw [hc]
    change replaceByte (sig.extractLsb' (64*201) 64) 7 _=replaceByte (sig.extractLsb' (64*201) 64) 7 _
    congr 1
    simp only [joinedWord,w0,w1,w2,w3]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterCodecBits.decodedByte,OuterTailPacket.unpack,OuterTailBytes.readNew,OuterSignatureCodec.bytes,BitVec.getLsbD_extractLsb']
  by_cases h4 : i=227
  · subst i
    change (unpackBlock.res.toState s).getMem 30488=_
    rw [unpack_fifth_word,w4]
    have hc:=OuterCodecBits.carrier_word sig ⟨4,by decide⟩
    change (OuterSignatureCodec.expand sig).extractLsb' (64*227) 64=replaceByte (sig.extractLsb' (64*227) 64) 7 (OuterCodecBits.decodedByte sig ⟨4,by decide⟩) at hc
    rw [hc]
    change replaceByte (sig.extractLsb' (64*227) 64) 7 _=replaceByte (sig.extractLsb' (64*227) 64) 7 _
    congr 1
    simp only [joinedWord,w0,w1,w2,w3]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterCodecBits.decodedByte,OuterTailPacket.unpack,OuterTailBytes.readNew,OuterSignatureCodec.bytes,BitVec.getLsbD_extractLsb']
  by_cases h5 : i=647
  · subst i
    change (unpackBlock.res.toState s).getMem 33848=_
    rw [unpack_last_word,w5]
    rw [OuterCodecBits.last_word,w4,OuterCodecMemory.byte_extract _ _ _ (by decide)]
  have hi' : i<648 := by omega
  rw [OuterCodecFrame.unpack_frame]
  · rw [hw i hi',OuterCodecBits.regular_word sig i hi' h0 h1 h2 h3 h4 h5]
  · simp only [OuterCodecFrame.carrierWords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro he
    rcases he with (he|he|he|he|he|he)|he
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
      | change 28672+8*i=33848 at he'
      | change 28672+8*i=33856 at he'
      omega
#print axioms words
end OuterCodecInput
