import SigGolfCandidate.OuterLooseBits
import SigGolfCandidate.OuterCodecInput
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLooseInput
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterSignatureCodec OuterCodecValues

theorem words (sig : OldSig) (s : MachineState)
    (hw : ∀i,i<648→s.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (ht : (s.getMem 33856).extractLsb' 0 16=(splitOld sig).2) :
    ∀i,i<648→(packBlock.res.toState s).getMem (BitVec.ofNat 64 (28672+8*i))=
      (OuterLooseCodec.compress sig).extractLsb' (64*i) 64 := by
  have w0 : s.getMem 29080=sig.extractLsb' (64*51) 64 := hw 51 (by decide)
  have w1 : s.getMem 29480=sig.extractLsb' (64*101) 64 := hw 101 (by decide)
  have w2 : s.getMem 29880=sig.extractLsb' (64*151) 64 := hw 151 (by decide)
  have w3 : s.getMem 30280=sig.extractLsb' (64*201) 64 := hw 201 (by decide)
  have w4 : s.getMem 30488=sig.extractLsb' (64*227) 64 := hw 227 (by decide)
  have w5 : s.getMem 33848=sig.extractLsb' (64*647) 64 := hw 647 (by decide)
  have tail : s.getMem 33856 &&& 65535=((splitOld sig).2).setWidth 64 := by
    rw [←ht]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [BitVec.getLsbD_extractLsb']
  intro i hi
  by_cases h0 : i=51
  · subst i
    change (packBlock.res.toState s).getMem 29080=_
    have hc:=OuterLooseBits.carrier_word sig ⟨0,by decide⟩
    change (OuterLooseCodec.compress sig).extractLsb' (64*51) 64=replaceByte (sig.extractLsb' (64*51) 64) 7 (OuterLooseBits.encodedByte sig ⟨0,by decide⟩) at hc
    conv_rhs => rw [hc]
    rw [pack_first_word,w0]
    apply congrArg (replaceByte (sig.extractLsb' (64*51) 64) 7)
    simp only [packedWord,w0,w1,w2,w3,w4,tail]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterLooseBits.encodedByte,OuterLooseCodec.pack,OuterLooseCodec.packedWord,OuterTailBytes.read,splitOld,OuterSignatureCodec.bytes,extractByte,BitVec.truncate,BitVec.getLsbD_extractLsb']
  by_cases h1 : i=101
  · subst i
    change (packBlock.res.toState s).getMem 29480=_
    have hc:=OuterLooseBits.carrier_word sig ⟨1,by decide⟩
    change (OuterLooseCodec.compress sig).extractLsb' (64*101) 64=replaceByte (sig.extractLsb' (64*101) 64) 7 (OuterLooseBits.encodedByte sig ⟨1,by decide⟩) at hc
    conv_rhs => rw [hc]
    rw [pack_second_word,w1]
    apply congrArg (replaceByte (sig.extractLsb' (64*101) 64) 7)
    simp only [packedWord,w0,w1,w2,w3,w4,tail]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterLooseBits.encodedByte,OuterLooseCodec.pack,OuterLooseCodec.packedWord,OuterTailBytes.read,splitOld,OuterSignatureCodec.bytes,extractByte,BitVec.truncate,BitVec.getLsbD_extractLsb']
  by_cases h2 : i=151
  · subst i
    change (packBlock.res.toState s).getMem 29880=_
    have hc:=OuterLooseBits.carrier_word sig ⟨2,by decide⟩
    change (OuterLooseCodec.compress sig).extractLsb' (64*151) 64=replaceByte (sig.extractLsb' (64*151) 64) 7 (OuterLooseBits.encodedByte sig ⟨2,by decide⟩) at hc
    conv_rhs => rw [hc]
    rw [pack_third_word,w2]
    apply congrArg (replaceByte (sig.extractLsb' (64*151) 64) 7)
    simp only [packedWord,w0,w1,w2,w3,w4,tail]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterLooseBits.encodedByte,OuterLooseCodec.pack,OuterLooseCodec.packedWord,OuterTailBytes.read,splitOld,OuterSignatureCodec.bytes,extractByte,BitVec.truncate,BitVec.getLsbD_extractLsb']
  by_cases h3 : i=201
  · subst i
    change (packBlock.res.toState s).getMem 30280=_
    have hc:=OuterLooseBits.carrier_word sig ⟨3,by decide⟩
    change (OuterLooseCodec.compress sig).extractLsb' (64*201) 64=replaceByte (sig.extractLsb' (64*201) 64) 7 (OuterLooseBits.encodedByte sig ⟨3,by decide⟩) at hc
    conv_rhs => rw [hc]
    rw [pack_fourth_word,w3]
    apply congrArg (replaceByte (sig.extractLsb' (64*201) 64) 7)
    simp only [packedWord,w0,w1,w2,w3,w4,tail]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;> simp [OuterLooseBits.encodedByte,OuterLooseCodec.pack,OuterLooseCodec.packedWord,OuterTailBytes.read,splitOld,OuterSignatureCodec.bytes,extractByte,BitVec.truncate,BitVec.getLsbD_extractLsb']
  by_cases h4 : i=227
  · subst i
    change (packBlock.res.toState s).getMem 30488=_
    have hc:=OuterLooseBits.carrier_word sig ⟨4,by decide⟩
    change (OuterLooseCodec.compress sig).extractLsb' (64*227) 64=replaceByte (sig.extractLsb' (64*227) 64) 7 (OuterLooseBits.encodedByte sig ⟨4,by decide⟩) at hc
    conv_rhs => rw [hc]
    rw [pack_fifth_word,w4,w5,OuterCodecMemory.byte_extract _ _ _ (by decide)]
    rfl
  by_cases h5 : i=647
  · subst i
    change (packBlock.res.toState s).getMem 33848=_
    conv_rhs => rw [OuterLooseBits.last_word sig]
    rw [pack_last_word,w5]
  conv_rhs => rw [OuterLooseBits.regular_word sig i hi h0 h1 h2 h3 h4 h5]
  rw [OuterCodecFrame.pack_frame]
  · exact hw i hi
  · simp only [OuterCodecFrame.carrierWords,List.mem_cons,List.not_mem_nil,or_false]
    intro he
    rcases he with he|he|he|he|he|he
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
      omega
#print axioms words
end OuterLooseInput
