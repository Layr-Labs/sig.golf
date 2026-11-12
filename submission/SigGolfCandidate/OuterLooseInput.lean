import SigGolfCandidate.OuterLooseBits
import SigGolfCandidate.OuterCodecInput
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterLooseInput
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterSignatureCodec OuterCodecValues
theorem tail0 (w : BitVec 64) : w &&& 7=(w.extractLsb' 0 16).setWidth 64 &&& 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;> simp [BitVec.getLsbD_extractLsb']
theorem tail1 (w : BitVec 64) : (w >>> (3 : Nat)) &&& 7=((w.extractLsb' 0 16) >>> (3 : Nat)).setWidth 64 &&& 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;> simp [BitVec.getLsbD_extractLsb']
theorem tail2 (w : BitVec 64) : (w >>> (6 : Nat)) &&& 7=((w.extractLsb' 0 16) >>> (6 : Nat)).setWidth 64 &&& 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;> simp [BitVec.getLsbD_extractLsb']
theorem tail3 (w : BitVec 64) : (w >>> (9 : Nat)) &&& 7=((w.extractLsb' 0 16) >>> (9 : Nat)).setWidth 64 &&& 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;> simp [BitVec.getLsbD_extractLsb']
theorem tail4 (w : BitVec 64) : (w >>> (12 : Nat)) &&& 15=((w.extractLsb' 0 16) >>> (12 : Nat)).setWidth 64 &&& 15 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;> simp [BitVec.getLsbD_extractLsb']
theorem words (sig : OldSig) (s : MachineState)
    (hw : ∀i,i<648→s.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (ht : (s.getMem 33856).extractLsb' 0 16=(splitOld sig).2) :
    ∀i,i<648→(packBlock.res.toState s).getMem (BitVec.ofNat 64 (28672+8*i))=
      (OuterLooseCodec.compress sig).extractLsb' (64*i) 64 := by
  intro i hi
  by_cases h0 : i=51
  · subst i
    have hc:=OuterLooseBits.carrier_word sig ⟨0,by decide⟩
    norm_num only [OuterCodecBits.carrierWord,OuterLooseBits.carrierShift,OuterLooseBits.carrierWidth,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Fin.val_mk,Nat.reduceLT,if_pos,if_neg,Nat.reduceMul,Nat.reducePow,Nat.reduceSub] at hc
    rw [show BitVec.ofNat 64 (28672+8*51)=(29080 : Word) from rfl,pack_first_word]
    rw [tail0,ht]
    rw [show (29080 : Word)=BitVec.ofNat 64 (28672+8*51) from rfl,hw 51 (by decide)]
    exact hc.symm
  by_cases h1 : i=101
  · subst i
    have hc:=OuterLooseBits.carrier_word sig ⟨1,by decide⟩
    norm_num only [OuterCodecBits.carrierWord,OuterLooseBits.carrierShift,OuterLooseBits.carrierWidth,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Fin.val_mk,Nat.reduceLT,if_pos,if_neg,Nat.reduceMul,Nat.reducePow,Nat.reduceSub] at hc
    rw [show BitVec.ofNat 64 (28672+8*101)=(29480 : Word) from rfl,pack_second_word]
    rw [tail1,ht]
    rw [show (29480 : Word)=BitVec.ofNat 64 (28672+8*101) from rfl,hw 101 (by decide)]
    exact hc.symm
  by_cases h2 : i=151
  · subst i
    have hc:=OuterLooseBits.carrier_word sig ⟨2,by decide⟩
    norm_num only [OuterCodecBits.carrierWord,OuterLooseBits.carrierShift,OuterLooseBits.carrierWidth,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Fin.val_mk,Nat.reduceLT,if_pos,if_neg,Nat.reduceMul,Nat.reducePow,Nat.reduceSub] at hc
    rw [show BitVec.ofNat 64 (28672+8*151)=(29880 : Word) from rfl,pack_third_word]
    rw [tail2,ht]
    rw [show (29880 : Word)=BitVec.ofNat 64 (28672+8*151) from rfl,hw 151 (by decide)]
    exact hc.symm
  by_cases h3 : i=201
  · subst i
    have hc:=OuterLooseBits.carrier_word sig ⟨3,by decide⟩
    norm_num only [OuterCodecBits.carrierWord,OuterLooseBits.carrierShift,OuterLooseBits.carrierWidth,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Fin.val_mk,Nat.reduceLT,if_pos,if_neg,Nat.reduceMul,Nat.reducePow,Nat.reduceSub] at hc
    rw [show BitVec.ofNat 64 (28672+8*201)=(30280 : Word) from rfl,pack_fourth_word]
    rw [tail3,ht]
    rw [show (30280 : Word)=BitVec.ofNat 64 (28672+8*201) from rfl,hw 201 (by decide)]
    exact hc.symm
  by_cases h4 : i=227
  · subst i
    have hc:=OuterLooseBits.carrier_word sig ⟨4,by decide⟩
    norm_num only [OuterCodecBits.carrierWord,OuterLooseBits.carrierShift,OuterLooseBits.carrierWidth,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Fin.val_mk,Nat.reduceLT,if_pos,if_neg,Nat.reduceMul,Nat.reducePow,Nat.reduceSub] at hc
    rw [show BitVec.ofNat 64 (28672+8*227)=(30488 : Word) from rfl,pack_fifth_word]
    rw [tail4,ht]
    rw [show (30488 : Word)=BitVec.ofNat 64 (28672+8*227) from rfl,hw 227 (by decide)]
    exact hc.symm
  rw [OuterCodecFrame.pack_frame]
  · rw [hw i hi,OuterLooseBits.regular_word sig i hi h0 h1 h2 h3 h4]
  · simp only [OuterCodecFrame.carrierWords,List.mem_cons,List.not_mem_nil,or_false]
    intro he
    rcases he with he|he|he|he|he
    all_goals
      have he':=congrArg BitVec.toNat he
      have ha : (BitVec.ofNat 64 (28672+8*i)).toNat=28672+8*i:=Nat.mod_eq_of_lt (by omega)
      rw [ha] at he'
      first
      | change 28672+8*i=29080 at he'
      | change 28672+8*i=29480 at he'
      | change 28672+8*i=29880 at he'
      | change 28672+8*i=30280 at he'
      | change 28672+8*i=30488 at he'
      omega
#print axioms words
end OuterLooseInput
