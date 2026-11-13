import SigGolfCandidate.OuterLooseCodec
import SigGolfCandidate.OuterCodecBits
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLooseBits
open OuterSignatureCodec OuterTailBytes OuterTailPacket RiscvZkvm.Rv64

theorem payload_bit (sig : OldSig) (i : Fin 5184) (j : Nat) (hj : j<8) :
    ((splitOld sig).1 i).getLsbD j=sig.getLsbD (8*i.val+j) := by
  simp only [splitOld,bytes,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  have h : 8*i.val+j<8*5184 := by omega
  simp only [h,decide_true,Bool.true_and,Nat.zero_add]

theorem compress_bit (sig : OldSig) (i : Nat) (hi : i<8*5183) :
    (OuterLooseCodec.compress sig).getLsbD i=
      (write (splitOld sig).1 (OuterLooseCodec.pack (OuterTailBytes.read (splitOld sig).1) (splitOld sig).2) ⟨i/8,by omega⟩).getLsbD (i%8) := by
  exact OuterCodecBits.ofBytes_bit _ _ _ hi

theorem regular_word (sig : OldSig) (i : Nat) (hi : i<648)
    (h0 : i≠51) (h1 : i≠101) (h2 : i≠151) (h3 : i≠201) (h4 : i≠227) (h5 : i≠647) :
    (OuterLooseCodec.compress sig).extractLsb' (64*i) 64=sig.extractLsb' (64*i) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  rw [compress_bit sig _ (by omega)]
  have hd : (64*i+j)/8=8*i+j/8 := by omega
  simp only [write,writeNew,keep,Fin.val_mk,hd,if_neg (by omega : 8*i+j/8≠415),if_neg (by omega : 8*i+j/8≠815),
    if_neg (by omega : 8*i+j/8≠1215),if_neg (by omega : 8*i+j/8≠1615),originalIndex,if_neg (by omega : 8*i+j/8≠1823)]
  rw [payload_bit _ _ _ (Nat.mod_lt _ (by decide))]
  simp only [Fin.val_mk]
  congr 1
  omega

def encodedByte (sig : OldSig) (k : Fin 5) : BitVec 8 :=
  let v:=OuterLooseCodec.pack (OuterTailBytes.read (splitOld sig).1) (splitOld sig).2
  [v.a,v.b,v.c,v.d,sig.extractLsb' (8*5183) 8].getD k.val 0

theorem carrier_word (sig : OldSig) (k : Fin 5) :
    (OuterLooseCodec.compress sig).extractLsb' (64*OuterCodecBits.carrierWord k) 64=
      replaceByte (sig.extractLsb' (64*OuterCodecBits.carrierWord k) 64) 7 (encodedByte sig k) := by
  fin_cases k
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
    rw [compress_bit sig _ (by norm_num only [OuterCodecBits.carrierWord,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some];omega)]
    interval_cases j <;> simp [OuterCodecBits.carrierWord,encodedByte,write,writeNew,keep,originalIndex,splitOld,bytes,replaceByte,BitVec.getLsbD_extractLsb']

theorem last_word (sig : OldSig) :
    (OuterLooseCodec.compress sig).extractLsb' (64*647) 64=
      replaceByte (sig.extractLsb' (64*647) 64) 7 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  by_cases h : j<56
  · rw [compress_bit sig _ (by omega)]
    interval_cases j <;> simp_all [write,writeNew,keep,originalIndex,splitOld,bytes,replaceByte,BitVec.getLsbD_extractLsb']
  · have hz : (OuterLooseCodec.compress sig).getLsbD (64*647+j)=false := BitVec.getLsbD_of_ge _ _ (by omega)
    rw [hz]
    interval_cases j <;> simp_all [replaceByte,BitVec.getLsbD_extractLsb']
#print axioms regular_word
#print axioms carrier_word
#print axioms last_word
end OuterLooseBits
