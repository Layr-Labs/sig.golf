import SigGolfCandidate.OuterLooseCodec
import SigGolfCandidate.OuterCodecBits
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterLooseBits
open OuterSignatureCodec OuterTailBytes OuterTailPacket

theorem payload_bit (sig : OldSig) (i : Fin 5184) (j : Nat) (hj : j<8) :
    ((splitOld sig).1 i).getLsbD j=sig.getLsbD (8*i.val+j) := by
  simp only [splitOld,bytes,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  have h : 8*i.val+j<8*5184 := by omega
  simp only [h,decide_true,Bool.true_and,Nat.zero_add]

theorem compress_bit (sig : OldSig) (i : Nat) (hi : i<8*5184) :
    (OuterLooseCodec.compress sig).getLsbD i=
      (write (splitOld sig).1 (OuterLooseCodec.pack (OuterTailBytes.read (splitOld sig).1) (splitOld sig).2) ⟨i/8,by omega⟩).getLsbD (i%8) := by
  exact OuterCodecBits.ofBytes_bit _ _ _ hi

theorem regular_word (sig : OldSig) (i : Nat) (hi : i<648)
    (h0 : i≠51) (h1 : i≠101) (h2 : i≠151) (h3 : i≠201) (h4 : i≠227) :
    (OuterLooseCodec.compress sig).extractLsb' (64*i) 64=sig.extractLsb' (64*i) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  rw [compress_bit sig _ (by omega)]
  have hd : (64*i+j)/8=8*i+j/8 := by omega
  simp only [write,Fin.val_mk,hd,if_neg (by omega : 8*i+j/8≠415),if_neg (by omega : 8*i+j/8≠815),
    if_neg (by omega : 8*i+j/8≠1215),if_neg (by omega : 8*i+j/8≠1615),if_neg (by omega : 8*i+j/8≠1823)]
  rw [payload_bit _ _ _ (Nat.mod_lt _ (by decide))]
  simp only [Fin.val_mk]
  congr 1
  omega

def carrierShift (k : Fin 5) : Nat := if k.val<4 then 61 else 60
def carrierWidth (k : Fin 5) : Nat := if k.val<4 then 3 else 4

theorem carrier_word (sig : OldSig) (k : Fin 5) :
    (OuterLooseCodec.compress sig).extractLsb' (64*OuterCodecBits.carrierWord k) 64=
      sig.extractLsb' (64*OuterCodecBits.carrierWord k) 64 |||
        ((((splitOld sig).2 >>> (3*k.val)).setWidth 64 &&& (BitVec.ofNat 64 (2^carrierWidth k-1))) <<< carrierShift k) := by
  fin_cases k
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
    rw [compress_bit sig _ (by norm_num only [OuterCodecBits.carrierWord,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some];omega)]
    interval_cases j <;> simp [OuterCodecBits.carrierWord,carrierShift,carrierWidth,write,OuterLooseCodec.pack,OuterTailBytes.read,splitOld,bytes,BitVec.truncate,BitVec.getLsbD_extractLsb']
#print axioms payload_bit
#print axioms regular_word
#print axioms carrier_word
end OuterLooseBits
