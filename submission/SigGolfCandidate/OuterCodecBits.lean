import SigGolfCandidate.OuterSignatureCodec
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import RiscvZkvm.Rv64.Word
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCodecBits
open OuterSignatureCodec OuterTailBytes OuterTailPacket RiscvZkvm.Rv64

theorem ofBytes_bit (n : Nat) (f : Fin n → BitVec 8) (i : Nat) (hi : i<8*n) :
    (ofBytes n f).getLsbD i=(f ⟨i/8,by omega⟩).getLsbD (i%8) := by
  unfold ofBytes
  rw [fromBits_get (8*n) _ ⟨i,hi⟩]

theorem expand_payload_bit (sig : NewSig) (i : Nat) (hi : i<8*5184) :
    (OuterSignatureCodec.expand sig).getLsbD i=
      ((OuterTailBytes.expand (bytes 5183 sig)).1 ⟨i/8,by omega⟩).getLsbD (i%8) := by
  simp only [OuterSignatureCodec.expand,joinOld,BitVec.getLsbD_append,hi,decide_true,↓reduceIte]
  exact ofBytes_bit _ _ _ hi

theorem regular_word (sig : NewSig) (i : Nat) (hi : i<648)
    (h0 : i≠51) (h1 : i≠101) (h2 : i≠151) (h3 : i≠201) (h4 : i≠227) (h5 : i≠647) :
    (OuterSignatureCodec.expand sig).extractLsb' (64*i) 64=sig.extractLsb' (64*i) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  rw [expand_payload_bit sig (64*i+j) (by omega)]
  have hd : (64*i+j)/8=8*i+j/8 := by omega
  have hm : (64*i+j)%8=j%8 := by omega
  simp only [OuterTailBytes.expand,writeOld,inflate,Fin.val_mk,hd,
    if_neg (by omega : 8*i+j/8≠415),if_neg (by omega : 8*i+j/8≠815),
    if_neg (by omega : 8*i+j/8≠1215),if_neg (by omega : 8*i+j/8≠1615),
    if_neg (by omega : 8*i+j/8≠1823),compactIndex,if_neg (by omega : 8*i+j/8≠5183),bytes]
  simp only [BitVec.getLsbD_extractLsb',show (64*i+j)%8<8 from Nat.mod_lt _ (by decide),decide_true,Bool.true_and]
  congr 1
  omega

def carrierWord (k : Fin 5) : Nat := [51,101,151,201,227].getD k.val 0
def decodedByte (sig : NewSig) (k : Fin 5) : BitVec 8 :=
  let v:=(unpack (readNew (bytes 5183 sig))).1
  [v.a,v.b,v.c,v.d,v.e].getD k.val 0

theorem carrier_word (sig : NewSig) (k : Fin 5) :
    (OuterSignatureCodec.expand sig).extractLsb' (64*carrierWord k) 64=
      replaceByte (sig.extractLsb' (64*carrierWord k) 64) 7 (decodedByte sig k) := by
  fin_cases k
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
    rw [expand_payload_bit sig _ (by norm_num only [carrierWord,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some];omega)]
    interval_cases j <;> simp [carrierWord,decodedByte,OuterTailBytes.expand,writeOld,inflate,compactIndex,bytes,replaceByte,BitVec.getLsbD_extractLsb']

theorem last_word (sig : NewSig) :
    (OuterSignatureCodec.expand sig).extractLsb' (64*647) 64=
      replaceByte (sig.extractLsb' (64*647) 64) 7 (sig.extractLsb' (8*1823) 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  rw [expand_payload_bit sig _ (by omega)]
  interval_cases j <;> simp [OuterTailBytes.expand,writeOld,inflate,compactIndex,bytes,replaceByte,BitVec.getLsbD_extractLsb']

theorem tail_word (sig : NewSig) :
    (OuterSignatureCodec.expand sig).extractLsb' (64*648) 64=(unpack (readNew (bytes 5183 sig))).2.setWidth 64 := by
  change ((unpack (readNew (bytes 5183 sig))).2 ++ ofBytes 5184 _).extractLsb' (64*648) 64=_
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb']
  simp only [hj,decide_true,Bool.true_and]
  rw [BitVec.getLsbD_append,if_neg (by omega : ¬(64*648+j<8*5184))]
  simp only [BitVec.getLsbD_setWidth,hj,decide_true,Bool.true_and]
  rw [show 64*648+j-8*5184=j by omega]
#print axioms regular_word
#print axioms carrier_word
#print axioms last_word
#print axioms tail_word
end OuterCodecBits
