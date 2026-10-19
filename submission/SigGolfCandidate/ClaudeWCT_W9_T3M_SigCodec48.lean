import SigGolfCandidate.ClaudeWCT_W9_T3M_SigCodecC
set_option Elab.async false

/-! # The pre-v6 5,248-byte signature layout (`SharedCodec48`, r3-lean-topbytes)

The img-v6 expander first runs a pre-pass (words 43250..43333) that rewrites the 5,239-byte signature in place into
this older 5,248-byte layout; the rest of the expander and its proofs read the 5,248-byte layout. Copied from the
r3x codec (`SharedCodec`, Bytes 5248); the layout-independent definitions (`sigDigests`, `serializedWord`,
`inflatedRead`, ...) are shared with the v6 `SharedCodec`. -/
namespace ClaudeWCT.W9.T3M.SharedCodec48
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat getD_append_left' getD_append_right' getD_ofFn'
  chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)

abbrev CBytes := Bytes 5248
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- Full index179 is stored as the trailing112-bit top sibling. -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 179 then cDig b k else if k = 179 then (b.extractLsb' (128 * 327) 112).setWidth 128 else cDig b (k - 1)
def sigDecC (b : CBytes) : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature where
  rho := digC b 0
  policyHints := b.extractLsb' (8 * 5246) 16
  forest := {
    pairs := fun p => {
      firstValues := fun i => digC b (1 + 25 * p.val + i.val)
      firstPath := fun i => digC b (1 + 25 * p.val + 6 + i.val)
      secondValues := fun i => digC b (1 + 25 * p.val + 12 + i.val)
      secondPath := fun i => digC b (1 + 25 * p.val + 18 + i.val) }
    singleton := {
      values := fun i => digC b (101 + i.val)
      path := fun i => digC b (107 + i.val) } }
  layers := fun lay => {
    values := fun i => digC b (ClaudeWCT.W9.T3M.SharedCodec.layIdx lay + i.val)
    path := fun i => digC b (ClaudeWCT.W9.T3M.SharedCodec.layIdx lay + chainCount lay + i.val) }
def sigBC (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) : CBytes :=
  BitVec.ofNat _ (digNat ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179) +
    2 ^ (128 * 327) * (((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD 179 0).toNat % 2 ^ 112) +
    2 ^ (8 * 5246) * s.policyHints.toNat)
theorem compact_length : 327 * 16 + 14 + 2 = 5248 := by decide
end ClaudeWCT.W9.T3M.SharedCodec48


namespace ClaudeWCT.W9.T3M.SharedCodec48
open ClaudeWCT.W9.T3M.SharedCodec
end ClaudeWCT.W9.T3M.SharedCodec48

namespace ClaudeWCT.W9.T3M.SharedCodec48
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.T3
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem tail_low_word (b : CBytes) :
    ((b.extractLsb' (128*327) 112).setWidth 128).extractLsb' 0 64 =
      b.extractLsb' (64*654) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, Nat.zero_add,
    hj, decide_true, Bool.true_and]
  rw [show decide (j < 128) = true from decide_eq_true (by omega), Bool.true_and,
    show decide (j < 112) = true from decide_eq_true (by omega), Bool.true_and]

theorem tail_high_word (b : CBytes) :
    ((b.extractLsb' (128*327) 112).setWidth 128).extractLsb' 64 64 =
      (b.extractLsb' (64*655) 64 <<< 16) >>> 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    hj, decide_true, Bool.true_and]
  by_cases h : j < 48
  · simp only [show decide (64+j < 128) = true from decide_eq_true (by omega),
      show decide (64+j < 112) = true from decide_eq_true (by omega),
      show decide (16+j < 64) = true from decide_eq_true (by omega),
      show decide (16+j < 16) = false from decide_eq_false (by omega),
      Bool.not_false, Bool.true_and, Nat.add_sub_cancel_left, hj, decide_true]
    congr 1
    omega
  · simp only [show decide (64+j < 112) = false from decide_eq_false (by omega),
      show decide (16+j < 64) = false from decide_eq_false (by omega),
      Bool.false_and, Bool.and_false]

theorem serializedWord_digC (b : CBytes) (k i : Nat) (hi : i < 2) :
    ClaudeWCT.W9.T3M.SharedCodec.serializedWord (fun j => b.extractLsb' (64*j) 64) (2*k+i) =
      (ClaudeWCT.W9.T3M.SharedCodec.inflatedRead (0 : Digest) (digC b) k).extractLsb' (64*i) 64 := by
  rw [ClaudeWCT.W9.T3M.SharedCodec.serializedWord_index _ k i hi]
  cases hd : ClaudeWCT.W9.T3M.SharedCodec.internalDummy k
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, ClaudeWCT.W9.T3M.SharedCodec.inflatedRead]
    by_cases ht : k = 183
    · subst k
      simp only [if_pos rfl, show ClaudeWCT.W9.T3M.SharedCodec.externalFullIndex 183 = 179 from rfl, digC,
        show ¬(179 < 179) from by omega, if_neg, if_pos rfl]
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · simpa only [Nat.mul_zero, ↓reduceIte] using (tail_low_word b).symm
      · simpa using (tail_high_word b).symm
    · rw [if_neg ht]
      have he : ClaudeWCT.W9.T3M.SharedCodec.externalFullIndex k ≠ 179 := by
        intro h
        exact ht ((ClaudeWCT.W9.T3M.SharedCodec.externalFullIndex_tail_iff k).mp h)
      unfold digC
      by_cases hl : ClaudeWCT.W9.T3M.SharedCodec.externalFullIndex k < 179
      · simp only [if_pos hl, cDig]
        rw [ClaudeWCT.W9.T3M.SharedCodec.extract_digest_word b _ i hi]
        congr 1
        omega
      · simp only [if_neg hl, if_neg he, cDig]
        rw [ClaudeWCT.W9.T3M.SharedCodec.extract_digest_word b _ i hi]
        congr 1
        omega
  · simp [hd, ClaudeWCT.W9.T3M.SharedCodec.inflatedRead]

end ClaudeWCT.W9.T3M.SharedCodec48

namespace ClaudeWCT.W9.T3M.SharedCodec48
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit lt_split split_mod split_div)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem sigBC_toNat (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) :
    (sigBC s).toNat = digNat ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179) +
      2^(128*327)*(((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD 179 0).toNat%2^112)+
      2^(8*5246)*s.policyHints.toNat := by
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179)
  rw [ClaudeWCT.W9.T3M.SharedCodec.length_eraseIdx_sig] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD 179 0).toNat (show 0<2^112 by positivity))
  have hx : digNat ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179)+
      2^(128*327)*(((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD 179 0).toNat%2^112)<2^(8*5246) := by
    simpa only [←pow_add] using hT
  have hn := lt_split _ _ _ _ hx s.policyHints.isLt
  simpa only [←pow_add] using hn

theorem encoded_low (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) :
    (sigBC s).toNat%2^(128*327)=digNat ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179) := by
  have hD := digNat_lt ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179)
  rw [ClaudeWCT.W9.T3M.SharedCodec.length_eraseIdx_sig] at hD
  rw [sigBC_toNat,show 2^(8*5246)=2^(128*327)*2^112 by rw [←pow_add]]
  rw [mul_assoc,add_assoc,←mul_add,split_mod _ _ _ hD]

theorem encoded_tail (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) :
    (sigBC s).toNat/2^(128*327)%2^112=((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD 179 0).toNat%2^112 := by
  have hD := digNat_lt ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179)
  rw [ClaudeWCT.W9.T3M.SharedCodec.length_eraseIdx_sig] at hD
  rw [sigBC_toNat,show 2^(8*5246)=2^(128*327)*2^112 by rw [←pow_add]]
  rw [mul_assoc,add_assoc,←mul_add,split_div _ _ _ hD,Nat.add_mul_mod_self_left,Nat.mod_mod]

theorem encoded_hints (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) :
    (sigBC s).toNat/2^(8*5246)=s.policyHints.toNat := by
  have hD := digNat_lt ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179)
  rw [ClaudeWCT.W9.T3M.SharedCodec.length_eraseIdx_sig] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD 179 0).toNat (show 0<2^112 by positivity))
  rw [sigBC_toNat,split_div _ _ _ (by simpa only [←pow_add] using hT)]

theorem cDig_sigBC (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) (j : Nat) (hj : j<327) :
    cDig (sigBC s) j=((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).eraseIdx 179).getD j 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,←digNat_digit]
  rw [←mod_digit _ 327 j hj,encoded_low]

theorem digC_sigBC (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) (k : Nat) (hk : k<328) :
    digC (sigBC s) k=if k=179 then BitVec.ofNat 128 (((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD k 0).toNat % 2 ^ 112)
      else (ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD k 0 := by
  by_cases hlt : k<179
  · rw [digC,if_pos hlt,cDig_sigBC s k (by omega),getD_eraseIdx,if_pos hlt,if_neg (by omega)]
  · by_cases he : k=179
    · subst he
      rw [digC,if_neg (by decide),if_pos rfl,if_pos rfl]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,encoded_tail,
        BitVec.toNat_ofNat]
    · rw [digC,if_neg hlt,if_neg he,cDig_sigBC s (k-1) (by omega),getD_eraseIdx,
        if_neg (by omega),show k-1+1=k by omega,if_neg he]

theorem policyHints_sigDecC_sigBC (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) :
    (sigDecC (sigBC s)).policyHints=s.policyHints := by
  apply BitVec.eq_of_toNat_eq
  change ((sigBC s).extractLsb' (8*5246) 16).toNat=s.policyHints.toNat
  rw [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,encoded_hints,Nat.mod_eq_of_lt s.policyHints.isLt]

#print axioms digC_sigBC
#print axioms policyHints_sigDecC_sigBC
end ClaudeWCT.W9.T3M.SharedCodec48

namespace ClaudeWCT.W9.T3M.SharedCodec48
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (getD_append_left' getD_append_right' getD_ofFn')
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem forest_sigDecC_sigBC (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature) :
    (sigDecC (sigBC s)).forest=s.forest := by
  have hp : (sigDecC (sigBC s)).forest.pairs=s.forest.pairs := by
    funext p
    have h1 : ((sigDecC (sigBC s)).forest.pairs p).firstValues=(s.forest.pairs p).firstValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),ClaudeWCT.W9.T3M.SharedCodec.sigDigests_pair s p i.val (by omega),ClaudeWCT.W9.T3M.SharedCodec.pairList_firstValue]
    have h2 : ((sigDecC (sigBC s)).forest.pairs p).firstPath=(s.forest.pairs p).firstPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+6+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 1+25*p.val+6+i.val=1+25*p.val+(6+i.val) by omega,
        ClaudeWCT.W9.T3M.SharedCodec.sigDigests_pair s p (6+i.val) (by omega),ClaudeWCT.W9.T3M.SharedCodec.pairList_firstPath]
    have h3 : ((sigDecC (sigBC s)).forest.pairs p).secondValues=(s.forest.pairs p).secondValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+12+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 1+25*p.val+12+i.val=1+25*p.val+(12+i.val) by omega,
        ClaudeWCT.W9.T3M.SharedCodec.sigDigests_pair s p (12+i.val) (by omega),ClaudeWCT.W9.T3M.SharedCodec.pairList_secondValue]
    have h4 : ((sigDecC (sigBC s)).forest.pairs p).secondPath=(s.forest.pairs p).secondPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+18+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 1+25*p.val+18+i.val=1+25*p.val+(18+i.val) by omega,
        ClaudeWCT.W9.T3M.SharedCodec.sigDigests_pair s p (18+i.val) (by omega),ClaudeWCT.W9.T3M.SharedCodec.pairList_secondPath]
    cases h : (sigDecC (sigBC s)).forest.pairs p
    cases h' : s.forest.pairs p
    simp only [h,h'] at h1 h2 h3 h4
    cases h1;cases h2;cases h3;cases h4;rfl
  have hs : (sigDecC (sigBC s)).forest.singleton=s.forest.singleton := by
    have h1 : (sigDecC (sigBC s)).forest.singleton.values=s.forest.singleton.values := by
      funext i
      change digC (sigBC s) (101+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),ClaudeWCT.W9.T3M.SharedCodec.sigDigests_singleton s i.val (by omega),ClaudeWCT.W9.T3M.SharedCodec.singletonList,
        getD_append_left' (by simp),getD_ofFn']
    have h2 : (sigDecC (sigBC s)).forest.singleton.path=s.forest.singleton.path := by
      funext i
      change digC (sigBC s) (107+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 107+i.val=101+(6+i.val) by omega,
        ClaudeWCT.W9.T3M.SharedCodec.sigDigests_singleton s (6+i.val) (by omega),ClaudeWCT.W9.T3M.SharedCodec.singletonList,getD_append_right' (by simp),
        List.length_ofFn,Nat.add_sub_cancel_left,getD_ofFn']
    cases h : (sigDecC (sigBC s)).forest.singleton
    cases h' : s.forest.singleton
    simp only [h,h'] at h1 h2
    cases h1;cases h2;rfl
  cases h : (sigDecC (sigBC s)).forest
  cases h' : s.forest
  simp only [h,h'] at hp hs
  cases hp;cases hs;rfl

theorem sigDecC_sigBC (s : ClaudeWCT.W9.T3M.SharedCodec.SharedSignature)
    (h179 : ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests s).getD 179 0).toNat < 2 ^ 109) :
    sigDecC (sigBC s)=fillTopSignature s 0 := by
  have hr : (sigDecC (sigBC s)).rho=s.rho := by
    change digC (sigBC s) 0=s.rho
    rw [digC_sigBC s 0 (by decide),if_neg (by decide),ClaudeWCT.W9.T3M.SharedCodec.sigDigests_rho]
  have hh := policyHints_sigDecC_sigBC s
  have hf := forest_sigDecC_sigBC s
  have hl : (sigDecC (sigBC s)).layers=(fillTopSignature s 0).layers := by
    funext lay
    have hc : ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+chainCount lay≤328 := by fin_cases lay <;> decide
    have hp : ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+chainCount lay+height lay≤328 := by fin_cases lay <;> decide
    have hv : ((sigDecC (sigBC s)).layers lay).values=((fillTopSignature s 0).layers lay).values := by
      funext i
      change digC (sigBC s) (ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+i.val)=(s.layers lay).values i
      have hn : ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+i.val≠179 := by
        fin_cases lay <;> simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx,chainCount] at * <;> omega
      rw [digC_sigBC s _ (by omega),if_neg hn,ClaudeWCT.W9.T3M.SharedCodec.sigDigests_layValue]
    have hpath : ((sigDecC (sigBC s)).layers lay).path=((fillTopSignature s 0).layers lay).path := by
      funext i
      change digC (sigBC s) (ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+chainCount lay+i.val)=(ClaudeWCT.WCT9.fillLayer lay (s.layers lay) 0).path i
      have he : ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+(chainCount lay+i.val)=179 ↔ lay.val=0 ∧ i.val=11 := by
        fin_cases lay <;> simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx,chainCount] at * <;> omega
      rw [show ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+chainCount lay+i.val=ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+(chainCount lay+i.val) by omega,
        digC_sigBC s _ (by omega)]
      rw [ClaudeWCT.W9.T3M.SharedCodec.sigDigests_layPath s lay i.val i.isLt]
      by_cases hq : lay.val=0 ∧ i.val=11
      · have h179' := h179
        rw [← he.mpr hq, ClaudeWCT.W9.T3M.SharedCodec.sigDigests_layPath s lay i.val i.isLt] at h179'
        simp only [he,ClaudeWCT.WCT9.fillLayer,if_pos hq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat,ClaudeWCT.WCT9.setTop_toNat,Nat.mod_eq_of_lt (h179'.trans (by norm_num)),
          Nat.mod_eq_of_lt h179',Nat.mod_eq_of_lt (h179'.trans (by norm_num))]
        simp
      · simp only [he,ClaudeWCT.WCT9.fillLayer,if_neg hq]
    cases h : (sigDecC (sigBC s)).layers lay
    cases h' : (fillTopSignature s 0).layers lay
    simp only [h,h'] at hv hpath
    cases hv;cases hpath;rfl
  have hf' : (sigDecC (sigBC s)).forest=(fillTopSignature s 0).forest := hf
  have hr' : (sigDecC (sigBC s)).rho=(fillTopSignature s 0).rho := hr
  have hh' : (sigDecC (sigBC s)).policyHints=(fillTopSignature s 0).policyHints := hh
  cases h : sigDecC (sigBC s)
  cases h' : fillTopSignature s 0
  simp only [h,h'] at hr' hh' hf' hl
  cases hr';cases hh';cases hf';cases hl;rfl

#print axioms sigDecC_sigBC
end ClaudeWCT.W9.T3M.SharedCodec48

namespace ClaudeWCT.W9.T3M.SharedCodec48
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_eq_of_digits getD_append_left' getD_append_right' getD_ofFn'
 chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem sigDigests_sigDecC (b : CBytes) (k : Nat) (hk : k<328) :
    (ClaudeWCT.W9.T3M.SharedCodec.sigDigests (sigDecC b)).getD k 0=digC b k := by
  by_cases h0:k=0
  · subst h0;exact ClaudeWCT.W9.T3M.SharedCodec.sigDigests_rho _
  by_cases hp:k<101
  · have hq:(k-1)/25<4:=by omega
    let p : Fin 4:=⟨(k-1)/25,hq⟩
    let j : Nat:=(k-1)%25
    have hj:j<25:=Nat.mod_lt _ (by decide)
    have he:k=1+25*p.val+j:=by dsimp [p,j];omega
    rw [he,ClaudeWCT.W9.T3M.SharedCodec.sigDigests_pair _ p j hj]
    by_cases h1:j<6
    · rw [ClaudeWCT.W9.T3M.SharedCodec.pairList_firstValue _ ⟨j,h1⟩]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · by_cases h2:j<12
      · rw [show j=6+(j-6) by omega,ClaudeWCT.W9.T3M.SharedCodec.pairList_firstPath _ ⟨j-6,by omega⟩]
        change digC b _=digC b _
        congr 1 <;> simp only [Fin.val_mk] <;> omega
      · by_cases h3:j<18
        · rw [show j=12+(j-12) by omega,ClaudeWCT.W9.T3M.SharedCodec.pairList_secondValue _ ⟨j-12,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
        · rw [show j=18+(j-18) by omega,ClaudeWCT.W9.T3M.SharedCodec.pairList_secondPath _ ⟨j-18,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
  by_cases hs:k<114
  · have he:k=101+(k-101):=by omega
    rw [he,ClaudeWCT.W9.T3M.SharedCodec.sigDigests_singleton _ (k-101) (by omega)]
    by_cases h1:k-101<6
    · unfold ClaudeWCT.W9.T3M.SharedCodec.singletonList
      rw [getD_append_left' (by simp;omega),getD_ofFn' _ (k-101) h1]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · unfold ClaudeWCT.W9.T3M.SharedCodec.singletonList
      rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ ((k-101)-6) (by omega)]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
  have key:∀ (lay:Layer) (i:Nat),i<chainCount lay+height lay→ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+i=k→
      (ClaudeWCT.W9.T3M.SharedCodec.sigDigests (sigDecC b)).getD k 0=digC b k := by
    intro lay i hi he
    subst he
    rw [ClaudeWCT.W9.T3M.SharedCodec.sigDigests_layer _ lay i hi]
    unfold ClaudeWCT.W9.T3M.SharedCodec.layerList
    by_cases hc:i<chainCount lay
    · rw [getD_append_left' (by simpa using hc),getD_ofFn' _ i hc];rfl
    · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (i-chainCount lay) (by omega)]
      change digC b (ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+chainCount lay+(i-chainCount lay))=_
      congr 1;omega
  by_cases h1:k<180
  · exact key 0 (k-114) (by rw [chainCount_0,height_0];omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
  by_cases h2:k<230
  · exact key 1 (k-180) (by rw [chainCount_1,height_1];omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
  by_cases h3:k<279
  · exact key 2 (k-230) (by rw [chainCount_2,height_2];omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
  · exact key 3 (k-279) (by rw [chainCount_3,height_3];omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)

theorem sigBC_sigDecC (b : CBytes) : sigBC (sigDecC b)=b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigBC_toNat]
  have hD : digNat ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests (sigDecC b)).eraseIdx 179)=b.toNat%2^(128*327) := by
    apply digNat_eq_of_digits
    · rw [ClaudeWCT.W9.T3M.SharedCodec.length_eraseIdx_sig];exact Nat.mod_lt _ (by positivity)
    · intro k hk
      rw [ClaudeWCT.W9.T3M.SharedCodec.length_eraseIdx_sig] at hk
      rw [getD_eraseIdx,mod_digit _ 327 k hk]
      split
      · rename_i hlt
        rw [sigDigests_sigDecC b k (by omega),digC,if_pos hlt,cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
      · rename_i hge
        rw [sigDigests_sigDecC b (k+1) (by omega),digC,if_neg (by omega),if_neg (by omega),
          show k+1-1=k by omega,cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  have hT : ((ClaudeWCT.W9.T3M.SharedCodec.sigDigests (sigDecC b)).getD 179 0).toNat%2^112=b.toNat/2^(128*327)%2^112 := by
    rw [sigDigests_sigDecC b 179 (by decide),digC,if_neg (by decide),if_pos rfl,
      BitVec.toNat_setWidth,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.mod_mod_of_dvd]
    · exact Nat.mod_mod _ _
    · exact Nat.pow_dvd_pow 2 (by decide)
  have hH : (sigDecC b).policyHints.toNat=b.toNat/2^(8*5246) := by
    change (b.extractLsb' (8*5246) 16).toNat=_
    rw [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul (by positivity),←pow_add]
    exact b.isLt
  rw [hD,hT,hH]
  have he : b.toNat/2^(8*5246)=b.toNat/2^(128*327)/2^112 := by
    rw [Nat.div_div_eq_div_mul,←pow_add]
  rw [he,show 2^(8*5246)=2^(128*327)*2^112 by rw [←pow_add]]
  calc
    _=b.toNat%2^(128*327)+2^(128*327)*(b.toNat/2^(128*327)%2^112+
        2^112*(b.toNat/2^(128*327)/2^112)):=by ring
    _=b.toNat%2^(128*327)+2^(128*327)*(b.toNat/2^(128*327)):=by rw [Nat.mod_add_div]
    _=b.toNat:=Nat.mod_add_div _ _
#print axioms sigBC_sigDecC
end ClaudeWCT.W9.T3M.SharedCodec48

namespace ClaudeWCT.W9.T3M.SharedCodec48
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest

-- sigBC_fillTopSignature dropped (V71: 112-bit storage vs 109-bit setTop; unused)
end ClaudeWCT.W9.T3M.SharedCodec48

/-! ## Bridge: the v6 decode is fixed by the 5,248-byte round trip -/
namespace ClaudeWCT.W9.T3M.SharedCodec48
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 (Digest)

theorem setTop_zero_of_lt (d : Digest) (h : d.toNat < 2 ^ 109) : ClaudeWCT.WCT9.setTop d 0 = d := by
  apply BitVec.eq_of_toNat_eq
  rw [ClaudeWCT.WCT9.setTop_toNat, Nat.mod_eq_of_lt h]
  simp

theorem digC179_lt (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    (ClaudeWCT.W9.T3M.SharedCodec.digC b 179).toNat < 2 ^ 109 := by
  unfold ClaudeWCT.W9.T3M.SharedCodec.digC
  rw [if_neg (by omega), if_pos rfl, BitVec.toNat_ofNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 327)) (show 0 < 2 ^ 56 by positivity)
  have h2 := Nat.mod_lt (ClaudeWCT.W9.T3M.SharedCodec.xOfB b) (show 0 < 2 ^ 42 by positivity)
  have h3 : ClaudeWCT.W9.T3M.SharedCodec.xOfB b % 2 ^ 42 * 2 ^ 56 ≤ (2 ^ 42 - 1) * 2 ^ 56 :=
    Nat.mul_le_mul_right _ (by omega)
  refine lt_of_le_of_lt (Nat.mod_le _ _) ?_
  have : (2 ^ 42 - 1) * 2 ^ 56 + 2 ^ 56 < (2 : Nat) ^ 109 := by norm_num
  omega

/-- The v6-decoded signature has its brute-forced top-sibling field clear. -/
theorem fill_sigDecC (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    fillTopSignature (ClaudeWCT.W9.T3M.SharedCodec.sigDecC b) 0 = ClaudeWCT.W9.T3M.SharedCodec.sigDecC b := by
  unfold fillTopSignature
  have hl : (fun lay => ClaudeWCT.WCT9.fillLayer lay ((ClaudeWCT.W9.T3M.SharedCodec.sigDecC b).layers lay) 0) =
      (ClaudeWCT.W9.T3M.SharedCodec.sigDecC b).layers := by
    funext lay
    unfold ClaudeWCT.WCT9.fillLayer
    show _ = (⟨_, _⟩ : SigGolfCandidate.T3.LayerSignature lay)
    congr 1
    funext j
    split
    · rename_i h
      obtain ⟨hl0, hj⟩ := h
      have : lay = 0 := Fin.ext hl0
      subst this
      apply setTop_zero_of_lt
      change (ClaudeWCT.W9.T3M.SharedCodec.digC b
        (ClaudeWCT.W9.T3M.SharedCodec.layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val)).toNat < _
      rw [show ClaudeWCT.W9.T3M.SharedCodec.layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val = 179 by
        simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx, SigGolfCandidate.T3.chainCount, hj]]
      exact digC179_lt b
    · rfl
  rw [hl]

/-- The 5,248-byte encoding of the v6 decode decodes back to it (the expander's pre-pass output). -/
theorem sigDecC_sigBC_v6 (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    sigDecC (sigBC (ClaudeWCT.W9.T3M.SharedCodec.sigDecC b)) = ClaudeWCT.W9.T3M.SharedCodec.sigDecC b := by
  rw [sigDecC_sigBC _ (by
    rw [ClaudeWCT.W9.T3M.SharedCodec.sigDigests_sigDecC b 179 (by decide)]; exact digC179_lt b), fill_sigDecC]

#print axioms sigDecC_sigBC_v6
end ClaudeWCT.W9.T3M.SharedCodec48
