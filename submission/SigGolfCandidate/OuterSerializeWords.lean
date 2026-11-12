import SigGolfCandidate.OuterSerializerCode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSerializeWords
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Research.SharedForest SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedSerializer
theorem serialize_good {im : Image} (hc : OuterSerializer.Code im) (s : MachineState) (hp : s.pc=pcOf 540)
    (sig : SharedSignature) (hraw : RawAt s sig)
-- C13STUB signm R6: final sign theorem: end pc and step bound must be re-derived for C13R (pc 25900; c13 label helper adds steps)
    (hh : s.getMem (BitVec.ofNat 64 417792)=BitVec.ofNat 64 sig.policyHints.toNat)
    (hok : ClaudeWCT.W9.T3M.SharedCodec.HintOK sig.policyHints.toNat) :
    ∃n c,c≤8549 ∧ ∃t,Steps im s n c t ∧ t.pc=pcOf 25963 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t SIG 5186=sigBC sig ∧
      (∀k,k<648→t.getMem (BitVec.ofNat 64 (SIG+8*k))=(sigBC sig).extractLsb' (64*k) 64) ∧
      (t.getMem 33856).extractLsb' 0 16=(sigBC sig).extractLsb' (8*5184) 16 := by
  obtain ⟨n,c,hn,t,st,tp,t5,t10,tw⟩:=OuterSerializer.full_readout hc s hp _ hok hh
  refine ⟨n,c,hn,t,st,tp,t5,t10,?_⟩
  have hr : ∀ j, j<650 → packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))) j=sigWord sig j :=
    fun j hj => packedWord_raw hraw j hj
  have hN : nN (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))) 0)
      (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))) 1) sig.policyHints.toNat=rhoN sig := by
    rw [hr 0 (by omega),hr 1 (by omega)]; exact nN_sig sig
  have hw : ∀ k, k<650 → t.getMem (BitVec.ofNat 64 (SIG+8*k))=packWord (postWord (nWord (sigWord sig) (rhoN sig))
      (Xn (((sigDigests sig).getD 176 0).extractLsb' 64 64) (rhoN sig / 2 ^ 128))) k := by
    intro k hk
    rw [tw k hk,hN,preWord_657 hraw]
    apply packWord_congr _ k hk
    intro j hj
    apply postWord_congr _ _ j hj
    intro i hi
    unfold nWord
    split
    · rfl
    · split
      · rfl
      · exact hr i hi
  refine ⟨?_,?_,?_⟩
  · apply sl_readBuffer_5186 t (sigBC sig)
    · intro k hk
      rw [hw k (by omega)]
      exact enc_word_pack sig k hk
    · rw [hw 648 (by omega)]
      exact enc_word_tail sig _ _
  · intro k hk
    rw [hw k (by omega)]
    exact enc_word_pack sig k hk
  · change (t.getMem (BitVec.ofNat 64 (SIG+8*648))).extractLsb' 0 16=_
    rw [hw 648 (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, enc_word_tail]
    rw [BitVec.extractLsb'_toNat]
    rw [Nat.shiftRight_eq_div_pow]
    change (sigBC sig).toNat / 2^(64*648) = ((sigBC sig).toNat / 2^(64*648)) % 2^16
    exact (Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by simpa only [←Nat.pow_add] using (sigBC sig).isLt))).symm


#print axioms serialize_good
end OuterSerializeWords
