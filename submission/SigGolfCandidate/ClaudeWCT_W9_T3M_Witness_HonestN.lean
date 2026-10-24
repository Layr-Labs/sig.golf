import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Honest
import SigGolfCandidate.W9Drv_FtsCore

/-! # Honest acceptance of the nonce-carrying expand output (`Paired.witEncN`, r3h HonestN)
img-v6: the scheme verifier reads the top node nonces (`verifyTopN w.topNonces`), so the honest expand output is
`witEncN` (nonce pads filled). Main results: `Paired.layersCanonicalBC_witEncN` (retained layer program on
`witEncN` = the scheme's `verifyLayers`), `W9Drv.SharedCanonical.forest_witEncN`, and the read-backs
`Paired.wrho_witEncN` / `wdc_witEncN` / `wtopHigh_witEncN`. -/

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem expandN_fillTopSignature (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    expandN message pk (fillTopSignature sig c)=expandN message pk sig := by
  simp only [expandN,hints_retained,fillTopSignature_fillTopSignature]

theorem expandB_fillTopSignature (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    expandB message pk (fillTopSignature sig c)=expandB message pk sig := by
  rw [expandB,expandB,expandN_fillTopSignature]
end ClaudeWCT.W9.T3M.Paired

/-! The read-back lemmas of the top node nonces (`PairedNonce.noncePos_*`, `witEncN_extract_*`, `wmerklePad_witEncN_*`)
live in `Witness/Honest.lean` (needed there by `Paired.expandN_nonce`). -/


/-! ### HonestN 1: bit-level agreement of `witEncN` with `witEnc` away from the nonce words -/
namespace ClaudeWCT.W9.T3M.PairedNonce
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem witEncN_getLsbD_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (i : Nat)
    (h : ∀ j, j < 11 → i / 8 < noncePos output j ∨ noncePos output j + 8 ≤ i / 8) :
    (witEncN output w).getLsbD i = (Paired.witEnc output w).getLsbD i := by
  by_cases hlt : i < 8 * 22012
  · have e : ∀ x : WBytes, x.getLsbD i = (x.extractLsb' (8 * (i / 8)) (8 * 1)).getLsbD (i % 8) := by
      intro x
      rw [BitVec.getLsbD_extractLsb']
      simp [show i % 8 < 8 * 1 by omega, show 8 * (i / 8) + i % 8 = i by omega]
    rw [e (witEncN output w), e (Paired.witEnc output w), witEncN_extract_free output w (i / 8) 1 (by omega) (by
      intro i' hi1 hi2 j hj
      have := h j hj
      omega)]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

/-- Any window `[off, off + k)` avoiding the 11 nonce words reads the same in `witEncN` and `witEnc`. -/
theorem extract_witEncN_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k m : Nat) (hm : m ≤ 8 * k)
    (h : ∀ j, j < 11 → off + k ≤ noncePos output j ∨ noncePos output j + 8 ≤ off) :
    (witEncN output w).extractLsb' (8 * off) m = (Paired.witEnc output w).extractLsb' (8 * off) m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp only [hi, decide_true, Bool.true_and]
  apply witEncN_getLsbD_free
  intro j hj
  have := h j hj
  omega

theorem extract_witEncN_out (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k m : Nat) (hm : m ≤ 8 * k) (h : off + k ≤ 7696 ∨ 8320 ≤ off) :
    (witEncN output w).extractLsb' (8 * off) m = (Paired.witEnc output w).extractLsb' (8 * off) m := by
  apply extract_witEncN_free output w off k m hm
  intro j hj
  have := noncePos_bounds output j hj
  omega

theorem wdig_witEncN_out (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : off + 16 ≤ 7696 ∨ 8320 ≤ off) :
    wdig (witEncN output w) off = wdig (Paired.witEnc output w) off :=
  extract_witEncN_out output w off 16 128 (by omega) h

theorem wdig_witEncN_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : ∀ j, j < 11 → off + 16 ≤ noncePos output j ∨ noncePos output j + 8 ≤ off) :
    wdig (witEncN output w) off = wdig (Paired.witEnc output w) off :=
  extract_witEncN_free output w off 16 128 (by omega) h

theorem wdig_witEnc_legacy (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (ho : 7664 ≤ off) (hc : off + 16 ≤ choiceOff ∨ choiceOff < off) :
    wdig (Paired.witEnc output w) off = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) off := by
  rw [PairedReadout.wdig_witEnc_base output w off hc]
  exact PairedReadout.wdig_prefixEnc (forestBytes output w) (forestBytes_length output w)
    output (mainWitness w) off ho

theorem wdig_N_legacy_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (ho : 7664 ≤ off) (hc : off + 16 ≤ choiceOff ∨ choiceOff < off)
    (h : ∀ j, j < 11 → off + 16 ≤ noncePos output j ∨ noncePos output j + 8 ≤ off) :
    wdig (witEncN output w) off = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) off := by
  rw [wdig_witEncN_free output w off h, wdig_witEnc_legacy output w off ho hc]

theorem wdig_N_legacy_hi (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (ho : 8320 ≤ off) (hc : off + 16 ≤ choiceOff ∨ choiceOff < off) :
    wdig (witEncN output w) off = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) off := by
  rw [wdig_witEncN_out output w off (Or.inr ho), wdig_witEnc_legacy output w off (by omega) hc]
end ClaudeWCT.W9.T3M.PairedNonce

/-! ### HonestN 2: read-backs outside the nonce area -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.PairedNonce
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

@[simp] theorem wtopHigh_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wtopHigh (witEncN output w) = w.topHigh := by
  rw [← PairedReadout.wtopHigh_witEnc output w]
  unfold wtopHigh wchoice
  rw [extract_witEncN_out output w choiceOff 1 8 (by omega) (Or.inr (by unfold choiceOff; omega))]
end ClaudeWCT.W9.T3M.Paired

/-! ### HonestN 3: the top path windows avoid the nonce words
Slots of one leaf's top plan: a level-`j` window occupies slots `s_j .. s_j + 3` (`left | tweak | Z pad | right`);
the nonce of level `j'` is the low half of slot `s_j' + 2`. Only the level-`j` Z pad (`j < 11`) meets a nonce. -/
namespace ClaudeWCT.W9.T3M.PairedNonce
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem topPlanA_free0 : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 ≠ (topPlanA.getD r []).getD j' 0 + 2 := by decide
theorem topPlanA_free1 : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 + 1 ≠ (topPlanA.getD r []).getD j' 0 + 2 := by decide
theorem topPlanA_free3 : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 + 3 ≠ (topPlanA.getD r []).getD j' 0 + 2 := by decide
theorem topPlanB_free0 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 ≠ (topPlanB.getD r []).getD k' 0 + 2 := by decide
theorem topPlanB_free1 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 + 1 ≠ (topPlanB.getD r []).getD k' 0 + 2 := by decide
theorem topPlanB_free3 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 + 3 ≠ (topPlanB.getD r []).getD k' 0 + 2 := by decide
theorem topPlanB_inj6 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 = (topPlanB.getD r []).getD k' 0 → k = k' := by decide
theorem topPlanA_free (r : Nat) (hr : r < 64) (j : Nat) (hj : j < 6) (j' : Nat) (hj' : j' < 6) (s : Nat) (hs : s < 4)
    (h : (topPlanA.getD r []).getD j 0 + s = (topPlanA.getD r []).getD j' 0 + 2) : j = j' ∧ s = 2 := by
  have h0 := topPlanA_free0 r hr j hj j' hj'
  have h1 := topPlanA_free1 r hr j hj j' hj'
  have h3 := topPlanA_free3 r hr j hj j' hj'
  have hs2 : s = 2 := by omega
  subst hs2
  exact ⟨topPlanA_inj r hr j hj j' hj' (by omega), rfl⟩
theorem topPlanB_free (r : Nat) (hr : r < 64) (k : Nat) (hk : k < 6) (k' : Nat) (hk' : k' < 5) (s : Nat) (hs : s < 4)
    (h : (topPlanB.getD r []).getD k 0 + s = (topPlanB.getD r []).getD k' 0 + 2) : k = k' ∧ s = 2 := by
  have h0 := topPlanB_free0 r hr k hk k' hk'
  have h1 := topPlanB_free1 r hr k hk k' hk'
  have h3 := topPlanB_free3 r hr k hk k' hk'
  have hs2 : s = 2 := by omega
  subst hs2
  exact ⟨topPlanB_inj6 r hr k hk k' hk' (by omega), rfl⟩
theorem topPlanB_bounds6 : ∀ r, r < 64 → ∀ k, k < 6 → (topPlanB.getD r []).getD k 0 ≤ 16 := by decide

theorem slot_free (leaf j j' s : Nat) (hj : j < 12) (hj' : j' < 11) (hs : s < 4)
    (h : topPlanSlot leaf j + s = topPlanSlot leaf j' + 2) : j = j' ∧ s = 2 := by
  have hr1 : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr2 : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold topPlanSlot at h
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · rw [if_pos h6, if_pos h6'] at h
    exact topPlanA_free _ hr1 j h6 j' h6' s hs h
  · rw [if_pos h6, if_neg h6'] at h
    have := (topPlanA_bounds _ hr1 j h6).1
    have := topPlanB_bounds _ hr2 (j' - 6) (by omega)
    omega
  · rw [if_neg h6, if_pos h6'] at h
    have := (topPlanA_bounds _ hr1 j' h6').1
    have := topPlanB_bounds6 _ hr2 (j - 6) (by omega)
    omega
  · rw [if_neg h6, if_neg h6'] at h
    have := topPlanB_free _ hr2 (j - 6) (by omega) (j' - 6) (by omega) s hs h
    omega

theorem merkleBlock_top (leaf j : Nat) : merkleBlock 0 leaf j = 7664 + 16 * topPlanSlot leaf j := by
  unfold merkleBlock
  rw [if_pos (show (0 : Layer).val = 0 from rfl)]
  rfl

/-- Slot `s` (`< 4`) of the level-`j` top window is nonce-free unless it is a nonce-carrying Z pad. -/
theorem top_window_free (output : HashOutput) (j s : Nat) (hj : j < 12) (hs : s < 4) (hne : ¬ (j < 11 ∧ s = 2)) :
    ∀ j', j' < 11 → merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s + 16 ≤ noncePos output j' ∨
      noncePos output j' + 8 ≤ merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s := by
  intro j' hj'
  rw [noncePos_eq, merkleBlock_top]
  by_cases he : topPlanSlot (route (WCT9.digestIndex output) 0).1 j + s =
      topPlanSlot (route (WCT9.digestIndex output) 0).1 j' + 2
  · obtain ⟨h1, h2⟩ := slot_free _ j j' s hj hj' hs he
    exact absurd ⟨by omega, h2⟩ hne
  · omega

theorem topPlanSlot_le (leaf j : Nat) (hj : j < 12) : topPlanSlot leaf j ≤ 38 := by
  have hr1 : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr2 : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold topPlanSlot
  split_ifs with h6
  · exact (topPlanA_bounds _ hr1 j h6).2
  · have := topPlanB_bounds6 _ hr2 (j - 6) (by omega); omega

/-- The reads of a top window slot agree with the legacy encoding. -/
theorem top_slot_legacy (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j s : Nat) (hj : j < 12) (hs : s < 4) (hne : ¬ (j < 11 ∧ s = 2)) :
    wdig (witEncN output w) (merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s) =
      wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s) := by
  have hb := topPlanSlot_le (route (WCT9.digestIndex output) 0).1 j hj
  have hm := merkleBlock_top (route (WCT9.digestIndex output) 0).1 j
  apply wdig_N_legacy_free output w _ (by omega) (Or.inl (by unfold choiceOff; omega))
  have := top_window_free output j s hj hs hne
  intro j' hj'
  have := this j' hj'
  omega

theorem wpath_top_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat) (hj : j < 12) :
    wpath (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j =
      wpath (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) 0 (route (WCT9.digestIndex output) 0).1 j := by
  unfold wpath SigGolfCandidate.T3M.sibOff
  split_ifs
  · have := top_slot_legacy output w j 0 hj (by decide) (by omega)
    simpa using this
  · have := top_slot_legacy output w j 3 hj (by decide) (by omega)
    simpa using this

theorem wmerkleHigh_top_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat)
    (hj : j < 12) :
    wmerkleHigh (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j =
      wmerkleHigh (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) 0 (route (WCT9.digestIndex output) 0).1 j := by
  unfold wmerkleHigh
  have := top_slot_legacy output w j 1 hj (by decide) (by omega)
  simp only [Nat.mul_one] at this
  rw [this]

theorem wmerklePad_root_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 11 =
      wmerklePad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) 0 (route (WCT9.digestIndex output) 0).1 11 := by
  unfold wmerklePad
  have := top_slot_legacy output w 11 2 (by decide) (by decide) (by omega)
  simpa using this

/-- The level-`j` (`j < 11`) top Z pad of `witEncN` is the nonce `nonces.getD j 0 mod 2^64`. -/
theorem wmerklePad_top_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat)
    (hj : j < 11) :
    wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j =
      BitVec.ofNat 128 (w.topNonces.getD j 0 % 2 ^ 64) := by
  have hlo := wmerklePad_witEncN_lo output w j hj
  have hhi := wmerklePad_witEncN_hi output w j hj
  generalize wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j = d at hlo hhi ⊢
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hlo
  have h2 := congrArg BitVec.toNat hhi
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero,
    Nat.div_one, BitVec.toNat_zero] at h1 h2
  have hd := d.isLt
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at h1 h2 hd hz ⊢
  omega

/-! ### HonestN 4: retained layer reads away from the top path windows -/

theorem chainBlock_ge (lay : Layer) (i : Nat) : 8336 ≤ chainBlock lay i := by
  have : 8336 ≤ layerBase lay + 16 * pathSlots lay := by fin_cases lay <;> decide
  unfold chainBlock; omega

theorem chain_fields_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    (∀ i, wchainPads (witEncN output w) lay i = wchainPads (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i) ∧
    (∀ i, wchainHeaderPad (witEncN output w) lay i = wchainHeaderPad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i) ∧
    (∀ i, wvalue (witEncN output w) lay i = wvalue (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i) ∧
    (∀ i, i < chainCount lay →
      wdig (witEncN output w) (leafBufferSlot lay i) = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (leafBufferSlot lay i)) ∧
    (∀ digits i, i < chainCount lay →
      wvalueFor (witEncN output w) lay digits i = wvalueFor (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay digits i) := by
  have hc : ∀ i x, x ≤ 48 → wdig (witEncN output w) (chainBlock lay i + x) =
      wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (chainBlock lay i + x) := by
    intro i x hx
    have := chainBlock_le lay i
    have := chainBlock_ge lay i
    exact wdig_N_legacy_hi output w _ (by omega) (Or.inl (by unfold choiceOff; omega))
  have hb : ∀ i, i < chainCount lay →
      wdig (witEncN output w) (leafBufferSlot lay i) = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (leafBufferSlot lay i) := by
    intro i hi
    have hch := leafBufferSlot_choice lay i hi
    have h8 : 8320 ≤ leafBufferSlot lay i := by
      have : 8320 ≤ leafBufferBase lay := by fin_cases lay <;> decide
      unfold leafBufferSlot; split_ifs <;> omega
    exact wdig_N_legacy_hi output w _ h8 hch.1
  have hv : ∀ i, wvalue (witEncN output w) lay i = wvalue (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i := by
    intro i
    unfold wvalue
    exact hc i _ (by unfold valueOff; split_ifs <;> omega)
  refine ⟨?_, ?_, hv, hb, ?_⟩
  · intro i
    unfold wchainPads
    rw [hc i _ (by unfold pad0Off; split_ifs <;> omega), hc i _ (by unfold pad1Off; split_ifs <;> omega)]
  · intro i
    unfold wchainHeaderPad
    rw [hc i 16 (by omega)]
  · intro digits i hi
    unfold wvalueFor
    split
    · exact hb i hi
    · exact hv i

theorem merkleBlock_lower_ge (lay : Layer) (hl : lay ≠ 0) (leaf j : Nat) : 11144 ≤ merkleBlock lay leaf j := by
  have : 11144 ≤ layerBase lay := by
    fin_cases lay
    · exact absurd rfl hl
    all_goals decide
  unfold merkleBlock; omega

theorem merkle_fields_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer)
    (hl : lay ≠ 0) :
    (∀ leaf j, wpath (witEncN output w) lay leaf j = wpath (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay leaf j) ∧
    (∀ leaf j, wmerklePad (witEncN output w) lay leaf j = wmerklePad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay leaf j) ∧
    (∀ leaf j, wmerkleHigh (witEncN output w) lay leaf j = wmerkleHigh (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay leaf j) := by
  have hm : ∀ leaf j x, x ≤ 48 → wdig (witEncN output w) (merkleBlock lay leaf j + x) =
      wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (merkleBlock lay leaf j + x) := by
    intro leaf j x hx
    have := PairedReadout.merkleBlock_le lay leaf j
    have := merkleBlock_lower_ge lay hl leaf j
    exact wdig_N_legacy_hi output w _ (by omega) (Or.inl (by unfold choiceOff; omega))
  refine ⟨?_, ?_, ?_⟩
  · intro leaf j
    unfold wpath
    exact hm leaf j _ (by unfold SigGolfCandidate.T3M.sibOff; split_ifs <;> omega)
  · intro leaf j
    unfold wmerklePad
    exact hm leaf j 32 (by omega)
  · intro leaf j
    unfold wmerkleHigh
    rw [hm leaf j 16 (by omega)]

theorem wtopLeafPad_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wtopLeafPad (witEncN output w) = wtopLeafPad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) := by
  unfold wtopLeafPad
  exact wdig_N_legacy_hi output w _ (by decide) (Or.inl (by decide))

theorem wleafHigh_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wleafHigh (witEncN output w) lay = wleafHigh (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay := by
  have hl : 8320 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hw : leafBufferBase lay + 16 + 8 + 8 ≤ choiceOff ∨ choiceOff < leafBufferBase lay + 16 + 8 := by
    fin_cases lay <;> decide
  unfold wleafHigh
  rw [PairedReadout.wdig_hi_extract, PairedReadout.wdig_hi_extract,
    extract_witEncN_out output w (leafBufferBase lay + 16 + 8) 8 (8 * 8) le_rfl (Or.inr (by omega)),
    PairedReadout.witEnc_extract output w _ _ hw]
  exact PairedReadout.word_prefixEnc (forestBytes output w) (forestBytes_length output w)
    output (mainWitness w) _ (by omega)

theorem layerPairP_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) :
    layerPairP (witEncN output w) index lay digits = layerPairP (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) index lay digits := by
  obtain ⟨hcp, hh, -, -, hvf⟩ := chain_fields_N output w lay
  obtain ⟨hp, hm, hmh⟩ := merkle_fields_N output w lay hl
  have hv : ∀ i : Fin (chainCount lay), wvalueFor (witEncN output w) lay digits i.val =
      wvalueFor (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay digits i.val := fun i => hvf digits i.val i.isLt
  simp only [layerPairP, hcp, hh, hv, hp, hm, hmh, wtopLeafPad_N, wleafHigh_N]

theorem layerGuardedPairP_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (lay : Layer) (hl : lay ≠ 0) (answer : Digest) (digits : List Nat) :
    layerGuardedPairP (witEncN output w) index lay answer digits =
      layerGuardedPairP (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) index lay answer digits := by
  obtain ⟨hcp, hh, -, -, hvf⟩ := chain_fields_N output w lay
  have hpos : 0 < chainCount lay := by fin_cases lay <;> decide
  have hc : layerChainP (witEncN output w) index lay digits = layerChainP (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) index lay digits := by
    funext i
    simp only [layerChainP, hcp, hh, hvf digits (i % chainCount lay) (Nat.mod_lt _ hpos)]
  simp only [layerGuardedPairP, hc, layerPairP_N output w index lay hl]

theorem rowBlock_out (index : Nat) (lay : Layer) : rowBlock index lay = 0 ∨ 11144 ≤ rowBlock index lay := by
  unfold rowBlock
  split
  · exact Or.inl rfl
  · rename_i h3
    right
    apply merkleBlock_lower_ge
    revert h3
    fin_cases lay <;> decide

theorem wbcCtr_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wbcCtr (witEncN output w) (WCT9.digestIndex output) lay = w.counters lay := by
  rw [← Paired.wbcCtr_witEnc output w lay]
  unfold wbcCtr wle32 bcCounterOff
  exact extract_witEncN_out output w _ 4 32 (by omega) (by
    rcases rowBlock_out (WCT9.digestIndex output) lay with h | h <;> omega)
theorem wbcPad_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wbcPad (witEncN output w) (WCT9.digestIndex output) lay = 0 := by
  rw [← Paired.wbcPad_witEnc output w lay]
  unfold wbcPad bcCounterOff
  exact extract_witEncN_out output w _ 12 96 (by omega) (by
    rcases rowBlock_out (WCT9.digestIndex output) lay with h | h <;> omega)
theorem wbcHigh_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wbcHigh (witEncN output w) (WCT9.digestIndex output) lay = 1 := by
  rw [← Paired.wbcHigh_witEnc output w lay]
  unfold wbcHigh
  rw [wdig_witEncN_out output w (rowBlock (WCT9.digestIndex output) lay + 16)
    (by rcases rowBlock_out (WCT9.digestIndex output) lay with h | h <;> omega)]
end ClaudeWCT.W9.T3M.PairedNonce

/-! ### HonestN 5: the top layer on nonce pads is `verifyTopN` -/
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Honest pads of a nonce-carrying witness: all zero except the top Z pads of levels `< 11` (the nonces). -/
def noncePads (nonces : List Nat) : Pads :=
  { (0 : Pads) with merkle := fun lay j =>
      if lay.val = 0 ∧ j.val < 11 then BitVec.ofNat 128 (nonces.getD j.val 0 % 2 ^ 64) else 0 }

@[simp] theorem noncePads_chain (n : List Nat) (lay : Layer) (i : Fin (chainCount lay)) :
    (noncePads n).chain lay i = (0, 0) := rfl
@[simp] theorem noncePads_chainHeader (n : List Nat) (lay : Layer) (i : Fin (chainCount lay)) :
    (noncePads n).chainHeader lay i = 0 := rfl
@[simp] theorem noncePads_endpointMask (n : List Nat) (lay : Layer) (i : Fin (chainCount lay)) :
    (noncePads n).endpointMask lay i = 0 := rfl
@[simp] theorem noncePads_merkleHigh (n : List Nat) (lay : Layer) (j : Fin (height lay)) :
    (noncePads n).merkleHigh lay j = 0 := rfl
@[simp] theorem noncePads_topLeaf (n : List Nat) : (noncePads n).topLeaf = 0 := rfl
@[simp] theorem noncePads_leafHigh (n : List Nat) (lay : Layer) : (noncePads n).leafHigh lay = 0 := rfl
theorem noncePads_merkle (n : List Nat) (lay : Layer) (j : Fin (height lay)) :
    (noncePads n).merkle lay j =
      if lay.val = 0 ∧ j.val < 11 then BitVec.ofNat 128 (n.getD j.val 0 % 2 ^ 64) else 0 := rfl

theorem valueP_noncePads (sig : WCT9.Signature) (n : List Nat) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) : valueP sig (noncePads n) lay digits i = (sig.layers lay).values i := by
  unfold valueP
  split
  · rw [noncePads_endpointMask]; exact BitVec.xor_zero
  · rfl

/-- A top node hash with the nonce in its Z pad is `T3.topNodeHashN`. -/
theorem lowerNodeHashP_nonce (heap n : Nat) (left right : Digest) :
    WCT9.lowerNodeHashP 0 0 heap left 0 (BitVec.ofNat 128 (n % 2 ^ 64)) right =
      SigGolfCandidate.T3.topNodeHashN heap n left right := by
  unfold WCT9.lowerNodeHashP WCT9.lowerHash WCT9.lowerNodeInputP SigGolfCandidate.T3.topNodeHashN
    SigGolfCandidate.T3.topNodeInput SigGolfCandidate.T3.nonceBytes
  rw [WCT9.lowerHigh_top_eq_nodeHalfHigh, WCT9.halfHash_eq_projHash,
    show ((0 : BitVec 64) ++ WCT9.merkleWord 0 0 heap) = WCT9.merkleTweak 0 0 heap from
      (WCT9.merkleTweak_eq_word 0 0 heap).symm, WCT9.merkleTweak_top]

theorem route_top_tree (index : Nat) (hindex : index < 2 ^ 31) : (route index 0).2 = 0 := by
  simp only [route, height, Matrix.cons_val_zero]
  exact Nat.div_eq_of_lt (lt_of_lt_of_eq hindex (by norm_num))

theorem topFold_noncePads (n : List Nat) (index : Nat) (hindex : index < 2 ^ 31) (j : Fin (height 0))
    (heap : Nat) (left right : Digest) :
    WCT9.lowerNodeHashP (0 : Layer).val (route index 0).2 heap left ((noncePads n).merkleHigh 0 j)
        ((noncePads n).merkle 0 j) right =
      if j.val < 11 then SigGolfCandidate.T3.topNodeHashN heap (n.getD j.val 0) left right
      else SigGolfCandidate.T3.nodeHash 3 (0 : Layer).val (route index 0).2 heap left right := by
  rw [noncePads_merkleHigh, noncePads_merkle]
  by_cases h2 : j.val < 11
  · rw [if_pos ⟨rfl, h2⟩, if_pos h2, route_top_tree index hindex]
    exact lowerNodeHashP_nonce heap _ left right
  · rw [if_neg (fun h => h2 h.2), if_neg h2]
    exact (WCT9.lowerNodeHash_eqP' 0 _ heap left right).symm.trans (WCT9.lowerNodeHash_top _ heap left right)

theorem verifyTopP_noncePads (sig : WCT9.Signature) (n : List Nat) (index : Nat) (answer : Digest)
    (hindex : index < 2 ^ 31) :
    verifyTopP sig (noncePads n) index answer = WCT9.verifyTopN sig n index answer := by
  simp only [verifyTopP, WCT9.verifyTopN, noncePads_chain, noncePads_chainHeader, valueP_noncePads,
    chainPW_zero_top _ _ _ _ hindex, noncePads_topLeaf, noncePads_leafHigh, leafHashW_zero,
    WCT9.lowerLeafHash_top, topFold_noncePads n index hindex]

/-- `verifyTopP` reads only the top layer's signature part and the top pads. -/
theorem verifyTopP_congr (sig sig' : WCT9.Signature) (pads pads' : Pads) (index : Nat) (answer : Digest)
    (hl : sig.layers 0 = sig'.layers 0)
    (hc : ∀ i, pads.chain 0 i = pads'.chain 0 i)
    (hch : ∀ i, pads.chainHeader 0 i = pads'.chainHeader 0 i)
    (hm : ∀ i, pads.endpointMask 0 i = pads'.endpointMask 0 i)
    (ht : pads.topLeaf = pads'.topLeaf)
    (hlh : pads.leafHigh 0 = pads'.leafHigh 0)
    (hmh : ∀ j, pads.merkleHigh 0 j = pads'.merkleHigh 0 j)
    (hmk : ∀ j, pads.merkle 0 j = pads'.merkle 0 j) :
    verifyTopP sig pads index answer = verifyTopP sig' pads' index answer := by
  simp only [verifyTopP, valueP, hl, hc, hch, hm, ht, hlh, hmh, hmk]

/-- Interface for the security side (r3-lean-nonsec, any witness bytes): a top verifier whose pads are zero except the
level-`j < 11` Z pads `BitVec.ofNat 128 (n_j % 2^64)` (= `WCT9.nonceDigest n_j`) is the nonce-reading `verifyTopN`. -/
theorem verifyTopP_eq_verifyTopN (sig : WCT9.Signature) (pads : Pads) (n : List Nat) (index : Nat) (answer : Digest)
    (hindex : index < 2 ^ 31)
    (hc : ∀ i, pads.chain 0 i = (0, 0)) (hch : ∀ i, pads.chainHeader 0 i = 0) (hm : ∀ i, pads.endpointMask 0 i = 0)
    (ht : pads.topLeaf = 0) (hlh : pads.leafHigh 0 = 0) (hmh : ∀ j, pads.merkleHigh 0 j = 0)
    (hmk : ∀ j : Fin (height 0), pads.merkle 0 j =
      if j.val < 11 then BitVec.ofNat 128 (n.getD j.val 0 % 2 ^ 64) else 0) :
    verifyTopP sig pads index answer = WCT9.verifyTopN sig n index answer := by
  rw [← verifyTopP_noncePads sig n index answer hindex]
  apply verifyTopP_congr sig sig pads (noncePads n) index answer rfl hc hch hm ht hlh hmh
  intro j
  rw [hmk j, noncePads_merkle]
  simp only [Fin.val_zero, true_and]

/-- The same on witness bytes: the retained top layer of any witness whose decoded top pads are the nonce pads. -/
theorem topLayerP_eq_verifyTopN (N : HashOutput) (w : WBytes) (n : List Nat) (answer : Digest)
    (hc : ∀ i, (padDecP N w).chain 0 i = (0, 0)) (hch : ∀ i, (padDecP N w).chainHeader 0 i = 0)
    (hm : ∀ i, (padDecP N w).endpointMask 0 i = 0) (ht : (padDecP N w).topLeaf = 0)
    (hlh : (padDecP N w).leafHigh 0 = 0) (hmh : ∀ j, (padDecP N w).merkleHigh 0 j = 0)
    (hmk : ∀ j : Fin (height 0), (padDecP N w).merkle 0 j =
      if j.val < 11 then BitVec.ofNat 128 (n.getD j.val 0 % 2 ^ 64) else 0) :
    topLayerP w (WCT9.digestIndex N) answer =
      WCT9.verifyTopN (witDecP N w).signature n (WCT9.digestIndex N) answer := by
  rw [topLayerP_dec N w]
  exact verifyTopP_eq_verifyTopN _ _ n _ answer (WCT9.digestIndex_lt N) hc hch hm ht hlh hmh hmk
end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M.PairedNonce
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layerSig_ext {lay : Layer} (s t : SigGolfCandidate.T3.LayerSignature lay) (h1 : s.values = t.values)
    (h2 : s.path = t.path) : s = t := by
  cases s; cases t; cases h1; cases h2; rfl

/-- The retained top layer on `witEncN` is the scheme's nonce-reading top verifier. -/
theorem topLayerP_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (answer : Digest) :
    topLayerP (witEncN output w) (WCT9.digestIndex output) answer =
      WCT9.verifyTopN (mainWitness w).signature w.topNonces (WCT9.digestIndex output) answer := by
  have hz := ClaudeWCT.W9.T3M.padDecP_witEnc output (mainWitness w)
  have hd := ClaudeWCT.W9.T3M.witDecP_witEnc output (mainWitness w)
  obtain ⟨hcp, hh, hv, hb, -⟩ := chain_fields_N output w 0
  have hj12 : ∀ j : Fin (height (0 : Layer)), j.val < 12 := fun j => j.isLt
  rw [topLayerP_dec output, ← verifyTopP_noncePads _ w.topNonces _ answer (WCT9.digestIndex_lt output)]
  apply verifyTopP_congr
  · rw [← hd]
    apply layerSig_ext
    · funext i; simp only [witDecP]; exact hv i.val
    · funext j; simp only [witDecP]; exact wpath_top_N output w j.val (hj12 j)
  · intro i
    rw [show (noncePads w.topNonces).chain 0 i = (0 : Pads).chain 0 i from rfl, ← hz]
    simp only [padDecP]
    exact hcp i.val
  · intro i
    rw [show (noncePads w.topNonces).chainHeader 0 i = (0 : Pads).chainHeader 0 i from rfl, ← hz]
    simp only [padDecP]
    exact hh i.val
  · intro i
    rw [show (noncePads w.topNonces).endpointMask 0 i = (0 : Pads).endpointMask 0 i from rfl, ← hz]
    simp only [padDecP]
    rw [hv i.val, hb i.val i.isLt]
  · rw [show (noncePads w.topNonces).topLeaf = (0 : Pads).topLeaf from rfl, ← hz]
    simp only [padDecP]
  · rw [show (noncePads w.topNonces).leafHigh 0 = (0 : Pads).leafHigh 0 from rfl, ← hz]
    simp only [padDecP]
    exact wleafHigh_N output w 0
  · intro j
    rw [show (noncePads w.topNonces).merkleHigh 0 j = (0 : Pads).merkleHigh 0 j from rfl, ← hz]
    simp only [padDecP]
    rw [wmerkleHigh_top_N output w j.val (hj12 j)]
  · intro j
    rw [noncePads_merkle]
    simp only [padDecP]
    by_cases hj : j.val < 11
    · simp only [Fin.val_zero, or_true, true_and, hj, ↓reduceIte]
      exact wmerklePad_top_N output w j.val hj
    · have hj11 : j.val = 11 := by have := hj12 j; omega
      have h0 := congrArg (fun p : Pads => p.merkle 0 j) hz
      simp only [padDecP] at h0
      simp only [Fin.val_zero, or_true, true_and, hj, ↓reduceIte] at h0 ⊢
      rw [hj11, wmerklePad_root_N output w, ← hj11]
      exact h0

end ClaudeWCT.W9.T3M.PairedNonce

/-! ### HonestN 6: the retained layers on `witEncN` are the scheme's `verifyLayers` -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.PairedNonce
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layersCanonicalBCH_witEncN (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) : ∀ n, n ≤ 4 → ∀ left right,
    layersCanonicalBCH w.topHigh (witEncN output w) (WCT9.digestIndex output) n (.pair left right) =
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) n (.pair left right) := by
  intro n
  induction n with
  | zero => intro _ left right; rfl
  | succ n ih =>
    intro hn left right
    have hguard : n ≠ 0 → ∀ answer digits,
        layerGuardedPairP (witEncN output w) (WCT9.digestIndex output) (Fin.ofNat 4 n) answer digits =
        WCT9.recoverLayerPairGuard (mainWitness w).signature (WCT9.digestIndex output)
          (Fin.ofNat 4 n) answer digits := by
      intro h0 answer digits
      have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := by
        intro e; have := congrArg Fin.val e; simp [Fin.val_ofNat] at this; omega
      rw [layerGuardedPairP_N output w _ _ hlay, layerGuardedPairP_dec output,
        ClaudeWCT.W9.T3M.witDecP_witEnc, ClaudeWCT.W9.T3M.padDecP_witEnc]
      exact recoverLayerPairGuardP_zero _ _ _ _ _ (WCT9.digestIndex_lt output) hlay
    by_cases h0 : n = 0
    · simp only [layersCanonicalBCH, SigGolfCandidate.Research.SharedForest.verifyLayers,
        wbcCtr_witEncN, wbcPad_witEncN, wbcHigh_witEncN, topLayerP_witEncN,
        layerEncodingInputP, WCT9.layerEncodingInput, WCT9.pairEncodingInputH_one, h0, ↓reduceIte]
      rfl
    · simp only [layersCanonicalBCH, SigGolfCandidate.Research.SharedForest.verifyLayers,
        wbcCtr_witEncN, wbcPad_witEncN, wbcHigh_witEncN, hguard h0,
        ih (by omega), layerEncodingInputP, WCT9.layerEncodingInput, WCT9.pairEncodingInputH_one, h0, ↓reduceIte]
      rfl

/-- Honest acceptance on the nonce-carrying encoding: the retained layer program on `witEncN` is the scheme's. -/
theorem layersCanonicalBC_witEncN (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (n : Nat) (left right : Digest) (hn : n ≤ 4) :
    layersCanonicalBC (witEncN output w) (WCT9.digestIndex output) n (.pair left right) =
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) n (.pair left right) := by
  rw [layersCanonicalBC_eq_H, wtopHigh_witEncN]
  exact layersCanonicalBCH_witEncN output w n hn left right
end ClaudeWCT.W9.T3M.Paired

/-! ### HonestN 7: the FTS forest reads only bytes below 7696 -/
namespace W9Drv.SharedCanonical
open W9Machine SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3M.PairedNonce
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wdigM_witEncN_low (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : off + 16 ≤ 7696) :
    W9Machine.wdig (Paired.witEncN output w) off = W9Machine.wdig (Paired.witEnc output w) off :=
  wdig_witEncN_out output w off (Or.inl h)

theorem regionOffset_le (k : Fin 9) : V3.regionOffset k.val ≤ 6864 := by
  have := k.isLt; unfold V3.regionOffset; omega

theorem chainReadout_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (word : Rank) (values : Fin 6 → Digest)
    (h : ChainReadout (Paired.witEnc output w) k word values) :
    ChainReadout (Paired.witEncN output w) k word values := by
  have hr := regionOffset_le k
  refine ⟨fun i => Eq.trans ?_ (h.padA i), fun i => Eq.trans ?_ (h.padB i), fun i => Eq.trans ?_ (h.padC i),
    fun i => Eq.trans ?_ (h.reveal i)⟩
  · have hb := PairedReadout.chain_field_bound i
    unfold V3.chainPadA V3.chainOffset
    exact wdigM_witEncN_low output w _ (by omega)
  · have hb := PairedReadout.chain_field_bound i
    unfold V3.chainPadB V3.chainOffset
    exact extract_witEncN_out output w _ 8 64 le_rfl (Or.inl (by omega))
  · have hb := PairedReadout.chain_field_bound i
    unfold V3.chainPadC V3.chainOffset
    exact wdigM_witEncN_low output w _ (by omega)
  · have hb := PairedReadout.chain_field_bound i
    have hi := i.isLt
    unfold V3.reveal V3.chainOffset
    split_ifs
    · exact wdigM_witEncN_low output w _ (by unfold V3.leafSlot; split_ifs <;> omega)
    · exact wdigM_witEncN_low output w _ (by
        have : ClaudeWCT.W9.T3M.wctValueOff i.val ≤ 48 := by
          unfold ClaudeWCT.W9.T3M.wctValueOff; split_ifs <;> omega
        omega)

theorem blkOff_bound (k : Fin 9) (c : Nat) (hc : c < 128) (l : Nat) (hl : l ≤ SharedV3.lastLevel k.val) :
    V3.regionOffset k.val + SharedV3.blkOff c l + 64 ≤ 7696 := by
  have hr := regionOffset_le k
  unfold SharedV3.blkOff
  split_ifs with h5
  · have : SigGolfCandidate.Research.SharedPathPacking.block c l + 64 ≤ 640 := PairedReadout.block_bound ⟨c, hc⟩ l h5
    omega
  · have hl5 : l = 5 := by unfold SharedV3.lastLevel at hl; split_ifs at hl <;> omega
    have hk : k.val ≠ 0 := by
      intro hk; rw [hk] at hl; unfold SharedV3.lastLevel SharedV3.first at hl; simp at hl; omega
    have := k.isLt
    unfold V3.regionOffset at hr ⊢
    omega

theorem pathReadout_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (raw : Child) (path : Nat → Digest)
    (h : PathReadout (Paired.witEnc output w) k raw path) :
    PathReadout (Paired.witEncN output w) k raw path := by
  have hc := SharedV3.physical_lt k.val raw.val raw.isLt
  have hr := regionOffset_le k
  refine ⟨fun l hl => Eq.trans ?_ (h.headerPads l hl), fun l hl hne => Eq.trans ?_ (h.nodePads l hl hne),
    fun l hl => Eq.trans ?_ (h.siblings l hl), Eq.trans ?_ h.topOther⟩
  · unfold SharedV3.nodeHPad SharedV3.nodeTw
    have := blkOff_bound k _ hc l hl
    split_ifs
    all_goals first
      | exact congrArg (fun d : Digest => d.extractLsb' 64 64) (wdigM_witEncN_low output w _ (by omega))
      | rfl
  · unfold SharedV3.nodePad
    have := blkOff_bound k _ hc l hl
    exact wdigM_witEncN_low output w _ (by omega)
  · unfold SharedV3.sibling SharedV3.sibOff
    have := blkOff_bound k _ hc l hl
    exact wdigM_witEncN_low output w _ (by
      have : 48 * (1 - SharedV3.physical k.val raw.val / 2 ^ l % 2) ≤ 48 := by omega
      omega)
  · unfold SharedV3.topOther SharedV3.topOtherOff SharedV3.handR SharedV3.handL
    exact wdigM_witEncN_low output w _ (by split_ifs <;> omega)

theorem initialPair_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    SharedV3.initialPair (Paired.witEncN output w) = SharedV3.initialPair (Paired.witEnc output w) := by
  unfold SharedV3.initialPair SharedV3.leafPad V3.leafPad
  rw [wdigM_witEncN_low output w (V3.regionOffset 0 + 672) (by unfold V3.regionOffset; omega),
    wdigM_witEncN_low output w (V3.regionOffset 0 + 160) (by unfold V3.regionOffset; omega)]

theorem forest_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (hi : index < 2 ^ 31) :
    SharedV3.forest (Paired.witEncN output witness) index (rawChildFromOutput output)
      (fun k => ClaudeWCT.WCT9.embed (forestRank output k.val)) =
      recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output)
        witness.signature.forest := by
  have hp : ∀ k, PathReadout (Paired.witEncN output witness) k
      (coordinateRaw (forestSelectionFromOutput output) k) (coordinatePath witness.signature.forest k) := by
    intro k; rw [coordinateRaw_output]
    exact pathReadout_witEncN output witness k _ _ (pathReadout_witEnc output witness k)
  have h := forest_canonical (Paired.witEncN output witness) index hi
    (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest
    ((initialPair_witEncN output witness).trans (PairedReadout.initialPair_witEnc output witness))
    (fun k => chainReadout_witEncN output witness k _ _ (chainReadout_witEnc output witness k _)) hp
  simpa only [coordinateRaw_output, coordinateWord_output] using h
end W9Drv.SharedCanonical

/-! ### HonestN 8: the expander's re-derived top nonces are the keygen nonces (interface with r3-lean-nonsec)
`topHonestNonce answers index k` is r3n's `WCT9.honestNonce answers 0 (route index 0).2 k ((route index 0).1 / 2^(k+1))`
unfolded at `lay = 0, k < 11` (`unfold honestNonce; rw [if_pos ⟨rfl, hk⟩]`). -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The keygen (nonce-searched) nonce of the level-`k + 1` top node on the path of `index`'s top leaf. -/
noncomputable def topHonestNonce (answers : Answers) (index k : Nat) : Nat :=
  (evalWithAnswerFn answers (topNodeAt (k + 1) (2 ^ (height (0 : Layer) - k - 1) + (route index 0).1 / 2 ^ (k + 1))
    (treeValue (wotsTree answers 0 (route index 0).2) k (2 * ((route index 0).1 / 2 ^ (k + 1))))
    (treeValue (wotsTree answers 0 (route index 0).2) k (2 * ((route index 0).1 / 2 ^ (k + 1)) + 1)))).1

/-- Fold invariant: value on the honest path, and the honest nonces of the levels passed so far. -/
theorem eval_topFoldN_nonces_steps (answers : Answers) (sig : Signature) (index : Nat)
    (levels : List (List Digest)) (leaves : List Digest) (htree : TopTreeLevels answers leaves 12 levels)
    (hleaf : (route index 0).1 < 2 ^ 12)
    (hpath : ∀ j : Fin (height 0), j.val < 11 → (sig.layers 0).path j =
      treeValue levels j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) :
    let R := evalWithAnswerFn answers (((List.finRange (height 0)).take 11).foldlM (topStepN sig index)
      (treeValue levels 0 (route index 0).1, []))
    R.2.length = 11 ∧ ∀ k, k < 11 → R.2.getD k 0 =
      (evalWithAnswerFn answers (topNodeAt (k + 1) (2 ^ (12 - (k + 1)) + (route index 0).1 / 2 ^ (k + 1))
        (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1))))
        (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1)) + 1)))).1 := by
  intro R
  have hi := eval_foldlM_list_inv answers ((List.finRange (height 0)).take 11) (topStepN sig index)
    (fun i (st : Digest × List Nat) => st.1 = treeValue levels i ((route index 0).1 / 2 ^ i) ∧ st.2.length = i ∧
      ∀ k, k < i → st.2.getD k 0 =
        (evalWithAnswerFn answers (topNodeAt (k + 1) (2 ^ (12 - (k + 1)) + (route index 0).1 / 2 ^ (k + 1))
          (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1))))
          (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1)) + 1)))).1)
    (treeValue levels 0 (route index 0).1, []) ⟨by simp, rfl, fun k hk => absurd hk (by omega)⟩
    (fun i hi st hv => ?_)
  · have hl : ((List.finRange (height 0)).take 11).length = 11 := by decide
    rw [hl] at hi
    exact ⟨hi.2.1, hi.2.2⟩
  · have hi' : i < 11 := by
      have h' := hi
      simp only [List.length_take, List.length_finRange] at h'
      change i < min 11 12 at h'
      omega
    generalize hj : ((List.finRange (height 0)).take 11)[i]'hi = j
    have hjv : j.val = i := by
      subst hj
      simp [List.getElem_take]
    obtain ⟨hv1, hv2, hv3⟩ := hv
    have hp := hpath j (by omega)
    simp only [topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [hp, hv1, hjv, sibling_pair (fun k => treeValue levels i k), div_pow_succ]
    have hh : height (0 : Layer) - i - 1 = 12 - (i + 1) := by
      change 12 - i - 1 = 12 - (i + 1); omega
    rw [hh]
    refine ⟨?_, ?_, ?_⟩
    · have hn := htree.2.2 i (by omega) ((route index 0).1 / 2 ^ (i + 1))
        (by simpa only [Nat.zero_add] using
          div_pow_bound (height := 12) (start := 0) (level := i + 1) (by omega) (by simpa using hleaf))
      rw [topLevelNode_lt answers (level := i + 1) (by omega)] at hn
      simpa only [treeValue] using hn.symm
    · simp [hv2]
    · intro k hk
      by_cases hki : k < i
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hv3 k hki
      · have hk' : k = i := by omega
        subst hk'
        rw [List.getD_append_right _ _ _ _ (by omega), hv2, Nat.sub_self]
        rfl

/-- Honest top layer (honest chain values for `digits`, honest path below the root): the expander's re-derived
nonces are the keygen nonces, `topHonestNonce`. -/
theorem topFoldN_nonces_honest (answers : Answers) (sig : Signature) (index : Nat) (hindex : index < 2 ^ 31)
    (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (hvalues : ∀ i : Fin (chainCount 0), (sig.layers 0).values i =
      wotsValue answers 0 (route index 0).2 (route index 0).1 digits i.val)
    (hpath : ∀ j : Fin (height 0), j.val < 11 → (sig.layers 0).path j =
      treeValue (wotsTree answers 0 (route index 0).2) j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) :
    (evalWithAnswerFn answers (topFoldN sig index digits)).2.length = 11 ∧
      ∀ k, k < 11 → (evalWithAnswerFn answers (topFoldN sig index digits)).2.getD k 0 = topHonestNonce answers index k := by
  have ht : (route index 0).2 = 0 := route_top_tree index hindex
  have hleaf : (route index 0).1 < 2 ^ 12 := route_leaf_bound index 0
  have htree := builtTopTree_correct answers 0
  have hvalues' : ∀ i : Fin (chainCount 0), (sig.layers 0).values i =
      leafValue answers 0 0 (route index 0).1 digits i.val := by
    intro i; rw [hvalues i, ht, wotsValue_top]
  have hpath' : ∀ j : Fin (height 0), j.val < 11 → (sig.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route index 0).1 / 2 ^ j.val ^^^ 1) := by
    intro j hj; rw [hpath j hj, ht, wotsTree_top]
  have hends : evalWithAnswerFn answers (topEnds sig index digits) =
      (List.range (chainCount 0)).map (leafEnd answers 0 0 (route index 0).1) := by
    unfold topEnds
    rw [ht]
    exact eval_chains_honest answers 0 0 _ digits hvalid _ hvalues'
  have hroot : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
      (evalWithAnswerFn answers (topEnds sig index digits))) =
      treeValue (builtTree answers 0 0) 0 (route index 0).1 := by
    rw [hends, ht, builtTree_leaf answers 0 0 _ hleaf]
    rfl
  have hs := eval_topFoldN_nonces_steps answers sig index _ _ htree hleaf hpath'
  have hf : evalWithAnswerFn answers (topFoldN sig index digits) =
      evalWithAnswerFn answers (((List.finRange (height 0)).take 11).foldlM (topStepN sig index)
        (treeValue (builtTree answers 0 0) 0 (route index 0).1, [])) := by
    unfold topFoldN
    simp only [evalWithAnswerFn_bind]
    rw [hroot]
  rw [hf]
  refine ⟨hs.1, fun k hk => ?_⟩
  rw [hs.2 k hk]
  unfold topHonestNonce
  rw [ht, wotsTree_top]
  have hh : height (0 : Layer) - k - 1 = 12 - (k + 1) := by change 12 - k - 1 = 12 - (k + 1); omega
  rw [hh]
end ClaudeWCT.WCT9

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The recovered top nonces are the nonce fold of the recovered top digits. -/
theorem recoverHintedLayers_nonces (answers : Answers) (sig : Signature) (index : Nat) (other : Digest) :
    ∀ n, ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index other n msg) = some result →
      result.digits ≠ [] ∧
      result.nonces = (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (result.digits.getD 0 []))).2 := by
  intro n
  induction n with
  | zero => intro msg result he; simp [recoverHintedLayers] at he
  | succ n ih =>
      intro msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      · rename_i counter digits low _
        by_cases hn0 : n = 0
        · subst n
          simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst result
          exact ⟨List.cons_ne_nil _ _, rfl⟩
        · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
          split at he
          · rename_i previous hr
            simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            obtain ⟨hne, hn⟩ := ih _ _ hr
            have hlen : 0 < previous.digits.length := List.length_pos_of_ne_nil hne
            refine ⟨List.append_ne_nil_of_left_ne_nil hne _, ?_⟩
            show previous.nonces = _
            rw [List.getD_append _ _ _ _ hlen]
            exact hn
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
end SigGolfCandidate.Research.SharedForest

/-! ### HonestN 9: the `Paired.witEnc` read lemmas used by the security side, for `witEncN` -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.PairedNonce
open W9Drv.SharedCanonical (wdigM_witEncN_low regionOffset_le blkOff_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wvalueFor_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (digits : List Nat) (i : Fin (chainCount lay)) :
    wvalueFor (witEncN output w) lay digits i.val = (w.signature.layers lay).values i := by
  rw [← wvalueFor_witEnc output w lay digits i]
  unfold wvalueFor
  split
  · have h8 : 8320 ≤ leafBufferSlot lay i.val := by
      have : 8320 ≤ leafBufferBase lay := by fin_cases lay <;> decide
      unfold leafBufferSlot; split_ifs <;> omega
    exact wdig_witEncN_out output w _ (Or.inr h8)
  · unfold wvalue
    have := chainBlock_ge lay i.val
    exact wdig_witEncN_out output w _ (Or.inr (by omega))

theorem wpath_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (j : Fin (height lay)) :
    wpath (witEncN output w) lay (route (WCT9.digestIndex output) lay).1 j.val = (w.signature.layers lay).path j := by
  rw [← wpath_witEnc output w lay j]
  by_cases hl : lay = 0
  · subst hl
    have hj : j.val < 12 := j.isLt
    unfold wpath SigGolfCandidate.T3M.sibOff
    split_ifs
    · have := top_window_free output j.val 0 hj (by decide) (by omega)
      exact wdig_witEncN_free output w _ (fun j' hj' => by have := this j' hj'; omega)
    · have := top_window_free output j.val 3 hj (by decide) (by omega)
      exact wdig_witEncN_free output w _ (fun j' hj' => by have := this j' hj'; omega)
  · unfold wpath
    have := merkleBlock_lower_ge lay hl (route (WCT9.digestIndex output) lay).1 j.val
    exact wdig_witEncN_out output w _ (Or.inr (by omega))

theorem wleafValue_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEncN output witness) (W9Machine.V3.regionOffset k.val + W9Machine.V3.leafSlot i.val) =
      coordinateValues witness.signature.forest k i := by
  have hr := regionOffset_le k
  have hi := i.isLt
  refine Eq.trans ?_ (wleafValue_witEnc output witness k i)
  exact wdigM_witEncN_low output witness _ (by unfold W9Machine.V3.leafSlot; split_ifs <;> omega)

theorem wchainValue_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEncN output witness) (W9Machine.V3.chainOffset k.val i.val + ClaudeWCT.W9.T3M.wctValueOff i.val) =
      coordinateValues witness.signature.forest k i := by
  have hr := regionOffset_le k
  have hb := PairedReadout.chain_field_bound i
  have hv : ClaudeWCT.W9.T3M.wctValueOff i.val ≤ 48 := by
    unfold ClaudeWCT.W9.T3M.wctValueOff; split_ifs <;> omega
  refine Eq.trans ?_ (wchainValue_witEnc output witness k i)
  exact wdigM_witEncN_low output witness _ (by unfold W9Machine.V3.chainOffset; omega)

theorem wsibling_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (level : Nat) (hl : level < W9Machine.SharedV3.lastLevel k.val + 1) :
    W9Machine.SharedV3.sibling (witEncN output witness) k.val
      (W9Machine.SharedV3.physical k.val (rawChildFromOutput output k).val) level =
      coordinatePath witness.signature.forest k level := by
  have hc := W9Machine.SharedV3.physical_lt k.val (rawChildFromOutput output k).val
    (rawChildFromOutput output k).isLt
  have hb := blkOff_bound k _ hc level (by omega)
  refine Eq.trans ?_ (wsibling_witEnc output witness k level hl)
  unfold W9Machine.SharedV3.sibling W9Machine.SharedV3.sibOff
  exact wdigM_witEncN_low output witness _ (by
    have : 48 * (1 - W9Machine.SharedV3.physical k.val (rawChildFromOutput output k).val / 2 ^ level % 2) ≤ 48 := by
      omega
    omega)

theorem wtopOther_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) :
    W9Machine.SharedV3.topOther (witEncN output witness) k.val
      (W9Machine.SharedV3.physical k.val (rawChildFromOutput output k).val) =
      coordinatePath witness.signature.forest k (W9Machine.SharedV3.lastLevel k.val + 1) := by
  have hr := regionOffset_le k
  refine Eq.trans ?_ (wtopOther_witEnc output witness k)
  unfold W9Machine.SharedV3.topOther W9Machine.SharedV3.topOtherOff W9Machine.SharedV3.handR
    W9Machine.SharedV3.handL
  exact wdigM_witEncN_low output witness _ (by split_ifs <;> omega)
end ClaudeWCT.W9.T3M.Paired

/-! ### HonestN 10: the witness nonces are the nonce fold of the expander's top digits -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem expandN_nonces_raw (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    ∃ result c,
      evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0) (WCT9.digestIndex output)
        (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result ∧
      w.signature = fillTopSignature sig c ∧ w.topNonces = result.nonces := by
  unfold expandN at he
  simp only [show (fillTopSignature sig 0).rho = sig.rho from rfl,
    show (fillTopSignature sig 0).forest = sig.forest from rfl,
    show (fillTopSignature sig 0).policyHints = sig.policyHints from rfl] at he
  by_cases hh : sig.policyHints.toNat ≥ 7744
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  · simp only [hh, if_false, evalWithAnswerFn_bind] at he
    cases hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) with
    | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some found =>
        obtain ⟨counter, N⟩ := found
        simp only [hd, evalWithAnswerFn_bind] at he
        let forest := evalWithAnswerFn answers (recoverForest (WCT9.digestIndex N)
          (forestSelectionFromOutput N) (forestWordsFromOutput N) sig.forest)
        cases hr : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0)
          (WCT9.digestIndex N) (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
          (.pair forest.1 forest.2)) with
        | none =>
            dsimp only [forest] at hr
            simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
        | some result =>
            dsimp only [forest] at hr
            simp only [hr] at he
            by_cases hp : policyHintsValid sig.policyHints result.digits result.lows = true
            · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hk : result.root = pk
              · simp only [hk, if_true, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                exact ⟨result, 0, (by first | exact hr | rfl), rfl, rfl⟩
              · simp only [hk, if_false, evalWithAnswerFn_bind] at he
                cases hc : evalWithAnswerFn answers (WCT9.searchTop (WCT9.digestIndex N) result.foldedTop
                  (((fillTopSignature sig 0).layers 0).path WCT9.topJ) pk WCT9.searchFuel 1) with
                | none => simp only [hc, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    simp only [hc, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                    obtain ⟨rfl, rfl⟩ := he
                    exact ⟨result, c, (by first | exact hr | rfl), fillTopSignature_fillTopSignature sig 0 c, rfl⟩
            · have hp0 := Bool.eq_false_of_not_eq_true hp
              simp only [hp0, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he

/-- img-v6: the expanded witness's top nonces are the expander's nonce fold (`topFoldN`) of its top digits, on the
witness's own signature. With `ClaudeWCT.WCT9.topFoldN_nonces_honest` they are the keygen nonces on an honest top. -/
theorem expandN_topNonces (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    ∃ result,
      evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0) (WCT9.digestIndex output)
        (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result ∧
      w.topNonces = (evalWithAnswerFn answers
        (ClaudeWCT.WCT9.topFoldN (mainSignature w.signature) (WCT9.digestIndex output) (result.digits.getD 0 []))).2 := by
  obtain ⟨result, c, hr, hsig, hn⟩ := expandN_nonces_raw answers message pk sig output w he
  refine ⟨result, hr, ?_⟩
  rw [hn, (recoverHintedLayers_nonces answers _ _ _ 4 _ result hr).2, hsig, topFoldN_fill_signature,
    topFoldN_fill_signature]
end ClaudeWCT.W9.T3M.Paired
