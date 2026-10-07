import SigGolfCandidate.T3.Secc.WotsEncodingE1

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
def MarkEntry (T : Answers) (a : ChainAddr) (entry : Entry) : Prop :=
  ∃ (message : Digest) (counter : BitVec 32) (digits : List Nat),
    entry.1 = encodingRow a.key message counter ∧
      referenceInput T a.key ≠ some (encodingRow a.key message counter) ∧
      decode a.key.lay (low entry.2) = some digits ∧
      digits.getD a.chain 0 + 1 = (referenceDigits T a.key).getD a.chain 0 ∧
      ∀ i, i ≠ a.chain → (referenceDigits T a.key).getD i 0 ≤ digits.getD i 0
theorem markerAt_iff (T : Answers) (trace : List Entry) (a : ChainAddr) :
    MarkerAt T trace a ↔ ∃ entry ∈ trace, MarkEntry T a entry := by
  constructor
  · rintro ⟨message, counter, answer, digits, hmem, hne, hd, hlow, hrest⟩
    exact ⟨_, hmem, message, counter, digits, rfl, hne, hd, hlow, hrest⟩
  · rintro ⟨⟨input, answer⟩, hmem, message, counter, digits, rfl, hne, hd, hlow, hrest⟩
    exact ⟨message, counter, answer, digits, hmem, hne, hd, hlow, hrest⟩
theorem markEntry_cell_le (T : Answers) (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 57 / (2 : ENNReal) ^ 128 := by
  classical
  obtain ⟨v, hv⟩ := WotsExtract.referenceDigits_decode T a.key
  by_cases hc : a.chain < chainCount a.key.lay
  · let W := decodedWord hv
    let i : Fin (MixedCode.Code.n (code a.key.lay)) := ⟨a.chain, hc⟩
    let targets := EncodingTargets.targets a.key.lay (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] := by
          apply probEvent_mono
          rintro ans - ⟨message, counter, digits, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
      _ ≤ 57 / (2 : ENNReal) ^ 128 := by
          apply ENNReal.div_le_div_right
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_bound _ W i)
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, digits, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem unit_neighbors_le_53 (lay : Layer) (word : Encoding lay) (i : ChainIndex lay) :
    (MixedCode.unitNeighbors word i).card ≤ 53 :=
  (MixedCode.unitNeighbors_card_le word i).trans (Nat.sub_le_sub_right (chainCount_le_54 lay) 1)
theorem rejAnswers_card (lay : Layer) :
    (rejAnswers lay).card + EncodingCounting.acceptedCount lay * 2 ^ 128 = 2 ^ 256 := by
  have hc := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128) (by decide)
    (fun value : Digest => searchDecode lay value = none)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Digest))
    (fun value : Digest => searchDecode lay value = none)
  have hacc : (Finset.univ.filter fun value : Digest => ¬ searchDecode lay value = none).card =
      EncodingCounting.acceptedCount lay := by
    rw [← EncodingCounting.decoder_acceptance_count lay]
    refine (Fintype.card_of_subtype _ (fun v => ?_)).symm
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact Option.ne_none_iff_isSome
  have hr : (rejAnswers lay).card =
      (Finset.univ.filter fun value : Digest => searchDecode lay value = none).card * 2 ^ (256 - 128) := by
    rw [← hc]
    congr 1
  rw [hacc, Finset.card_univ, Fintype.card_bitVec] at hsplit
  have e0 : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  have e2 : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num
  rw [e0] at hsplit
  rw [hr, e0, e2]
  omega
theorem rejAnswers_card_ge (lay : Layer) : 53 * 2 ^ 256 ≤ 57 * (rejAnswers lay).card := by
  have h := rejAnswers_card lay
  have ha : EncodingCounting.acceptedCount lay ≤ 217433284086354415880083123326127992 := by
    fin_cases lay <;> simp [EncodingCounting.acceptedCount]
  have e1 : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  have e2 : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num
  rw [e1, e2] at h
  rw [e2]
  omega
theorem probEvent_cell_rej_le (lay : Layer) (p : HashOutput → Prop) :
    Pr[p | cell (rejAnswers lay)] ≤ 57 / 53 * Pr[p | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ans => ?_
  split_ifs
  · rw [SPMF.probOutput_eq_apply, cell_apply, probOutput_uniformSample]
    split_ifs
    · have hcard : ((53 : ENNReal) * 2 ^ 256) ≤ 57 * ((rejAnswers lay).card : ENNReal) := by
        exact_mod_cast rejAnswers_card_ge lay
      calc ((rejAnswers lay).card : ENNReal)⁻¹ = 57 / (57 * ((rejAnswers lay).card : ENNReal)) := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              mul_comm (57 : ENNReal)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
        _ ≤ 57 / (53 * 2 ^ 256) := ENNReal.div_le_div_left hcard _
        _ = 57 / 53 * ((Fintype.card HashOutput : Nat) : ENNReal)⁻¹ := by
            simp only [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
            rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              div_eq_mul_inv]
            ring
    · exact zero_le
  · simp
theorem rejAnswers_card_ge_tight (lay : Layer) : 1000 * 2 ^ 256 ≤ 1001 * (rejAnswers lay).card := by
  have h := rejAnswers_card lay
  have ha : EncodingCounting.acceptedCount lay ≤ 217433284086354415880083123326127992 := by
    fin_cases lay <;> simp [EncodingCounting.acceptedCount]
  have e1 : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  have e2 : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num
  rw [e1, e2] at h
  rw [e2]
  omega
theorem probEvent_cell_rej_le_tight (lay : Layer) (p : HashOutput → Prop) :
    Pr[p | cell (rejAnswers lay)] ≤ 1001 / 1000 * Pr[p | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ans => ?_
  split_ifs
  · rw [SPMF.probOutput_eq_apply, cell_apply, probOutput_uniformSample]
    split_ifs
    · have hcard : ((1000 : ENNReal) * 2 ^ 256) ≤ 1001 * ((rejAnswers lay).card : ENNReal) := by
        exact_mod_cast rejAnswers_card_ge_tight lay
      calc ((rejAnswers lay).card : ENNReal)⁻¹ = 1001 / (1001 * ((rejAnswers lay).card : ENNReal)) := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              mul_comm (1001 : ENNReal)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
        _ ≤ 1001 / (1000 * 2 ^ 256) := ENNReal.div_le_div_left hcard _
        _ = 1001 / 1000 * ((Fintype.card HashOutput : Nat) : ENNReal)⁻¹ := by
            simp only [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
            rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              div_eq_mul_inv]
            ring
    · exact zero_le
  · simp
theorem markEntry_rej_le (T : Answers) (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T a (x, ans) | cell (rejAnswers a.key.lay)] ≤ 57 / (2 : ENNReal) ^ 128 := by
  classical
  obtain ⟨v, hv⟩ := WotsExtract.referenceDigits_decode T a.key
  by_cases hc : a.chain < chainCount a.key.lay
  · let W := decodedWord hv
    let i : Fin (MixedCode.Code.n (code a.key.lay)) := ⟨a.chain, hc⟩
    let targets := EncodingTargets.targets a.key.lay (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | cell (rejAnswers a.key.lay)] := by
          apply probEvent_mono
          rintro ans - ⟨message, counter, digits, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ ≤ 57 / 53 * Pr[fun output => output.extractLsb' 0 128 ∈ targets |
            ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_cell_rej_le _ _
      _ = 57 / 53 * (targets.card / (2 : ENNReal) ^ 128) := by rw [FirstHit.uniform_low_mem targets]
      _ ≤ 57 / 53 * (53 / (2 : ENNReal) ^ 128) := by
          refine mul_le_mul' le_rfl (ENNReal.div_le_div_right ?_ _)
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_le_53 _ W i)
      _ = 57 / (2 : ENNReal) ^ 128 := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc (53 : ENNReal)⁻¹,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | cell (rejAnswers a.key.lay)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, digits, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_cell_le_tight (T : Answers) (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (53053 / 1000) / (2 : ENNReal) ^ 128 := by
  classical
  obtain ⟨v, hv⟩ := WotsExtract.referenceDigits_decode T a.key
  by_cases hc : a.chain < chainCount a.key.lay
  · let W := decodedWord hv
    let i : Fin (MixedCode.Code.n (code a.key.lay)) := ⟨a.chain, hc⟩
    let targets := EncodingTargets.targets a.key.lay (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] := by
          apply probEvent_mono
          rintro ans - ⟨message, counter, digits, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
      _ ≤ 53 / (2 : ENNReal) ^ 128 := by
          apply ENNReal.div_le_div_right
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_le_53 _ W i)
      _ ≤ (53053 / 1000) / (2 : ENNReal) ^ 128 := by
          gcongr
          apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
          norm_num
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, digits, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_rej_le_tight (T : Answers) (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T a (x, ans) | cell (rejAnswers a.key.lay)] ≤ (53053 / 1000) / (2 : ENNReal) ^ 128 := by
  classical
  obtain ⟨v, hv⟩ := WotsExtract.referenceDigits_decode T a.key
  by_cases hc : a.chain < chainCount a.key.lay
  · let W := decodedWord hv
    let i : Fin (MixedCode.Code.n (code a.key.lay)) := ⟨a.chain, hc⟩
    let targets := EncodingTargets.targets a.key.lay (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | cell (rejAnswers a.key.lay)] := by
          apply probEvent_mono
          rintro ans - ⟨message, counter, digits, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ ≤ 1001 / 1000 * Pr[fun output => output.extractLsb' 0 128 ∈ targets |
            ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_cell_rej_le_tight _ _
      _ = 1001 / 1000 * (targets.card / (2 : ENNReal) ^ 128) := by rw [FirstHit.uniform_low_mem targets]
      _ ≤ 1001 / 1000 * (53 / (2 : ENNReal) ^ 128) := by
          refine mul_le_mul' le_rfl (ENNReal.div_le_div_right ?_ _)
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_le_53 _ W i)
      _ = (53053 / 1000) / (2 : ENNReal) ^ 128 := by
          norm_num [div_eq_mul_inv]
          ring
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | cell (rejAnswers a.key.lay)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, digits, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_noncell (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (cellKey (eagerAnswers U privateTable pub)).1 x)
    (p : CanonGraph.LeafPos × Fin 58) :
    ¬ (WotsExtract.SourceChain (chainAt p) ∧
      MarkEntry (eagerAnswers U privateTable pub) (chainAt p) (x, eagerAnswers U privateTable pub (.inl (.inr x)))) := by
  rintro ⟨-, message, counter, digits, he, hne, hdec, -⟩
  have hin : encInput (p.1, message, counter) = x := he.symm
  have hnc : ¬ (Free (eagerAnswers U privateTable pub) (p.1, message, counter) ∨ Rej (eagerAnswers U privateTable pub) (p.1, message, counter)) :=
    fun hc => hx ⟨(p.1, message, counter), hc, hin⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf p.1) x := by
    by_contra hfree
    refine hnc (Or.inl ?_)
    change ¬ Reached _ _ (encInput (p.1, message, counter))
    rw [hin]
    exact hfree
  cases hs : searchDecode p.1.lay (low (eagerAnswers U privateTable pub (.inl (.inr x)))) with
  | none =>
      refine hnc (Or.inr ⟨?_, ?_⟩)
      · change Reached _ _ (encInput (p.1, message, counter))
        rw [hin]
        exact hreached
      · change searchDecode p.1.lay (low (eagerAnswers U privateTable pub (.inl (.inr (encInput (p.1, message, counter)))))) = none
        rw [hin]
        exact hs
  | some w =>
      have href := reached_valid_reference hreached hs
      exact hne (he ▸ href)
noncomputable def markerCount (s : RefSample) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ MarkerAt s.answers s.trace (chainAt p)).card
theorem markerCount_marks (T : Answers) (trace : List Entry) (pk : Digest) :
    markerCount ⟨T, pk, trace⟩ =
      Lazy.marks (fun p entry => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) entry) trace := by
  unfold markerCount Lazy.marks
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff : (WotsExtract.SourceChain (chainAt p) ∧ MarkerAt T trace (chainAt p)) ↔
      ∃ entry ∈ trace, WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) entry := by
    rw [markerAt_iff]
    constructor
    · rintro ⟨hs, entry, hmem, hm⟩
      exact ⟨entry, hmem, hs, hm⟩
    · rintro ⟨entry, hmem, hs, hm⟩
      exact ⟨hs, entry, hmem, hm⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl
end Enc
end SigGolfCandidate.T3.Security.Wots
