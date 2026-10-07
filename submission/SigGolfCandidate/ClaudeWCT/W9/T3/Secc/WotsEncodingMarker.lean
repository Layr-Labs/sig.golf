import SigGolfCandidate.T3.Secc.WotsEncodingMarker
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingE1
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.ProducerDecodeV5

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
def MarkEntry (T : Answers) (a : ChainAddr) (entry : Entry) : Prop :=
  ∃ (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) (digits : List Nat),
    Extract.msgFits a.key.lay message ∧ entry.1 = encRow a.key message counter pad ∧
      referenceInput T a.key ≠ some (encRow a.key message counter pad) ∧
      decode a.key.lay (low entry.2) = some digits ∧
      digits.getD a.chain 0 + 1 = (referenceDigits T a.key).getD a.chain 0 ∧
      ∀ i, i ≠ a.chain → (referenceDigits T a.key).getD i 0 ≤ digits.getD i 0
theorem markerAt_iff (T : Answers) (trace : List Entry) (a : ChainAddr) :
    MarkerAt T trace a ↔ ∃ entry ∈ trace, MarkEntry T a entry := by
  constructor
  · rintro ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩
    exact ⟨_, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
  · rintro ⟨⟨input, answer⟩, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
    exact ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩
theorem markerAt_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry)
    (p : CanonGraph.LeafPos × Fin 58) (hs : p.1.Source) :
    MarkerAt T' trace (chainAt p) ↔ MarkerAt T trace (chainAt p) := by
  unfold MarkerAt chainAt
  simp only
  rw [referenceInput_congr_honest h hs, referenceDigits_congr_honest h hs]
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
          rintro ans - ⟨message, counter, pad, digits, -, -, -, hd, hlow, hrest⟩
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
      rintro ans - ⟨message, counter, pad, digits, -, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem rejAnswers_card (lay : Layer) :
    (rejAnswers lay).card + ClaudeWCT.W9.T3.ProducerV5.producerCount lay * 2 ^ 128 = 2 ^ 256 := by
  have hc := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128) (by decide)
    (fun value : Digest => WCT9.producerDecode lay value = none)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Digest))
    (fun value : Digest => WCT9.producerDecode lay value = none)
  have hacc : (Finset.univ.filter fun value : Digest => ¬ WCT9.producerDecode lay value = none).card =
      ClaudeWCT.W9.T3.ProducerV5.producerCount lay := by
    rw [← ClaudeWCT.W9.T3.ProducerV5.card_producerDecode lay]
    exact congrArg Finset.card (Finset.filter_congr fun v _ => Option.ne_none_iff_isSome)
  have hr : (rejAnswers lay).card =
      (Finset.univ.filter fun value : Digest => WCT9.producerDecode lay value = none).card * 2 ^ (256 - 128) := by
    rw [← hc]
    rfl
  rw [hacc, Finset.card_univ, Fintype.card_bitVec] at hsplit
  have e0 : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  have e2 : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num
  rw [e0] at hsplit
  rw [hr, e0, e2]
  omega
theorem producerCount_le (lay : Layer) :
    ClaudeWCT.W9.T3.ProducerV5.producerCount lay ≤ 217433284086354415880083123326127992 := by
  fin_cases lay <;> decide +kernel
theorem rejAnswers_card_ge (lay : Layer) : 53 * 2 ^ 256 ≤ 57 * (rejAnswers lay).card := by
  have h := rejAnswers_card lay
  have ha := producerCount_le lay
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
          rintro ans - ⟨message, counter, pad, digits, -, -, -, hd, hlow, hrest⟩
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
      rintro ans - ⟨message, counter, pad, digits, -, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_init_le (T : Answers) (k : CellKey) (e : k.1) (p : CanonGraph.LeafPos × Fin 58) :
    Pr[fun ans => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e.val, ans) |
      cell (cellInit k e)] ≤ 57 / (2 : ENNReal) ^ 128 := by
  by_cases hp : p.1 = e.val.1.1
  · refine (probEvent_mono fun ans _ h => h.2).trans ?_
    unfold cellInit
    split_ifs
    · rw [Lazy.probEvent_cell_univ]
      exact markEntry_cell_le T _ _
    · have h := markEntry_rej_le T (encInput e.val) (chainAt p)
      rw [show (chainAt p).key.lay = e.val.1.1.lay from by rw [← hp]; rfl] at h
      exact h
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
    rintro ans - ⟨hsrc, message, counter, pad, digits, -, he, -⟩
    exact hp (encInput_leaf hsrc.1 (he.trans rfl : encInput e.val = encRow (leafOf p.1) message counter pad)).symm
theorem rejAnswers_card_ge_tight (lay : Layer) : 1000 * 2 ^ 256 ≤ 1001 * (rejAnswers lay).card := by
  have h := rejAnswers_card lay
  have ha := producerCount_le lay
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
          rintro ans - ⟨message, counter, pad, digits, -, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
      _ ≤ 53 / (2 : ENNReal) ^ 128 := by
          refine ENNReal.div_le_div_right ?_ _
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_le_53 _ W i)
      _ ≤ (53053 / 1000) / (2 : ENNReal) ^ 128 := by
          gcongr
          apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
          norm_num
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, pad, digits, -, -, -, -, hlow, -⟩
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
          rintro ans - ⟨message, counter, pad, digits, -, -, -, hd, hlow, hrest⟩
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
      rintro ans - ⟨message, counter, pad, digits, -, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_init_le_tight (T : Answers) (k : CellKey) (e : k.1) (p : CanonGraph.LeafPos × Fin 58) :
    Pr[fun ans => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e.val, ans) |
      cell (cellInit k e)] ≤ (53053 / 1000) / (2 : ENNReal) ^ 128 := by
  by_cases hp : p.1 = e.val.1.1
  · refine (probEvent_mono fun ans _ h => h.2).trans ?_
    unfold cellInit
    split_ifs
    · rw [Lazy.probEvent_cell_univ]
      exact markEntry_cell_le_tight T _ _
    · have h := markEntry_rej_le_tight T (encInput e.val) (chainAt p)
      rw [show (chainAt p).key.lay = e.val.1.1.lay from by rw [← hp]; rfl] at h
      exact h
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
    rintro ans - ⟨hsrc, message, counter, pad, digits, -, he, -⟩
    exact hp (encInput_leaf hsrc.1 (he.trans rfl : encInput e.val = encRow (leafOf p.1) message counter pad)).symm
theorem markEntry_sum_init_le (T : Answers) (k : CellKey) (e : k.1) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e.val, ans) |
        cell (cellInit k e)] ≤ 2865 / (2 : ENNReal) ^ 128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e.val, ans) |
        cell (cellInit k e)] ≤ if p.1 = e.val.1.1 then
          (if p.2.val < 54 then (53053 / 1000) / (2 : ENNReal) ^ 128 else 0) else 0 := by
    intro p
    split_ifs with hp hc
    · exact markEntry_init_le_tight T k e p
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsource, -⟩
      have hcount := chainCount_le_54 p.1.lay
      have hchain : p.2.val < chainCount p.1.lay := hsource.2
      omega
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsrc, message, counter, pad, digits, -, he, -⟩
      exact hp (encInput_leaf hsrc.1 (he.trans rfl : encInput e.val = encRow (leafOf p.1) message counter pad)).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single e.val.1.1 (fun L _ hL => by simp [hL]) (by simp)]
  simp only [if_true]
  have hn : (Finset.univ.filter (fun i : Fin 58 => i.val < 54)).card = 54 := by decide
  rw [← Finset.sum_filter, Finset.sum_const, hn, nsmul_eq_mul]
  rw [← mul_div_assoc]
  gcongr
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num
theorem markEntry_sum_cell_le (T : Answers) (e : EncIndex) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e, ans) |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 2865 / (2 : ENNReal) ^ 128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e, ans) |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ if p.1 = e.1.1 then
          (if p.2.val < 54 then (53053 / 1000) / (2 : ENNReal) ^ 128 else 0) else 0 := by
    intro p
    split_ifs with hp hc
    · exact (probEvent_mono fun ans _ h => h.2).trans (markEntry_cell_le_tight T _ _)
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsource, -⟩
      have hcount := chainCount_le_54 p.1.lay
      have hchain : p.2.val < chainCount p.1.lay := hsource.2
      omega
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsrc, message, counter, pad, digits, -, he, -⟩
      exact hp (encInput_leaf hsrc.1 (he.trans rfl : encInput e = encRow (leafOf p.1) message counter pad)).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single e.1.1 (fun L _ hL => by simp [hL]) (by simp)]
  simp only [if_true]
  have hn : (Finset.univ.filter (fun i : Fin 58 => i.val < 54)).card = 54 := by decide
  rw [← Finset.sum_filter, Finset.sum_const, hn, nsmul_eq_mul]
  rw [← mul_div_assoc]
  gcongr
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num
theorem markEntry_noncell (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (cellKey (eagerAnswers U privateTable pub)).1 x)
    (p : CanonGraph.LeafPos × Fin 58) :
    ¬ (WotsExtract.SourceChain7 (chainAt p) ∧
      MarkEntry (eagerAnswers U privateTable pub) (chainAt p) (x, eagerAnswers U privateTable pub (.inl (.inr x)))) := by
  rintro ⟨hsrc, message, counter, pad, digits, hfit, he, hne, hdec, -⟩
  have hin : encInput (encIdx p.1 hsrc.1 message counter pad hfit) = x :=
    (encInput_encIdx p.1 hsrc.1 message counter pad hfit).trans he.symm
  have hnc : ¬ (Free (eagerAnswers U privateTable pub) (encIdx p.1 hsrc.1 message counter pad hfit) ∨
      Rej (eagerAnswers U privateTable pub) (encIdx p.1 hsrc.1 message counter pad hfit)) :=
    fun hc => hx ⟨encIdx p.1 hsrc.1 message counter pad hfit, hc, hin⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf p.1) x := by
    by_contra hfree
    refine hnc (Or.inl ?_)
    change ¬ Reached _ _ (encInput (encIdx p.1 hsrc.1 message counter pad hfit))
    rw [hin]
    exact hfree
  cases hs : WCT9.producerDecode p.1.lay (low (eagerAnswers U privateTable pub (.inl (.inr x)))) with
  | none =>
      refine hnc (Or.inr ⟨?_, ?_⟩)
      · change Reached _ _ (encInput (encIdx p.1 hsrc.1 message counter pad hfit))
        rw [hin]
        exact hreached
      · change WCT9.producerDecode p.1.lay (low (eagerAnswers U privateTable pub
          (.inl (.inr (encInput (encIdx p.1 hsrc.1 message counter pad hfit)))))) = none
        rw [hin]
        exact hs
  | some w =>
      have href := reached_valid_reference hreached hs
      exact hne (he ▸ href)
noncomputable def markerCount (s : RefSample) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain7 (chainAt p) ∧ MarkerAt s.answers s.trace (chainAt p)).card
theorem markerCount_marks (T : Answers) (trace : List Entry) (pk : Digest) :
    markerCount ⟨T, pk, trace⟩ =
      Lazy.marks (fun p entry => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) entry) trace := by
  unfold markerCount Lazy.marks
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff : (WotsExtract.SourceChain7 (chainAt p) ∧ MarkerAt T trace (chainAt p)) ↔
      ∃ entry ∈ trace, WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry T (chainAt p) entry := by
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
theorem markerCount_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry)
    (pk : Digest) : markerCount ⟨T', pk, trace⟩ = markerCount ⟨T, pk, trace⟩ := by
  unfold markerCount
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, (markerAt_congr h trace p h1.1.1).mp h1.2⟩ h2
  · exact absurd ⟨h2.1, (markerAt_congr h trace p h2.1.1).mpr h2.2⟩ h1
  · rfl
theorem cells_marker_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (adversary : AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          (markerCount (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) : ENNReal) ≤
      (2865 / (2 : ENNReal) ^ 128) * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) : ENNReal) := by
  rw [cell_transfer adversary q U hU privateTable pub (fun s => (markerCount s : ENNReal))
      (fun tr => (Lazy.marks (fun p entry => WotsExtract.SourceChain7 (chainAt p) ∧
        MarkEntry (eagerAnswers U privateTable pub) (chainAt p) entry) tr : ENNReal))
      (fun y hy r => by
        unfold mkSample
        rw [markerCount_congr (agree_ovc U hU privateTable pub y hy), markerCount_marks]),
    cell_transfer adversary q U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y _ r => encodingCount_mkSample _ r)]
  refine (Lazy.lazy_marks_init_le encInput (cellKey (eagerAnswers U privateTable pub)).1 encInput_injective
    (eagerAnswers U privateTable pub)
    (fun p entry => WotsExtract.SourceChain7 (chainAt p) ∧ MarkEntry (eagerAnswers U privateTable pub) (chainAt p) entry)
    _ (cellInit (cellKey (eagerAnswers U privateTable pub))) (cellInit_nonempty _)
    (fun e => markEntry_sum_init_le (eagerAnswers U privateTable pub) (cellKey (eagerAnswers U privateTable pub)) e)
    (fun x hx p => markEntry_noncell U privateTable pub x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  exact_mod_cast cellCount_le_encoding _ _
end Enc
open Enc in
theorem reference_markerCount_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * (Enc.markerCount s : ENNReal) ≤
      (2865 / (2 : ENNReal) ^ 128) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact Enc.reference_cells_le adversary q (fun s => (Enc.markerCount s : ENNReal))
    (fun s => (encodingCount s : ENNReal)) _
    (fun privateTable pub => Enc.cells_marker_le adversary q (referenceInputs adversary)
      (Enc.publicUniverse_sub adversary) privateTable pub)
open Enc in
theorem reference_marker_sum_le (adversary : AdversaryP) (q : Nat) :
    ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
      (2865 / 2 ^ 128 : ENNReal) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  refine le_trans (le_of_eq ?_) (reference_markerCount_le adversary q)
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun s => ?_
  unfold Enc.markerCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold Enc.chainAt Enc.leafOf
  split_ifs <;> simp
end ClaudeWCT.W9.T3.Security.Wots
