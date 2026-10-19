import SigGolfCandidate.T3_Secc_WotsEncodingMarker
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEncodingE1
import SigGolfCandidate.ClaudeWCT_WCT9_TopDecode
import SigGolfCandidate.ClaudeWCT_WCT9_Basic
import SigGolfCandidate.T3_Nonbinary_EncodingCounts
import SigGolfCandidate.T3_Nonbinary_SourceEncoding
-- serialization only (no declarations used): keeps this ~9 GB-private module from building in parallel with WotsLeafSum under the verifier's 2-job / 24 GiB limit
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafSum



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
theorem uniform_unit_neighbors (lay : Layer) (W : Encoding lay) (i : ChainIndex lay) :
    Pr[fun ans => ∃ high : Bool, ClaudeWCT.WCT9.verificationAnswer lay high ans ∈
      EncodingTargets.targets lay (MixedCode.unitNeighbors W i) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (371 / 4) / (2 : ENNReal)^128 := by
  classical
  let targets := EncodingTargets.targets lay (MixedCode.unitNeighbors W i)
  have hc : targets.card ≤ chainCount lay - 1 :=
    (EncodingTargets.targets_card _ _).trans (MixedCode.unitNeighbors_card_le W i)
  have hn : targets.card ≤ 53 := by
    have hmax : chainCount lay ≤ 54 := by fin_cases lay <;> decide +kernel
    omega
  have hp : lay ≠ 0 → ∀ d, d ∈ targets → lowerSpare d := by
    intro hl d hd
    obtain ⟨word, _, hword⟩ := (EncodingTargets.mem_targets _ _ _).mp hd
    exact decode_lowerSpare hl hword
  calc _ ≤ (targets.card : ENNReal) * (7 / ((4 : ENNReal) * 2^128)) :=
        ClaudeWCT.WCT9.probability_verification_exists_le lay targets hp
    _ ≤ 53 * (7 / ((4 : ENNReal) * 2^128)) := mul_le_mul' (by exact_mod_cast hn) le_rfl
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
      norm_num
end Enc
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.WCT9.CanonicalRates
open SigGolfCandidate.T3
/-- Both halves of a uniform answer, counted separately (kept outside the `irreducible Finset.univ` section). -/
theorem halves_card (p : Digest → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a : HashOutput => p (a.extractLsb' 0 128)).card +
    (Finset.univ.filter fun a : HashOutput => p (a.extractLsb' 128 128)).card =
      (Finset.univ.filter p).card * (2*2^128) := by
  have hl := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128) (by decide) p
  have hh := SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 128) (by decide) p
  dsimp only [Nat.reduceSub] at hl hh
  rw [hl, hh]
  ring

theorem encoding_broad (lay : Layer) :
    (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome).card ≤
      (Finset.univ.filter fun d : Digest => (decode lay d).isSome).card * (2*2^128) := by
  have hsub : (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome) ⊆
      (Finset.univ.filter fun a : HashOutput => (decode lay (a.extractLsb' 0 128)).isSome) ∪
      (Finset.univ.filter fun a : HashOutput => (decode lay (a.extractLsb' 128 128)).isSome) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at ha ⊢
    rw [encodingAnswer_eq] at ha
    split_ifs at ha
    · exact Or.inl ha
    · exact Or.inr ha
  have hh := halves_card (fun d : Digest => (decode lay d).isSome = true)
  exact le_trans (Finset.card_le_card hsub) ((Finset.card_union_le _ _).trans hh.le)
end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open SigGolfCandidate.T3
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false
attribute [local irreducible] Finset.univ Finset.filter
def broadCount (lay : Layer) : Nat :=
  (Finset.univ.filter fun d : Digest => (decode lay d).isSome).card

theorem broad_decoder_card (lay : Layer) : broadCount lay =
    (if lay=0 then SigGolfResearch.NonbinaryTop.Counting.count else EncodingCounting.rawAcceptedCount lay) := by
  unfold broadCount
  rw [← Fintype.card_subtype]
  by_cases hl : lay=0
  · subst lay
    exact Nonbinary.actual_decoder_count
  · rw [Fintype.card_congr (EncodingCounting.acceptedDigestEquiv lay hl), EncodingCounting.accepted_words_count]
    exact (if_neg hl).symm

/-- Crude union bound (both halves): enough for the 1000/1001 rejection estimate. -/
theorem broad_encoding_card (lay : Layer) :
    (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome).card ≤
      broadCount lay * (2*2^128) := by
  simpa only [broadCount] using encoding_broad lay


theorem encodingAnswer_normal (lay : Layer) (a : HashOutput) :
    encodingAnswer (CanonicalPolicy.normalLayer lay) a=encodingAnswer lay a := by
  fin_cases lay <;> rfl

theorem verificationAnswer_normal (lay : Layer) (high : Bool) (a : HashOutput) :
    verificationAnswer (CanonicalPolicy.normalLayer lay) high a=verificationAnswer lay high a := by
  fin_cases lay <;> rfl

theorem producer_rejection_broad (lay : Layer) (floor : Nat) :
    1000*2^256 ≤ 1001*(Finset.univ.filter fun a : HashOutput =>
      CanonicalPolicy.producerDecodeOut lay floor a=none).card := by
  classical
  let accepted := Finset.univ.filter fun a : HashOutput => CanonicalPolicy.producerDecodeOut lay floor a ≠ none
  let broad := Finset.univ.filter fun a : HashOutput =>
    (SigGolfCandidate.T3.decode (CanonicalPolicy.normalLayer lay) (encodingAnswer (CanonicalPolicy.normalLayer lay) a)).isSome
  have hsub : accepted ⊆ broad := by
    intro a ha
    obtain ⟨⟨ds,low⟩,hds⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp ha).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,Option.isSome_iff_exists.mpr ⟨ds,?_⟩⟩
    rw [encodingAnswer_normal]
    exact (CanonicalPolicy.producerDecodeAt_spec (CanonicalPolicy.producerDecodeOut_spec hds).2).1
  have hbound : accepted.card ≤ broadCount (CanonicalPolicy.normalLayer lay) * (2*2^128) :=
    (Finset.card_le_card hsub).trans (broad_encoding_card _)
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset HashOutput))
    (fun a => CanonicalPolicy.producerDecodeOut lay floor a = none)
  simp only [Finset.card_univ, Fintype.card_bitVec] at hpart
  change (Finset.univ.filter fun a : HashOutput => CanonicalPolicy.producerDecodeOut lay floor a=none).card + accepted.card = 2^256 at hpart
  have hsmall : 1001 * (broadCount (CanonicalPolicy.normalLayer lay) * (2*2^128)) ≤ 2^256 := by
    rw [broad_decoder_card]
    fin_cases lay <;> norm_num [CanonicalPolicy.normalLayer, EncodingCounting.rawAcceptedCount, SigGolfResearch.NonbinaryTop.Counting.count]
  omega

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open OracleComp OracleSpec ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def UnitNeighborDecode (lay : Layer) (reference : List Nat) (chain : Nat) (output : HashOutput) : Prop :=
  ∃ digits, encodingCanDecode lay output digits ∧
    digits.getD chain 0+1=reference.getD chain 0 ∧
    ∀ j, j ≠ chain → reference.getD j 0 ≤ digits.getD j 0

theorem marker_uniform_raw (lay : Layer) (reference : List Nat) (value : Digest)
    (href : CanonicalPolicy.decode lay value=some reference) (chain : Nat) :
    Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (371/4)/(2:ENNReal)^128 := by
  classical
  let normal := CanonicalPolicy.normalLayer lay
  have href' : decode normal value=some reference := href
  by_cases hc : chain<chainCount normal
  · let W := decodedWord href'
    let i : Fin (MixedCode.Code.n (code normal)) := ⟨chain,hc⟩
    let targets := EncodingTargets.targets normal (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => ∃ high : Bool, verificationAnswer normal high output∈targets |
          ($ᵗ HashOutput : ProbComp HashOutput)] := by
          apply probEvent_mono
          rintro answer - ⟨digits,⟨high,hd⟩,hlow,hrest⟩
          refine ⟨high, ?_⟩
          have hd' : decode normal (verificationAnswer normal high answer)=some digits := by
            rw [verificationAnswer_normal]
            exact hd
          refine (EncodingTargets.source_decoded_target hd' _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid href',decodedWord_valid hd',hlow,?_⟩
          intro j hj
          exact hrest j.val (fun he=>hj (Fin.ext he))
      _ ≤ _ := ClaudeWCT.W9.T3.Security.Wots.Enc.uniform_unit_neighbors normal W i
  · have hz : Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)]=0 := by
      apply probEvent_eq_zero
      rintro answer - ⟨digits,-,hlow,hrest⟩
      have hlen := (decode_length_sum href').1
      rw [List.getD_eq_default reference 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le


open SphincsSecurity.Concrete.UniformTableCompletion

noncomputable def rejectedAt (lay : Layer) (floor : Nat) : Finset HashOutput :=
  Finset.univ.filter fun a => CanonicalPolicy.producerDecodeOut lay floor a=none

theorem probEvent_rejected_le (lay : Layer) (floor : Nat) (p : HashOutput→Prop) :
    Pr[p | cell (rejectedAt lay floor)] ≤ 1001/1000*Pr[p | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [probEvent_eq_tsum_ite,probEvent_eq_tsum_ite,←ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ans=>?_
  split_ifs
  · rw [SPMF.probOutput_eq_apply,cell_apply,probOutput_uniformSample]
    split_ifs
    · have hc : ((1000:ENNReal)*2^256)≤1001*((rejectedAt lay floor).card:ENNReal) := by
        exact_mod_cast producer_rejection_broad lay floor
      calc ((rejectedAt lay floor).card:ENNReal)⁻¹ = 1001/(1001*((rejectedAt lay floor).card:ENNReal)) := by
            rw [ENNReal.div_eq_inv_mul,ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              mul_comm (1001:ENNReal)⁻¹,mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),mul_one]
        _ ≤ 1001/(1000*2^256) := ENNReal.div_le_div_left hc _
        _ = 1001/1000*((Fintype.card HashOutput:Nat):ENNReal)⁻¹ := by
          simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
          rw [ENNReal.div_eq_inv_mul,ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),div_eq_mul_inv]
          ring
    · exact zero_le
  · simp

theorem marker_rejected_le (lay : Layer) (floor : Nat) (reference : List Nat) (value : Digest)
    (href : CanonicalPolicy.decode lay value=some reference) (chain : Nat) :
    Pr[UnitNeighborDecode lay reference chain | cell (rejectedAt lay floor)] ≤ 93/(2:ENNReal)^128 := by
  calc _ ≤ 1001/1000*Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)] :=
      probEvent_rejected_le _ _ _
    _ ≤ 1001/1000*((371/4)/(2:ENNReal)^128) := mul_le_mul' le_rfl (marker_uniform_raw lay reference value href chain)
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
      norm_num

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The LOW path bonus only helps: a word accepted through HIGH is accepted through LOW. -/
theorem producerDecodeAt_true_of_false {lay : Layer} {floor : Nat} {word : Digest} {digits : List Nat}
    (h : CanonicalPolicy.producerDecodeAt lay floor false word = some digits) :
    CanonicalPolicy.producerDecodeAt lay floor true word = some digits := by
  unfold CanonicalPolicy.producerDecodeAt at h ⊢
  cases hd : CanonicalPolicy.decode lay word with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h ⊢
      split_ifs at h with hc
      cases h
      have hb : ∀ d, CanonicalPolicy.pathReward lay false d ≤ CanonicalPolicy.pathReward lay true d := by
        intro d
        simp only [CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus_false]
        omega
      rw [if_pos ⟨hc.1.trans (hb _), hc.2⟩]

/-- Path-aware rejected cell (both layer kinds; top bonus 3, lower bonus 4). Let `word` be accepted at `floor`
through some half, with digits `digits`. A rejected answer that still decodes to `digits` for some witness hint has
HIGH half `word`: if its LOW half were `word`, LOW would pass the producer predicate through the (better) LOW path
and the producer would have selected it (top: the producer prefers a good LOW; lower: the decodable LOW is spare). -/
theorem rejected_canDecode {lay : Layer} {floor : Nat} (hfloor : lay = 0 → floor = CanonicalPolicy.topFloor)
    {word : Digest} {low : Bool} {digits : List Nat}
    (href : CanonicalPolicy.producerDecodeAt lay floor low word = some digits) {a : HashOutput}
    (hrej : CanonicalPolicy.producerDecodeOut lay floor a = none)
    (hdec : encodingCanDecode lay a digits) :
    a.extractLsb' 128 128 = word := by
  obtain ⟨high, hd⟩ := hdec
  have hword : verificationAnswer lay high a = word :=
    canonical_decode_injective hd (CanonicalPolicy.producerDecodeAt_spec href).1
  have hrej' : CanonicalPolicy.producerDecodeAt lay floor (lowSelected lay a) (encodingAnswer lay a) = none := by
    unfold CanonicalPolicy.producerDecodeOut at hrej
    simpa only [Option.map_eq_none_iff] using hrej
  have htrue : CanonicalPolicy.producerDecodeAt lay floor true word = some digits := by
    cases low
    · exact producerDecodeAt_true_of_false href
    · exact href
  have hlowne : a.extractLsb' 0 128 = word → False := by
    intro hlw
    have hsel : lowSelected lay a = true := by
      by_cases hl : lay = 0
      · subst hl
        have hf := hfloor rfl
        subst hf
        have hg : topGood (a.extractLsb' 0 128) := by
          unfold topGood
          rw [hlw, htrue]
          rfl
        simp only [lowSelected, if_true, topChooseLow, decide_eq_true_eq]
        exact Or.inl hg
      · have hdw := (CanonicalPolicy.producerDecodeAt_spec href).1
        simp only [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, if_neg hl] at hdw
        have hspare : lowerSpare (a.extractLsb' 0 128) := by
          rw [hlw]
          exact SigGolfCandidate.T3.decode_lowerSpare (by decide : (1 : Layer) ≠ 0) hdw
        simp [lowSelected, hl, hspare]
    rw [encodingAnswer_eq, hsel, if_pos rfl, hlw, htrue] at hrej'
    cases hrej'
  by_cases hl : lay = 0
  · subst hl
    have hread : verificationAnswer 0 high a = TopChoice.read high a := rfl
    rw [hread] at hword
    unfold TopChoice.read at hword
    split_ifs at hword
    · exact hword
    · exact (hlowne hword).elim
  · rw [verificationAnswer_eq_lower lay hl, verificationLow_lower lay hl] at hword
    split_ifs at hword
    · exact (hlowne hword).elim
    · exact hword

/-- Rejected-cell match bound (path-aware floors): `(1001/1000)/2^128 ≤ (7/4)/2^128`. -/
theorem canDecode_rejected_le {lay : Layer} {floor : Nat} (hfloor : lay = 0 → floor = CanonicalPolicy.topFloor)
    {word : Digest} {low : Bool} {digits : List Nat}
    (href : CanonicalPolicy.producerDecodeAt lay floor low word = some digits) :
    Pr[fun a => encodingCanDecode lay a digits | cell (rejectedAt lay floor)] ≤ 7/((4:ENNReal)*2^128) := by
  classical
  calc _ ≤ Pr[fun a : HashOutput => a.extractLsb' 128 128 = word | cell (rejectedAt lay floor)] := by
        apply probEvent_mono
        intro a ha hdec
        have hmem := SigGolfCandidate.T3.Security.Wots.Enc.Lazy.cell_nonzero_mem
          ((SPMF.mem_support_iff _ _).mp ha)
        have hrej : CanonicalPolicy.producerDecodeOut lay floor a = none := by
          simpa only [rejectedAt, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
        exact rejected_canDecode hfloor href hrej hdec
    _ ≤ 1001/1000*Pr[fun a : HashOutput => a.extractLsb' 128 128 = word |
          ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_rejected_le _ _ _
    _ = 1001/1000*(1/(2:ENNReal)^128) := by
        congr 1
        rw [probEvent_uniformSample]
        have hc := SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 128) (by decide)
          (fun v : BitVec 128 => v = word)
        have h1 : (Finset.univ.filter fun v : BitVec 128 => v = word).card = 1 := by
          rw [Finset.filter_eq' Finset.univ word]
          simp
        change (Finset.univ.filter fun a : HashOutput => a.extractLsb' 128 128 = word).card = _ at hc
        rw [hc, h1, Fintype.card_bitVec]
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_one]
        rw [show (2:ENNReal)^256 = 2^128*2^128 by rw [← pow_add], ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
          mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, one_div]
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
        ENNReal.toReal_one]
      norm_num

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def MarkEntry (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (entry : Entry) : Prop :=
  ∃ (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) (digits : List Nat),
    Extract.msgFits a.key.lay message ∧ entry.1 = encRow a.key message counter pad ∧
      referenceInput T messages a.key ≠ some (encRow a.key message counter pad) ∧
      WCT9.encodingCanDecode a.key.lay entry.2 digits ∧
      digits.getD a.chain 0 + 1 = (referenceDigits T messages a.key).getD a.chain 0 ∧
      ∀ i, i ≠ a.chain → (referenceDigits T messages a.key).getD i 0 ≤ digits.getD i 0

theorem markerAt_iff (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) (a : ChainAddr) :
    MarkerAt T messages trace a ↔ ∃ entry ∈ trace, MarkEntry T messages a entry := by
  constructor
  · rintro ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩
    exact ⟨_, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
  · rintro ⟨⟨input, answer⟩, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
    exact ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩

theorem markEntry_cell_le_raw (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (371/4)/(2:ENNReal)^128 := by
  obtain ⟨value,hvalue⟩ := referenceDigits_decode T messages a.key
  apply le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.marker_uniform_raw a.key.lay
    (referenceDigits T messages a.key) value hvalue a.chain)
  rintro answer - ⟨message,counter,pad,digits,hfit,he,hne,hd,hlow,hrest⟩
  exact ⟨digits,hd,hlow,hrest⟩

theorem markEntry_cell_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      93/(2:ENNReal)^128 := by
  refine (markEntry_cell_le_raw T messages x a).trans (ENNReal.div_le_div_right ?_ _)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem markEntry_rejected_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) (remaining : Nat) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | cell (rejectedAnswers a.key.lay remaining)] ≤
      93/(2:ENNReal)^128 := by
  obtain ⟨value,hvalue⟩ := referenceDigits_decode T messages a.key
  apply le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.marker_rejected_le a.key.lay
    (WCT9.CanonicalPolicy.threshold a.key.lay.val remaining)
    (referenceDigits T messages a.key) value hvalue a.chain)
  rintro answer - ⟨message,counter,pad,digits,hfit,he,hne,hd,hlow,hrest⟩
  exact ⟨digits,hd,hlow,hrest⟩

theorem markEntry_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (k : CellKey) (e : k.cells) (p : CanonGraph.LeafPos × Fin 58) :
    Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
      MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      93/(2:ENNReal)^128 := by
  by_cases hp : p.1=e.val.1.1
  · refine (probEvent_mono fun ans _ h => h.2).trans ?_
    unfold cellInit
    split_ifs
    · rw [Lazy.probEvent_cell_univ]
      exact markEntry_cell_le T messages _ _
    · split
      · rw [Lazy.probEvent_cell_univ]
        exact markEntry_cell_le T messages _ _
      · have h := markEntry_rejected_le T messages (Enc.encInput e.val) (Enc.chainAt p) ‹Nat›
        rw [show (Enc.chainAt p).key.lay=e.val.1.1.lay from by rw [←hp]; rfl] at h
        exact h
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
    rintro ans - ⟨hsrc,message,counter,pad,digits,hfit,he,hrest⟩
    exact hp (Enc.encInput_leaf hsrc.1 (he.trans rfl :
      Enc.encInput e.val=encRow (Enc.leafOf p.1) message counter pad)).symm

theorem markEntry_sum_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (k : CellKey) (e : k.cells) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      5022/(2:ENNReal)^128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      if p.1=e.val.1.1 then (if p.2.val<54 then 93/(2:ENNReal)^128 else 0) else 0 := by
    intro p
    split_ifs with hp hc
    · exact markEntry_init_le T messages k e p
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsource,-⟩
      have hcount := chainCount_le_54 p.1.lay
      have hchain : p.2.val < chainCount p.1.lay := hsource.2
      omega
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsrc,message,counter,pad,digits,hfit,he,hrest⟩
      exact hp (Enc.encInput_leaf hsrc.1 (he.trans rfl :
        Enc.encInput e.val=encRow (Enc.leafOf p.1) message counter pad)).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans ?_
  rw [Fintype.sum_prod_type,Finset.sum_eq_single e.val.1.1 (fun L _ hL=>by simp [hL]) (by simp)]
  simp only [if_true]
  have hn : (Finset.univ.filter (fun i : Fin 58 => i.val<54)).card=54 := by decide
  rw [←Finset.sum_filter,Finset.sum_const,hn,nsmul_eq_mul,←mul_div_assoc]
  gcongr
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem layerCounterSearch_first (T : Answers) (lay : Layer) (floor tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel start k (digits : List Nat × Bool), k<fuel →
      (∀i<k,WCT9.CanonicalPolicy.producerDecodeOut lay floor (T (.inl (.inr
        (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (start+i)))))))=none) →
      WCT9.CanonicalPolicy.producerDecodeOut lay floor (T (.inl (.inr
        (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (start+k)))))))=some digits →
      evalWithAnswerFn T (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg start fuel)=
        some (BitVec.ofNat 32 (start+k),digits) := by
  intro fuel
  induction fuel with
  | zero => intro start k digits hk; omega
  | succ fuel ih =>
      intro start k digits hk hprev hvalid
      simp only [WCT9.CanonicalPolicy.layerCounterSearchAt,evalWithAnswerFn_bind,eval_publicHash]
      rcases k with _ | k
      · simp only [Nat.add_zero] at hvalid ⊢
        rw [hvalid]
        rfl
      · have h0 := hprev 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [h0]
        have h := ih (start+1) k digits (by omega)
          (fun i hi=>by rw [show start+1+i=start+(i+1) by omega];exact hprev (i+1) (by omega))
          (by rw [show start+1+k=start+(k+1) by omega];exact hvalid)
        rw [show start+(k+1)=start+1+k by omega]
        exact h

theorem reached_valid_reference {T : Answers} {messages : LeafAddr→WCT9.LayerMsg}
    {L : LeafAddr} {input : HashInput} (hr : Reached T messages L input)
    {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    {digits : List Nat × Bool}
    (hv : WCT9.CanonicalPolicy.producerDecodeOut L.lay
      (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (T (.inl (.inr input)))=some digits) :
    referenceInput T messages L=some input := by
  obtain ⟨c,⟨hc,oldRemaining,hctx',hprev⟩,rfl⟩ := hr
  rw [hctx] at hctx'
  cases hctx'
  have hs : searchOf T messages L remaining=some (BitVec.ofNat 32 c,digits) := by
    unfold searchOf
    have h := layerCounterSearch_first T L.lay _ L.tree L.leaf (messages L)
      (WCT9.searchLimit L.lay) 0 c digits hc
      (fun i hi=>by rw [Nat.zero_add,←encRow_zero]; rw [←decodeRow_answer];exact hprev i hi)
      (by rw [Nat.zero_add,←encRow_zero];exact hv)
    simpa only [Nat.zero_add] using h
  have href : referenceSearch T messages L=some (BitVec.ofNat 32 c,digits) := by
    change (referenceContext T messages L).bind (searchOf T messages L)=_
    rw [hctx]
    exact hs
  unfold referenceInput
  rw [href]
  rfl

theorem referenceInput_eq_of_noncell (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x)
    (L : CanonGraph.LeafPos) (hsource : L.Source) (message : WCT9.LayerMsg)
    (counter : BitVec 32) (pad : RowPad) (hfit : Extract.msgFits L.lay message)
    (he : x=encRow (Enc.leafOf L) message counter pad) :
    referenceInput T messages (Enc.leafOf L)=some x := by
  let entry : Enc.EncIndex := Enc.encIdx L hsource message counter pad hfit
  have hin : Enc.encInput entry=x := (Enc.encInput_encIdx L hsource message counter pad hfit).trans he.symm
  have hleaf : Enc.leafOf entry.1.1=Enc.leafOf L := rfl
  have hnc : ¬(entry∈freeSet T messages ∨ entry∈rejectedSet T messages) :=
    fun hc=>hx ⟨entry,hc,hin⟩
  have hreached : Reached T messages (Enc.leafOf L) x := by
    by_contra hfree
    apply hnc
    left
    change ¬Reached T messages (Enc.leafOf entry.1.1) (Enc.encInput entry)
    rw [hin,hleaf]
    exact hfree
  obtain ⟨c,hreach,hxrow⟩ := hreached
  obtain ⟨hc,remaining,hctx,hprev⟩ := hreach
  cases hs : decodeRow T (Enc.leafOf L) (WCT9.CanonicalPolicy.threshold L.lay.val remaining)
      (messages (Enc.leafOf L)) c with
  | none =>
      exact False.elim (hnc (Or.inr
        ⟨c,remaining,⟨hc,remaining,hctx,hprev⟩,hin.trans hxrow,hctx,hs⟩))
  | some ds =>
      have hvalid : WCT9.CanonicalPolicy.producerDecodeOut L.lay
          (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (T (.inl (.inr x)))=some ds := by
        rw [decodeRow_answer,←hxrow] at hs
        exact hs
      have href := reached_valid_reference ⟨c,⟨hc,remaining,hctx,hprev⟩,hxrow⟩ hctx hvalid
      exact href


theorem markEntry_noncell (T : Answers) (messages : LeafAddr→WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x)
    (p : CanonGraph.LeafPos×Fin 58) :
    ¬(WotsExtract.SourceChain7 (Enc.chainAt p) ∧
      MarkEntry T messages (Enc.chainAt p) (x,T (.inl (.inr x)))) := by
  rintro ⟨hsrc,message,counter,pad,digits,hfit,he,hne,hdec,rest⟩
  exact hne (he ▸ referenceInput_eq_of_noncell T messages x hx p.1 hsrc.1
    message counter pad hfit he)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def MatchEntry (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (entry : Entry) : Prop :=
  ∃ (L : CanonGraph.LeafPos) (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad),
    L.Source ∧ Extract.msgFits L.lay message ∧ entry.1 = encRow (Enc.leafOf L) message counter pad ∧
      referenceInput T messages (Enc.leafOf L) ≠ some (encRow (Enc.leafOf L) message counter pad) ∧
      referenceSearch T messages (Enc.leafOf L) ≠ none ∧
      WCT9.encodingCanDecode L.lay entry.2 (referenceDigits T messages (Enc.leafOf L))

theorem matchEntry_cell_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (e : Enc.EncIndex) :
    Pr[fun ans => MatchEntry T messages (Enc.encInput e,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      7/((4:ENNReal)*2^128) := by
  apply le_trans (probEvent_mono ?_) (WCT9.probability_encodingCanDecode_le e.1.1.lay
    (referenceDigits T messages (Enc.leafOf e.1.1)))
  rintro answer - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs,hdec⟩
  have hL := Enc.encInput_leaf hsource he
  subst hL
  exact hdec

theorem referenceSearch_producerDecode (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    {c : BitVec 32} {digits : List Nat} {low : Bool} (hs : referenceSearch T messages L=some (c,digits,low)) :
    WCT9.CanonicalPolicy.producerDecodeOut L.lay (WCT9.CanonicalPolicy.threshold L.lay.val remaining)
      (T (.inl (.inr (encRow L (messages L) c 0))))=some (digits,low) := by
  have hs' : searchOf T messages L remaining=some (c,digits,low) := by
    change (referenceContext T messages L).bind (searchOf T messages L)=_ at hs
    rw [hctx] at hs
    exact hs
  have h := counterSearch_decode T L.lay _ L.tree L.leaf (messages L)
    (WCT9.searchLimit L.lay) 0 c (digits,low) hs'
  rw [eval_publicHash,←encRow_zero] at h
  exact h

/-- Path-aware floors: the reference word was accepted through the half the producer selected. -/
theorem reference_accepted (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    (hs : referenceSearch T messages L≠none) :
    ∃ (word : Digest) (low : Bool), WCT9.CanonicalPolicy.producerDecodeAt L.lay
      (WCT9.CanonicalPolicy.threshold L.lay.val remaining) low word=some (referenceDigits T messages L) := by
  obtain ⟨⟨c,digits,low⟩,hfound⟩ := Option.ne_none_iff_exists'.mp hs
  have href : referenceDigits T messages L=digits := by
    simp only [referenceDigits,hfound,Option.map_some,Option.getD_some]
  rw [href]
  exact ⟨_,_,(WCT9.CanonicalPolicy.producerDecodeOut_spec (referenceSearch_producerDecode T messages L hctx hfound)).2⟩

theorem threshold_top_floor (lay : Layer) (remaining : Nat) :
    lay = 0 → WCT9.CanonicalPolicy.threshold lay.val remaining = WCT9.CanonicalPolicy.topFloor := by
  rintro rfl
  simp [WCT9.CanonicalPolicy.threshold]

theorem matchEntry_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (e : (cellKey T messages).cells) :
    Pr[fun ans => MatchEntry T messages (Enc.encInput e.val,ans) |
      cell (cellInit (cellKey T messages) e)] ≤ 7/((4:ENNReal)*2^128) := by
  unfold cellInit
  split_ifs
  · rw [Lazy.probEvent_cell_univ]
    exact matchEntry_cell_le T messages e.val
  · split
    · rw [Lazy.probEvent_cell_univ]
      exact matchEntry_cell_le T messages e.val
    · rename_i hctx
      by_cases hs : referenceSearch T messages (Enc.leafOf e.val.1.1) = none
      · apply le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
        rintro ans - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs',hd⟩
        have hL := Enc.encInput_leaf hsource he
        subst hL
        exact hs' hs
      · obtain ⟨word,low,hword⟩ := reference_accepted T messages (Enc.leafOf e.val.1.1) hctx hs
        refine le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.canDecode_rejected_le
          (threshold_top_floor e.val.1.1.lay _) hword)
        rintro ans - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs',hd⟩
        have hL := Enc.encInput_leaf hsource he
        subst hL
        exact hd

theorem matchEntry_noncell (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x) :
    ¬MatchEntry T messages (x,T (.inl (.inr x))) := by
  rintro ⟨L,message,counter,pad,hsource,hfit,he,hne,hselected,hdecode⟩
  exact hne (he ▸ referenceInput_eq_of_noncell T messages x hx L hsource message counter pad hfit he)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def markerCount (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  Lazy.marks (fun p : CanonGraph.LeafPos × Fin 58 => fun entry =>
    WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T messages (Enc.chainAt p) entry) trace

noncomputable def matchCount (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  Lazy.marks (fun _ : Unit => MatchEntry T messages) trace

theorem lazy_marker_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    [Fintype (cellKey T messages).cells] [DecidableEq (cellKey T messages).cells]
    {α : Type} (program : OracleComp RefWorld α) :
    ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (markerCount T messages result.1.2.toList:ENNReal) ≤
      (5022/(2:ENNReal)^128) *
        ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal) := by
  refine (Lazy.lazy_marks_init_le Enc.encInput (cellKey T messages).cells Enc.encInput_injective
    T (fun p : CanonGraph.LeafPos × Fin 58 => fun entry =>
      WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T messages (Enc.chainAt p) entry)
    _ (cellInit (cellKey T messages)) (cellInit_nonempty _)
    (fun e => markEntry_sum_init_le T messages _ e)
    (fun x hx p => markEntry_noncell T messages x hx p) program).trans ?_
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  exact_mod_cast Enc.cellCount_le_encoding _ _

theorem lazy_match_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    [Fintype (cellKey T messages).cells] [DecidableEq (cellKey T messages).cells]
    {α : Type} (program : OracleComp RefWorld α) :
    ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (matchCount T messages result.1.2.toList:ENNReal) ≤
      (7/((4:ENNReal)*2^128)) *
        ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal) := by
  refine (Lazy.lazy_marks_init_le Enc.encInput (cellKey T messages).cells Enc.encInput_injective
    T (fun _ : Unit => MatchEntry T messages) _ (cellInit (cellKey T messages)) (cellInit_nonempty _)
    (fun e => by simpa using matchEntry_init_le T messages e)
    (fun x hx _ => matchEntry_noncell T messages x hx) program).trans ?_
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  exact_mod_cast Enc.cellCount_le_encoding _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem referenceDigits_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (leaf : LeafAddr) (hl : WotsExtract.SourceLeaf7 leaf) :
    referenceDigits T' messages' leaf=referenceDigits T messages leaf := by
  unfold referenceDigits
  rw [(source_reference_congr T T' messages messages' hm hd hl).2]

theorem referenceInput_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (leaf : LeafAddr) (hl : WotsExtract.SourceLeaf7 leaf) :
    referenceInput T' messages' leaf=referenceInput T messages leaf := by
  unfold referenceInput
  rw [(source_reference_congr T T' messages messages' hm hd hl).2,hm leaf hl]

theorem markEntry_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (entry : Entry) :
    MarkEntry T' messages' a entry ↔ MarkEntry T messages a entry := by
  unfold MarkEntry
  rw [referenceInput_decisions hm hd a.key ha.1, referenceDigits_decisions hm hd a.key ha.1]

theorem matchEntry_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (entry : Entry) :
    MatchEntry T' messages' entry ↔ MatchEntry T messages entry := by
  unfold MatchEntry
  apply exists_congr
  intro leaf
  apply exists_congr
  intro message
  apply exists_congr
  intro counter
  apply exists_congr
  intro pad
  by_cases hl : leaf.Source
  · have hs : WotsExtract.SourceLeaf7 (Enc.leafOf leaf) := hl
    rw [referenceInput_decisions hm hd _ hs, referenceDigits_decisions hm hd _ hs,
      (source_reference_congr T T' messages messages' hm hd hs).2]
  · simp only [hl,false_and]

theorem markerCount_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (trace : List Entry) :
    markerCount T' messages' trace=markerCount T messages trace := by
  apply congrArg (fun mark => SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks mark trace)
  funext p entry
  apply propext
  by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
  · exact and_congr_right fun _ => markEntry_decisions hm hd _ hs entry
  · simp [hs]

theorem matchCount_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (trace : List Entry) :
    matchCount T' messages' trace=matchCount T messages trace := by
  apply congrArg (fun mark => SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks mark trace)
  funext p entry
  exact propext (matchEntry_decisions hm hd entry)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cells_count_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (count : Answers → (LeafAddr → WCT9.LayerMsg) → List Entry → Nat) (rate : ENNReal)
    (hcount : ∀ {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg},
      (∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf) →
      DecisionsAgree T T' messages → ∀ trace, count T' messages' trace=count T messages trace)
    (hlazy : ∀ (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
        (program : OracleComp RefWorld (Option (Bool × Nat))),
      ∑' result, Pr[=result | (simulateQ (SigGolfCandidate.T3.Security.Wots.Enc.Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced SigGolfCandidate.T3.Security.Wots.Enc.Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (count T messages result.1.2.toList:ENNReal) ≤ rate *
        ∑' result, Pr[=result | (simulateQ (SigGolfCandidate.T3.Security.Wots.Enc.Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced SigGolfCandidate.T3.Security.Wots.Enc.Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal)) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub)
          (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable
          (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          (count (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
            (sourceMessages (eagerAnswers U privateTable pub))).cells pub y))
            (sourceMessages (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
              (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)))
            (traceOf (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
              (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r.2) : ENNReal) ≤
      rate * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub)
          (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable
          (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable
            (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) : ENNReal) := by
  have hleft := cell_transfer adversary q U hU privateTable pub
      (fun s => (count s.answers (sourceMessages s.answers) s.trace : ENNReal))
      (fun tr => (count (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr : ENNReal))
      (fun y hy r => by
        dsimp only [mkSample]
        rw [hcount (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)])
  simp only [mkSample] at hleft
  rw [hleft, cell_transfer adversary q U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y _ r => encodingCount_mkSample _ r)]
  exact hlazy _ _ _
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem reference_markerCount_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s *
      (markerCount s.answers (sourceMessages s.answers) s.trace : ENNReal) ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  apply reference_cells_le adversary q
  intro privateTable pub
  exact cells_count_le adversary q (PairedReference.referenceInputs adversary)
    Finset.subset_union_left privateTable pub markerCount _
    (fun hm hd trace => markerCount_decisions hm hd trace)
    (fun T messages program => lazy_marker_le T messages program)

theorem reference_matchCount_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s *
      (matchCount s.answers (sourceMessages s.answers) s.trace : ENNReal) ≤
      (7/((4:ENNReal)*2^128)) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  apply reference_cells_le adversary q
  intro privateTable pub
  exact cells_count_le adversary q (PairedReference.referenceInputs adversary)
    Finset.subset_union_left privateTable pub matchCount _
    (fun hm hd trace => matchCount_decisions hm hd trace)
    (fun T messages program => lazy_match_le T messages program)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem markerCount_marks_eq (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) :
    markerCount T messages trace = (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
      WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt T messages trace (Enc.chainAt p)).card := by
  unfold markerCount SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [markerAt_iff]
  constructor
  · rintro ⟨e,he,hs,hm⟩
    exact ⟨hs,e,he,hm⟩
  · rintro ⟨hs,e,he,hm⟩
    exact ⟨e,he,hs,hm⟩

theorem reference_marker_sum_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkerAt s.answers (sourceMessages s.answers) s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  refine le_trans (le_of_eq ?_) (reference_markerCount_le adversary q)
  simp only [probEvent_eq_tsum_ite,PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  rw [markerCount_marks_eq,Finset.card_filter,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

theorem matchCount_pos {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace : List Entry}
    {L : LeafAddr} (hsource : WotsExtract.SourceLeaf7 L)
    (hs : referenceSearch T messages L ≠ none) (hm : EncodingMatchAt T messages trace L) :
    1 ≤ matchCount T messages trace := by
  obtain ⟨message,counter,pad,answer,hfit,hmem,hne,-,hdecode⟩ := hm
  have ht31 : L.tree < 2^31 := lt_of_lt_of_le hsource.1
    (Nat.pow_le_pow_right (by decide) (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
  have hl12 : L.leaf < 4096 := lt_of_lt_of_le hsource.2 (by
    calc 2^height L.lay ≤ 2^12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le L.lay)
         _ = 4096 := by norm_num)
  unfold matchCount SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks
  apply Nat.succ_le_of_lt
  apply Finset.card_pos.mpr
  refine ⟨(),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  refine ⟨(encRow L message counter pad,answer),hmem,?_⟩
  exact ⟨⟨L.lay,⟨L.tree,ht31⟩,⟨L.leaf,hl12⟩⟩,message,counter,pad,hsource,hfit,rfl,hne,hs,hdecode⟩

theorem reference_encodingMatch_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ L, WotsExtract.SourceLeaf7 L ∧
      referenceSearch s.answers (sourceMessages s.answers) L ≠ none ∧
      EncodingMatchAt s.answers (sourceMessages s.answers) s.trace L |
        PairedReference.referenceExperiment adversary q] ≤
      (7/((4:ENNReal)*2^128)) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  refine le_trans ?_ (reference_matchCount_le adversary q)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro s
  split_ifs with h
  · obtain ⟨L,hsource,hs,hm⟩ := h
    rw [PMF.probOutput_eq_apply]
    exact le_mul_of_one_le_right' (by exact_mod_cast matchCount_pos hsource hs hm)
  · exact zero_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
