import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode
import SigGolfCandidate.ClaudeWCT.Numerics.LowerCreditCount
import SigGolfCandidate.ClaudeWCT.Numerics.TopCreditCount
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.CompletenessV5

namespace ClaudeWCT.W9.T3.ProducerV5
open OracleComp OracleSpec ENNReal Finset
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfResearch.NonbinaryTop
open ClaudeWCT.WCT9 (producerDecode producerFloor wordCredit searchLimit)
open ClaudeWCT.W9.T3.BaseAudit
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
def producerEncodingDecode (lay : Layer) (answer : HashOutput) : Option (List Nat) :=
  producerDecode lay (answer.extractLsb' 0 128)
theorem filter_range_getD (l : List ℕ) :
    ((List.range l.length).filter fun i => l.getD i 0 + 1 = 7).length = l.count 6 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hf : ((fun i => decide ((a :: l).getD i 0 + 1 = 7)) ∘ Nat.succ) = fun i => decide (l.getD i 0 + 1 = 7) := by
      funext i; simp
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, List.count_cons, hf]
    by_cases ha : a = 6
    · subst ha
      rw [if_pos (by simp), List.length_cons, List.length_map, ih]
      simp
    · rw [if_neg (by simp; omega), List.length_map, ih]
      simp [ha]
theorem dataDigits_lower (lay : Layer) (hl : lay ≠ 0) (v : Digest) :
    dataDigits lay v = ClaudeWCT.Numerics.LowerCredit.lowerDigits v.toNat := by
  simp [dataDigits, dataCount, hl, coreDigit, ClaudeWCT.Numerics.LowerCredit.lowerDigits]
theorem wordCredit_lower (lay : Layer) (hl : lay ≠ 0) (ds : List ℕ) (hlen : ds.length = 43) :
    wordCredit lay ds = ds.count 6 := by
  have hc : chainCount lay = 43 := by fin_cases lay <;> simp_all [chainCount]
  have hm : ∀ i, maxDigit lay i = 7 := by intro i; simp [maxDigit, hl]
  unfold wordCredit
  rw [hc, ← hlen]
  simp only [hm]
  exact filter_range_getD ds
theorem producerDecode_lower_isSome_iff (lay : Layer) (hl : lay ≠ 0) (v : Digest) :
    (producerDecode lay v).isSome ↔
      ClaudeWCT.Numerics.LowerCredit.LowerAccept (target lay) (producerFloor lay) v.toNat := by
  set L := ClaudeWCT.Numerics.LowerCredit.lowerDigits v.toNat with hL
  have hlen : (L ++ [target lay - L.sum]).length = 43 := by simp [hL, ClaudeWCT.Numerics.LowerCredit.lowerDigits]
  have hdec : decode lay v = if 2 ^ 126 ≤ v.toNat then none else
      if L.sum ≤ target lay ∧ target lay - L.sum < 8 then some (L ++ [target lay - L.sum]) else none := by
    simp only [decode, hl, encodedBits, if_false, dataDigits_lower lay hl, hL]
  unfold producerDecode ClaudeWCT.Numerics.LowerCredit.LowerAccept
  rw [hdec, ← hL]
  by_cases h1 : 2 ^ 126 ≤ v.toNat
  · rw [if_pos h1]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro h
    exact absurd h.1 (by omega)
  · rw [if_neg h1]
    by_cases h2 : L.sum ≤ target lay ∧ target lay - L.sum < 8
    · rw [if_pos h2]
      simp only
      rw [wordCredit_lower lay hl _ hlen]
      constructor
      · intro h
        split_ifs at h with h3
        · exact ⟨by omega, h2.1, h2.2, h3⟩
        · simp at h
      · intro h
        rw [if_pos h.2.2.2]
        rfl
    · rw [if_neg h2]
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨-, h3, h4, -⟩
      exact h2 ⟨h3, h4⟩
theorem card_producer_lower (lay : Layer) (hl : lay ≠ 0) (T f n : ℕ) (hT : target lay = T)
    (hf : producerFloor lay = f)
    (hn : (univ.filter fun v : BitVec 128 => ClaudeWCT.Numerics.LowerCredit.LowerAccept T f v.toNat).card = n) :
    (univ.filter fun v : Digest => (producerDecode lay v).isSome).card = n := by
  rw [← hn]
  exact congrArg Finset.card (filter_congr fun v _ => by rw [producerDecode_lower_isSome_iff lay hl, hT, hf])
theorem filter_length_eq_sum (l : List ℕ) (p : ℕ → Bool) :
    (l.filter p).length = (l.map fun i => if p i then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← ih]
    split <;> simp_all
    omega
theorem wordCredit_top (v : Digest) : wordCredit 0 (dataDigits 0 v) = topCredit v := by
  unfold wordCredit topCredit
  rw [show chainCount 0 = 54 from rfl, filter_length_eq_sum]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < 54 := List.mem_range.mp hi
  have hg : (dataDigits 0 v).getD i 0 = coreDigit 0 v i := by
    simp [dataDigits, dataCount, hi']
  rw [hg]
  by_cases h51 : i < 51
  · simp only [maxDigit, h51, if_true]
    split_ifs <;> simp_all
  · simp only [maxDigit, h51, if_true, if_false]
    split_ifs <;> simp_all
theorem decode_top_eq (v : Digest) : decode 0 v = if 2 ^ 125 ≤ v.toNat then none else
    if topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0 then some (dataDigits 0 v) else none := by
  simp only [decode, encodedBits, if_true]
  by_cases h1 : 2 ^ 125 ≤ v.toNat
  · simp
  · simp only [h1, if_false]
    by_cases h2 : topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0
    · simp [h2.1, h2.2]
    · rw [if_neg h2]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [if_neg h2]
theorem producerDecode_top_isSome_iff (v : Digest) :
    (producerDecode 0 v).isSome ↔ ∃ w, Decoder.parse 17 v.toNat = some w ∧
      Counting.weight w = target 0 ∧ producerFloor 0 ≤ CreditCounting.credit w := by
  unfold producerDecode
  rw [decode_top_eq]
  constructor
  · intro h
    by_cases h1 : 2 ^ 125 ≤ v.toNat
    · rw [if_pos h1] at h; simp at h
    · rw [if_neg h1] at h
      by_cases h2 : topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0
      · rw [if_pos h2] at h
        simp only at h
        split_ifs at h with h3
        · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
            ((SigGolfCandidate.T3.Nonbinary.parse_top_isSome_iff v).mpr ⟨by omega, h2.1⟩)
          refine ⟨w, hw, ?_, ?_⟩
          · rw [← SigGolfCandidate.T3.Nonbinary.wordDigits_sum, ← SigGolfCandidate.T3.Nonbinary.dataDigits_parse hw]
            exact h2.2
          · rw [← SigGolfCandidate.T3.Nonbinary.topCredit_parse hw, ← wordCredit_top]
            exact h3
        · simp at h
      · rw [if_neg h2] at h; simp at h
  · rintro ⟨w, hw, hweight, hcredit⟩
    have hp := (SigGolfCandidate.T3.Nonbinary.parse_top_isSome_iff v).mp (by rw [hw]; rfl)
    have h2 : topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0 := by
      refine ⟨hp.2, ?_⟩
      rw [SigGolfCandidate.T3.Nonbinary.dataDigits_parse hw, SigGolfCandidate.T3.Nonbinary.wordDigits_sum]
      exact hweight
    rw [if_neg (by omega), if_pos h2]
    simp only
    rw [if_pos (by rw [wordCredit_top, SigGolfCandidate.T3.Nonbinary.topCredit_parse hw]; exact hcredit)]
    rfl
theorem card_producer_top (T f n : ℕ) (hT : target 0 = T) (hf : producerFloor 0 = f)
    (hn : (univ.filter fun w : Codec.Word => Counting.weight w = T ∧ f ≤ CreditCounting.credit w).card = n) :
    (univ.filter fun v : Digest => (producerDecode 0 v).isSome).card = n := by
  classical
  rw [← hn, ← ClaudeWCT.Numerics.TopCredit.card_parse_filter]
  exact congrArg Finset.card (filter_congr fun v _ => by rw [producerDecode_top_isSome_iff, hT, hf])
def producerCount (lay : Layer) : ℕ := ![V5.topCount129, V5.lowerCount197, V5.lowerCount197, V5.lowerCount198] lay
theorem card_producerDecode (lay : Layer) :
    (univ.filter fun v : Digest => (producerDecode lay v).isSome).card = producerCount lay := by
  fin_cases lay
  · exact card_producer_top 129 7 _ rfl rfl ClaudeWCT.Numerics.TopCredit.credited_card_129_7
  · exact card_producer_lower 1 (by decide) 197 4 _ rfl rfl ClaudeWCT.Numerics.LowerCredit.card_lowerAccept_197_4
  · exact card_producer_lower 2 (by decide) 197 4 _ rfl rfl ClaudeWCT.Numerics.LowerCredit.card_lowerAccept_197_4
  · exact card_producer_lower 3 (by decide) 198 2 _ rfl rfl ClaudeWCT.Numerics.LowerCredit.card_lowerAccept_198_2
theorem producer_uniform_probability (lay : Layer) :
    Pr[fun answer => (producerEncodingDecode lay answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (producerCount lay : ENNReal) / 2 ^ 128 := by
  classical
  rw [probEvent_uniformSample]
  have hc := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128)
    (by decide) (fun value => (producerDecode lay value).isSome)
  have hc' : (univ.filter fun answer : HashOutput => (producerEncodingDecode lay answer).isSome).card =
      (univ.filter fun value : Digest => (producerDecode lay value).isSome).card * 2 ^ (256 - 128) := hc
  rw [hc', card_producerDecode]
  simp only [Fintype.card_bitVec, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)
noncomputable def producerRate (lay : Layer) : ℝ := (producerCount lay : ℝ) / 2 ^ 128
theorem producerRate_bounds (lay : Layer) : 1 / 4096 ≤ producerRate lay ∧ producerRate lay ≤ 1 := by
  fin_cases lay <;>
    norm_num [producerRate, producerCount, V5.topCount129, V5.lowerCount197, V5.lowerCount198]
theorem producer_failMass (lay : Layer) :
    failMass (producerEncodingDecode lay) = ENNReal.ofReal (1 - producerRate lay) := by
  rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept, producer_uniform_probability,
    ENNReal.ofReal_sub 1 (by linarith [(producerRate_bounds lay).1]), ENNReal.ofReal_one]
  congr 1
  rw [producerRate, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
theorem producer_failure_power (lay : Layer) :
    failMass (producerEncodingDecode lay) ^ searchLimit lay ≤ 1 / (2 : ENNReal) ^ 1024 := by
  have hp := producer_uniform_probability lay
  fin_cases lay
  · exact ClaudeWCT.W9.T3.Budgets.V5.top_failure_power _ hp
  · exact ClaudeWCT.W9.T3.Budgets.V5.lower197_failure_power _ hp
  · exact ClaudeWCT.W9.T3.Budgets.V5.lower197_failure_power _ hp
  · exact ClaudeWCT.W9.T3.Budgets.V5.lower198_failure_power _ hp
end ClaudeWCT.W9.T3.ProducerV5
