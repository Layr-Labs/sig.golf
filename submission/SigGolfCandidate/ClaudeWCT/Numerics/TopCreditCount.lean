import SigGolfCandidate.T3.Nonbinary.CreditFilter

namespace ClaudeWCT.Numerics.TopCredit
open Finset
open SigGolfResearch.NonbinaryTop
open SigGolfResearch.NonbinaryTop.Codec (Word encode encode_bound encode_injective)
open SigGolfResearch.NonbinaryTop.Counting (weight radix word_card_small)
open SigGolfResearch.NonbinaryTop.CreditCounting (credit stat stat_eq credit_le packed truncated_card)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.constructorNameAsVariable false
/-- Campaign T8D (NF17, 51 r5 + 3 r8): accepted top words at target 144 with at least 8 credits (about one in 2907). -/
def topCount144 : ℕ := 117045744219961653783874307332422420
theorem exact_packed_144_8 :
    (packed % radix ^ 9280) % (radix - 1) - (packed % radix ^ (9216 + 8)) % (radix - 1) = topCount144 := by
  decide +kernel
theorem credited_card_of (T f n : ℕ) (hf : f ≤ 64) (hT : 0 < T)
    (h : (packed % radix ^ (64 * T + 64)) % (radix - 1) - (packed % radix ^ (64 * T + f)) % (radix - 1) = n) :
    (univ.filter fun w : Word => weight w = T ∧ f ≤ credit w).card = n := by
  classical
  have hs : (univ.filter fun w : Word => weight w = T ∧ f ≤ credit w) =
      (univ.filter fun w : Word => stat w < 64 * T + 64) \ (univ.filter fun w : Word => stat w < 64 * T + f) := by
    ext w
    have hc := credit_le w
    have he := stat_eq w
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; omega
    · rintro ⟨h1, h2⟩
      have hw : weight w = T := by
        rcases Nat.lt_or_ge (weight w) T with h3 | h3
        · have : 64 * weight w + 64 ≤ 64 * T := by omega
          omega
        · rcases Nat.lt_or_ge T (weight w) with h4 | h4
          · have : 64 * T + 64 ≤ 64 * weight w := by omega
            omega
          · omega
      omega
  rw [hs, card_sdiff_of_subset]
  · rw [truncated_card _ (by omega), truncated_card _ (by omega), h]
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    omega
theorem credited_card_144_8 :
    (univ.filter fun w : Word => weight w = 144 ∧ 8 ≤ credit w).card = topCount144 :=
  credited_card_of 144 8 _ (by norm_num) (by norm_num) exact_packed_144_8
theorem card_parse_filter (P : Word → Prop) [DecidablePred P] :
    (univ.filter fun v : BitVec 128 => ∃ w, Decoder.parse 17 v.toNat = some w ∧ P w).card =
      (univ.filter P).card := by
  classical
  have hlt : ∀ w : Word, encode w < 2 ^ 128 := encode_bound
  have himage : (univ.filter fun v : BitVec 128 => ∃ w, Decoder.parse 17 v.toNat = some w ∧ P w) =
      (univ.filter P).image fun w => BitVec.ofNat 128 (encode w) := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨w, hp, hw⟩
      refine ⟨w, hw, ?_⟩
      have he : encode w = v.toNat := (Decoder.encodeN_word w).symm.trans (Decoder.encodeN_parse hp)
      rw [he]
      exact BitVec.ofNat_toNat ..
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, ?_, hw⟩
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hlt w), ← Decoder.encodeN_word]
      exact Decoder.parse_encodeN w
  rw [himage, card_image_of_injective]
  intro a b h
  apply encode_injective
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hlt a), Nat.mod_eq_of_lt (hlt b)] at h'
  exact h'
end ClaudeWCT.Numerics.TopCredit
