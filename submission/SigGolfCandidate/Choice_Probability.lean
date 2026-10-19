import SigGolfCandidate.ClaudeWCT_WCT9_Basic
set_option Elab.async false

/-! Restricted top choice (configuration (1)+(2)): per-query bounds for the verifier's attacker-chosen hint.
Adapted from `Choice/{Encoding,Probability,Target}.lean` of 311823ad to the Bool hint of
`ClaudeWCT.WCT9.verificationAnswer` (the witness byte's bit 4) and the `TopChoice` gate (LOW forced when
`LOW < 2^126`). These are local per-answer bounds; the adaptive security route threads them through. -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The 7/4 point-mass bound: the hint may depend on the complete hash output. -/
theorem verificationAnswer_top_card (targets : Finset Digest) (hint : HashOutput → Bool) :
    (Finset.univ.filter fun answer => verificationAnswer 0 (hint answer) answer ∈ targets).card ≤
      targets.card * (7 * 2 ^ 126) := by
  simpa only [verificationAnswer, if_true] using TopChoice.card_read_le targets hint

/-- Cardinality of the union over both hints. -/
theorem verificationAnswer_top_exists_card (targets : Finset Digest) :
    (Finset.univ.filter fun answer : HashOutput =>
      ∃ high : Bool, verificationAnswer 0 high answer ∈ targets).card ≤
      targets.card * (7 * 2 ^ 126) := by
  simpa only [verificationAnswer, if_true] using TopChoice.card_read_exists_le targets

/-- The producer's own top word obeys the same 7/4 bound. -/
theorem card_top_encoding_le (p : Digest → Prop) [DecidablePred p] :
    (Finset.univ.filter fun answer : HashOutput => p (encodingAnswer 0 answer)).card ≤
      (Finset.univ.filter p).card * (7 * 2 ^ 126) := by
  have h := verificationAnswer_top_card (Finset.univ.filter p) (encodingHigh 0)
  simpa only [verificationAnswer_honest, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem probability_top_verification_exists_le (targets : Finset Digest) :
    Pr[fun answer => ∃ high : Bool, verificationAnswer 0 high answer ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (targets.card : ENNReal) * (7 / ((4 : ENNReal) * 2 ^ 128)) := by
  classical
  rw [probEvent_uniformSample]
  change ((Finset.univ.filter fun answer : HashOutput =>
      ∃ high : Bool, verificationAnswer 0 high answer ∈ targets).card : ENNReal) /
      (Fintype.card HashOutput : ENNReal) ≤ _
  have hc : ((Finset.univ.filter fun answer : HashOutput =>
      ∃ high : Bool, verificationAnswer 0 high answer ∈ targets).card : ENNReal) ≤
      (targets.card * (7 * 2 ^ 126) : Nat) := by
    exact_mod_cast verificationAnswer_top_exists_card targets
  calc _ ≤ (targets.card * (7 * 2 ^ 126) : Nat) / (Fintype.card HashOutput : ENNReal) :=
        ENNReal.div_le_div_right hc _
    _ = _ := by
      rw [Fintype.card_bitVec, Nat.cast_mul, mul_div_assoc]
      congr 1
      apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
      norm_num

/-- A security event must include every hint the adversary could supply. -/
def encodingCanDecode (lay : Layer) (answer : HashOutput) (digits : List Nat) : Prop :=
  ∃ high : Bool, CanonicalPolicy.decode lay (verificationAnswer lay high answer) = some digits

theorem encodingCanDecode_honest (lay : Layer) (answer : HashOutput) (digits : List Nat)
    (h : CanonicalPolicy.decode lay (encodingAnswer lay answer) = some digits) :
    encodingCanDecode lay answer digits :=
  ⟨encodingHigh lay answer, by rwa [verificationAnswer_honest]⟩

theorem encodingCanDecode_lower (lay : Layer) (hl : lay ≠ 0)
    (answer : HashOutput) (digits : List Nat) :
    encodingCanDecode lay answer digits ↔
      CanonicalPolicy.decode lay (encodingAnswer lay answer) = some digits := by
  simp only [encodingCanDecode, verificationAnswer_lower lay hl, exists_const]

theorem probability_verification_exists_le (lay : Layer) (targets : Finset Digest)
    (hp : lay ≠ 0 → ∀ word, word ∈ targets → lowerSpare word) :
    Pr[fun answer => ∃ high : Bool, verificationAnswer lay high answer ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (targets.card : ENNReal) * (7 / ((4 : ENNReal) * 2 ^ 128)) := by
  classical
  by_cases hl : lay = 0
  · subst lay
    exact probability_top_verification_exists_le targets
  · have he : (fun answer => ∃ high : Bool, verificationAnswer lay high answer ∈ targets) =
        (fun word => word ∈ targets) ∘ DualHalf.select := by
      funext answer
      simp only [verificationAnswer, if_neg hl, exists_const, Function.comp_apply]
    rw [he, probability_lower_encoding _ (hp hl)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, le_refl]

theorem canonical_decode_injective {lay : Layer} {a b : Digest} {digits : List Nat}
    (ha : CanonicalPolicy.decode lay a = some digits) (hb : CanonicalPolicy.decode lay b = some digits) :
    a = b :=
  SigGolfCandidate.T3.decode_some_injective ha hb

/-- The widened match event retains the 7/4 point coefficient at every layer. -/
theorem probability_encodingCanDecode_le (lay : Layer) (digits : List Nat) :
    Pr[fun answer => encodingCanDecode lay answer digits |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 7 / ((4 : ENNReal) * 2 ^ 128) := by
  classical
  let targets : Finset Digest := Finset.univ.filter fun word => CanonicalPolicy.decode lay word = some digits
  have hcard : targets.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact canonical_decode_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hc : (targets.card : ENNReal) ≤ 1 := by exact_mod_cast hcard
  have hp : lay ≠ 0 → ∀ word, word ∈ targets → lowerSpare word := by
    intro hl word hw
    have hd := (Finset.mem_filter.mp hw).2
    simp only [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, if_neg hl] at hd
    exact SigGolfCandidate.T3.decode_lowerSpare (by decide : (1 : Layer) ≠ 0) hd
  have he : (fun answer => encodingCanDecode lay answer digits) =
      (fun answer => ∃ high : Bool, verificationAnswer lay high answer ∈ targets) := by
    funext answer
    simp only [encodingCanDecode, targets, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he]
  exact (probability_verification_exists_le lay targets hp).trans
    (by simpa only [one_mul] using mul_le_mul' hc (le_refl (7 / ((4 : ENNReal) * 2 ^ 128))))

/-- The residual probe must test every permitted witness opening: the target word is reachable iff it is LOW or
(LOW is not forced and it is HIGH). -/
def encodingTarget (lay : Layer) (target : Digest) (answer : HashOutput) : Digest :=
  if lay = 0 then
    if answer.extractLsb' 0 128 = target ∨ TopChoice.blocked (answer.extractLsb' 0 128)
      then answer.extractLsb' 0 128 else answer.extractLsb' 128 128
  else encodingAnswer lay answer

theorem verificationAnswer_top_exists_iff (answer : HashOutput) (target : Digest) :
    (∃ high : Bool, verificationAnswer 0 high answer = target) ↔
      answer.extractLsb' 0 128 = target ∨
        (¬ TopChoice.blocked (answer.extractLsb' 0 128) ∧ answer.extractLsb' 128 128 = target) := by
  show (∃ high : Bool, TopChoice.read high answer = target) ↔
    TopChoice.lowHalf answer = target ∨
      (¬ TopChoice.blocked (TopChoice.lowHalf answer) ∧ TopChoice.highHalf answer = target)
  by_cases hb : TopChoice.blocked (TopChoice.lowHalf answer)
  · simp only [TopChoice.read_blocked _ hb, exists_const, hb, not_true_eq_false, false_and, or_false]
  · have ht : TopChoice.read true answer = TopChoice.highHalf answer := by simp [TopChoice.read, hb]
    constructor
    · rintro ⟨high, hh⟩
      cases high
      · rw [TopChoice.read_false] at hh; exact Or.inl hh
      · rw [ht] at hh; exact Or.inr ⟨hb, hh⟩
    · rintro (hl | ⟨_, hh⟩)
      · exact ⟨false, by rw [TopChoice.read_false]; exact hl⟩
      · exact ⟨true, by rw [ht]; exact hh⟩

theorem verificationAnswer_exists_iff_target (lay : Layer) (answer : HashOutput) (target : Digest) :
    (∃ high : Bool, verificationAnswer lay high answer = target) ↔
      encodingTarget lay target answer = target := by
  by_cases hl : lay = 0
  · subst lay
    rw [verificationAnswer_top_exists_iff]
    simp only [encodingTarget, if_true]
    by_cases ht : answer.extractLsb' 0 128 = target <;>
      by_cases hg : TopChoice.blocked (answer.extractLsb' 0 128) <;>
      simp_all
  · simp only [verificationAnswer_lower lay hl, exists_const, encodingTarget, if_neg hl]

theorem encodingCanDecode_iff_target (lay : Layer) (answer : HashOutput)
    (target : Digest) (digits : List Nat) (href : CanonicalPolicy.decode lay target = some digits) :
    encodingCanDecode lay answer digits ↔ encodingTarget lay target answer = target := by
  rw [← verificationAnswer_exists_iff_target]
  constructor
  · rintro ⟨high, hh⟩
    exact ⟨high, canonical_decode_injective hh href⟩
  · rintro ⟨high, hh⟩
    exact ⟨high, hh ▸ href⟩

end ClaudeWCT.WCT9

#print axioms ClaudeWCT.WCT9.verificationAnswer_top_card
#print axioms ClaudeWCT.WCT9.card_top_encoding_le
#print axioms ClaudeWCT.WCT9.probability_encodingCanDecode_le
#print axioms ClaudeWCT.WCT9.encodingCanDecode_iff_target
