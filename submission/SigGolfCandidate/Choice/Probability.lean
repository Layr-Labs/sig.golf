import SigGolfCandidate.Choice.Search
import SigGolfCandidate.ClaudeWCT.WCT9.Basic

/-! Per-query bounds for the actual verifier's attacker-chosen selector.
These are local bounds, not the full adaptive security theorem. -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 ENNReal
open SigGolfCandidate.Choice
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ

/-- A security event must include every selector the adversary could supply. -/
def encodingCanDecode (lay : Layer) (answer : HashOutput) (digits : List Nat) : Prop :=
  ∃ hint : BitVec 64, decode lay (verificationAnswer lay hint answer) = some digits

theorem encodingCanDecode_honest (lay : Layer) (answer : HashOutput) (digits : List Nat)
    (h : decode lay (encodingAnswer lay answer) = some digits) :
    encodingCanDecode lay answer digits := by
  exact ⟨encodingHint lay answer, by rwa [verificationAnswer_honest]⟩

theorem encodingCanDecode_lower (lay : Layer) (hl : lay ≠ 0)
    (answer : HashOutput) (digits : List Nat) :
    encodingCanDecode lay answer digits ↔ decode lay (encodingAnswer lay answer) = some digits := by
  simp only [encodingCanDecode, verificationAnswer_lower lay hl, exists_const]

/-- A contact with producer-valid reference digits forces the canonical
search to stop, although it may stop on a different valid low word. -/
theorem encodingCanDecode_producer_contact (lay : Layer) (answer : HashOutput)
    (reference : Digest) (digits : List Nat)
    (href : producerDecode lay reference = some digits)
    (hit : encodingCanDecode lay answer digits) :
    ∃ values, producerDecode lay (encodingAnswer lay answer) = some values := by
  obtain ⟨hint, hdecode⟩ := hit
  have he := decode_some_injective hdecode (producerDecode_decode href)
  have hp : producerDecode lay (verificationAnswer lay hint answer) = some digits := by
    rwa [he]
  by_cases hl : lay = 0
  · subst lay
    cases hc : producerDecode 0 (encodingAnswer 0 answer) with
    | none =>
        have hn := top_rejected_no_witness answer hc hint
        rw [hp] at hn
        cases hn
    | some values => exact ⟨values, rfl⟩
  · exact ⟨digits, by simpa only [verificationAnswer_lower lay hl] using hp⟩

/-- Cardinality of the union over all hints, including choices made after
the complete hash output has been observed. -/
theorem verificationAnswer_top_exists_card (targets : Finset Digest) :
    (Finset.univ.filter fun answer : HashOutput =>
      ∃ hint : BitVec 64, verificationAnswer 0 hint answer ∈ targets).card ≤
      targets.card * (7 * 2 ^ 126) := by
  classical
  let allowed := Finset.univ.filter fun answer : HashOutput =>
    Selector.splitEquiv answer ∈ Gated.accepted targets Selector.blocked
  have hc : allowed.card = (Gated.accepted targets Selector.blocked).card := by
    apply Finset.card_equiv Selector.splitEquiv
    intro answer
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and]
  calc _ ≤ allowed.card := Finset.card_le_card (by
        intro answer ha
        obtain ⟨hint, hh⟩ := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Selector.branchRead_allowed targets _ hint hh⟩)
    _ = _ := hc
    _ ≤ _ := Selector.accepted_upper targets

theorem probability_top_verification_exists_le (targets : Finset Digest) :
    Pr[fun answer => ∃ hint : BitVec 64, verificationAnswer 0 hint answer ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (targets.card : ENNReal) * (7 / ((4 : ENNReal) * 2 ^ 128)) := by
  classical
  rw [probEvent_uniformSample]
  change ((Finset.univ.filter fun answer : HashOutput =>
      ∃ hint : BitVec 64, verificationAnswer 0 hint answer ∈ targets).card : ENNReal) /
      (Fintype.card HashOutput : ENNReal) ≤ _
  have hc : ((Finset.univ.filter fun answer : HashOutput =>
      ∃ hint : BitVec 64, verificationAnswer 0 hint answer ∈ targets).card : ENNReal) ≤
      (targets.card * (7 * 2 ^ 126) : Nat) := by
    exact_mod_cast verificationAnswer_top_exists_card targets
  calc _ ≤ (targets.card * (7 * 2 ^ 126) : Nat) / (Fintype.card HashOutput : ENNReal) :=
        ENNReal.div_le_div_right hc _
    _ = _ := by
      rw [Fintype.card_bitVec, Nat.cast_mul, mul_div_assoc]
      congr 1
      apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
      norm_num

theorem probability_verification_exists_le (lay : Layer) (targets : Finset Digest)
    (hp : lay ≠ 0 → ∀ word, word ∈ targets → lowerSpare word) :
    Pr[fun answer => ∃ hint : BitVec 64, verificationAnswer lay hint answer ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (targets.card : ENNReal) * (7 / ((4 : ENNReal) * 2 ^ 128)) := by
  classical
  by_cases hl : lay = 0
  · subst lay
    exact probability_top_verification_exists_le targets
  · have he : (fun answer => ∃ hint : BitVec 64, verificationAnswer lay hint answer ∈ targets) =
        (fun word => word ∈ targets) ∘ DualHalf.select := by
      funext answer
      simp only [verificationAnswer_lower lay hl, exists_const, Function.comp_apply,
        encodingAnswer, if_neg hl]
    rw [he, probability_lower_encoding _ (hp hl)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, le_refl]

theorem card_top_encoding_le (p : Digest → Prop) [DecidablePred p] :
    (Finset.univ.filter fun answer : HashOutput => p (encodingAnswer 0 answer)).card ≤
      (Finset.univ.filter p).card * (7 * 2 ^ 126) := by
  simpa only [verificationAnswer_honest, Finset.mem_filter, Finset.mem_univ, true_and] using
    verificationAnswer_top_card (Finset.univ.filter p) (encodingHint 0)

/-- The widened match event retains the 7/4 point coefficient at every layer. -/
theorem probability_encodingCanDecode_le (lay : Layer) (digits : List Nat) :
    Pr[fun answer => encodingCanDecode lay answer digits |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 7 / ((4 : ENNReal) * 2 ^ 128) := by
  classical
  let targets : Finset Digest := Finset.univ.filter fun word => decode lay word = some digits
  have hcard : targets.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact SigGolfCandidate.T3.decode_some_injective
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hc : (targets.card : ENNReal) ≤ 1 := by exact_mod_cast hcard
  by_cases hl : lay = 0
  · subst lay
    have he : (fun answer => encodingCanDecode 0 answer digits) =
        (fun answer => ∃ hint : BitVec 64, verificationAnswer 0 hint answer ∈ targets) := by
      funext answer
      simp only [encodingCanDecode, targets, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact (probability_top_verification_exists_le targets).trans
      (by simpa only [one_mul] using mul_le_mul' hc (le_refl (7 / ((4 : ENNReal) * 2 ^ 128))))
  · have hp : ∀ word, word ∈ targets → lowerSpare word := fun word hw =>
        SigGolfCandidate.T3.decode_lowerSpare hl (Finset.mem_filter.mp hw).2
    have he : (fun answer => encodingCanDecode lay answer digits) =
        (fun word => word ∈ targets) ∘ DualHalf.select := by
      funext answer
      simp only [encodingCanDecode_lower lay hl, Function.comp_apply,
        targets, Finset.mem_filter, Finset.mem_univ, true_and, encodingAnswer, if_neg hl]
    rw [he, probability_lower_encoding _ hp]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simpa only [one_mul] using mul_le_mul' hc (le_refl (7 / ((4 : ENNReal) * 2 ^ 128)))

end ClaudeWCT.WCT9

#print axioms ClaudeWCT.WCT9.verificationAnswer_top_exists_card
#print axioms ClaudeWCT.WCT9.probability_encodingCanDecode_le
