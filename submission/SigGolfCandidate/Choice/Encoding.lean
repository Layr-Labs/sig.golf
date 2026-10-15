import SigGolfCandidate.ClaudeWCT.WCT9.Core

/-! Source-level bridge for the restricted encoding selector. -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Choice
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ

def topProducerWords : Finset Digest :=
  Finset.univ.filter fun word => (producerDecode 0 word).isSome

@[simp] theorem mem_topProducerWords (word : Digest) :
    word ∈ topProducerWords ↔ (producerDecode 0 word).isSome = true := by
  simp only [topProducerWords, Finset.mem_filter, Finset.mem_univ, true_and]

theorem topChooseLow_eq (answer : HashOutput) :
    topChooseLow answer = true ↔
      answer.extractLsb' 0 128 ∈ topProducerWords ∨
      answer.extractLsb' 0 128 ∈ Selector.blocked := by
  simp only [topChooseLow, Bool.or_eq_true, decide_eq_true_eq, mem_topProducerWords,
    Selector.blocked, Finset.mem_filter, Finset.mem_univ, true_and]

theorem encodingAnswer_top_choose (answer : HashOutput) :
    encodingAnswer 0 answer = Gated.choose topProducerWords Selector.blocked
      (Selector.splitEquiv answer) := by
  simp only [encodingAnswer, if_true, Gated.choose, Selector.splitEquiv,
    Equiv.coe_fn_mk, topChooseLow_eq]

theorem encodingHint_top (answer : HashOutput) :
    encodingHint 0 answer =
      if answer.extractLsb' 0 128 ∈ topProducerWords ∨
          answer.extractLsb' 0 128 ∈ Selector.blocked then 0 else 16 := by
  by_cases h : topChooseLow answer = true
  · simp only [encodingHint, true_and, h, Bool.true_eq_false, if_false,
      if_pos ((topChooseLow_eq answer).mp h)]
  · have hf : topChooseLow answer = false := Bool.eq_false_iff.mpr h
    simp only [encodingHint, true_and, hf, if_true,
      if_neg (fun he => h ((topChooseLow_eq answer).mpr he))]

/-- The expander's canonical hint selects exactly the signer's word. -/
theorem verificationAnswer_honest (lay : Layer) (answer : HashOutput) :
    verificationAnswer lay (encodingHint lay answer) answer = encodingAnswer lay answer := by
  by_cases hl : lay = 0
  · subst lay
    rw [verificationAnswer, if_pos rfl, encodingHint_top, encodingAnswer_top_choose]
    exact Selector.branchRead_canonical topProducerWords (Selector.splitEquiv answer)
  · simp only [verificationAnswer, encodingAnswer, hl, if_false]

theorem verificationAnswer_lower (lay : Layer) (hl : lay ≠ 0)
    (hint : BitVec 64) (answer : HashOutput) :
    verificationAnswer lay hint answer = encodingAnswer lay answer := by
  simp only [verificationAnswer, encodingAnswer, hl, if_false]

theorem verificationHash_lower (lay : Layer) (hl : lay ≠ 0)
    (hint : BitVec 64) (input : HashInput) :
    verificationHash lay hint input = encodingHash lay input := by
  unfold verificationHash encodingHash
  congr 1
  funext answer
  exact verificationAnswer_lower lay hl hint answer

theorem verificationHash_hints_lower (lay : Layer) (hl : lay ≠ 0)
    (left right : BitVec 64) (input : HashInput) :
    verificationHash lay left input = verificationHash lay right input := by
  rw [verificationHash_lower lay hl, verificationHash_lower lay hl]

theorem verificationHash_bind {β : Type} (lay : Layer) (hint : BitVec 64)
    (input : HashInput) (f : Digest → M β) :
    verificationHash lay hint input >>= f = publicHash input >>= fun a =>
      f (verificationAnswer lay hint a) := by
  unfold verificationHash
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

theorem verificationHash_congr (lay : Layer) (hint : BitVec 64)
    {x y : HashInput} (h : pad64 x = pad64 y) :
    verificationHash lay hint x = verificationHash lay hint y := by
  unfold verificationHash publicHash
  rw [h]

/-- Retaining a hint changes neither successful counters/digits nor the oracle
program after the result is projected. In particular it adds no hash query. -/
theorem layerCounterSearchHint_forget (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (counter fuel : Nat) :
    (Option.map fun x : BitVec 32 × List Nat × BitVec 64 => (x.1, x.2.1)) <$>
        layerCounterSearchHint lay tree leaf msg counter fuel =
      layerCounterSearch lay tree leaf msg counter fuel := by
  induction fuel generalizing counter with
  | zero => simp only [layerCounterSearchHint, layerCounterSearch, map_pure, Option.map_none]
  | succ fuel ih =>
      rw [layerCounterSearchHint, layerCounterSearch, encodingHash_bind, map_bind]
      congr 1
      funext answer
      cases hd : producerDecode lay (encodingAnswer lay answer) with
      | none => simpa only [hd] using ih (counter + 1)
      | some digits => simp only [hd, map_pure, Option.map_some]

/-- This bound allows the hint to depend on the entire hash output. -/
theorem verificationAnswer_top_card (targets : Finset Digest) (hint : HashOutput → BitVec 64) :
    (Finset.univ.filter fun answer => verificationAnswer 0 (hint answer) answer ∈ targets).card ≤
      targets.card * (7 * 2 ^ 126) := by
  simpa only [verificationAnswer, if_true] using
    Selector.arbitrary_hash_witness_card targets hint

end ClaudeWCT.WCT9

#print axioms ClaudeWCT.WCT9.verificationAnswer_honest
#print axioms ClaudeWCT.WCT9.layerCounterSearchHint_forget
#print axioms ClaudeWCT.WCT9.verificationAnswer_top_card
