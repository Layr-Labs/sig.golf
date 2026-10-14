import SigGolfCandidate.Choice.Encoding
import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Choice
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ

/-- Every successful signing search has a corresponding expansion hint. -/
theorem layerCounterSearchHint_exists (answers : QueryImpl Spec Id)
    (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (found : BitVec 32) (digits : List Nat)
    (h : evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) =
      some (found, digits)) :
    ∃ hint, evalWithAnswerFn answers (layerCounterSearchHint lay tree leaf msg counter fuel) =
      some (found, digits, hint) := by
  have he := congrArg (evalWithAnswerFn answers)
    (layerCounterSearchHint_forget lay tree leaf msg counter fuel)
  rw [evalWithAnswerFn_map, h] at he
  cases hs : evalWithAnswerFn answers (layerCounterSearchHint lay tree leaf msg counter fuel) with
  | none => simp only [hs, Option.map_none, reduceCtorEq] at he
  | some result =>
      obtain ⟨c, ds, hint⟩ := result
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hint, rfl⟩

/-- Successful expansion searches replay the exact word used by signing. -/
theorem layerCounterSearchHint_some (answers : QueryImpl Spec Id)
    (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter found digits hint, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (layerCounterSearchHint lay tree leaf msg counter fuel) =
        some (found, digits, hint) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        hint = encodingHint lay (evalWithAnswerFn answers
          (publicHash (layerEncodingInput lay tree leaf msg found))) ∧
        producerDecode lay (evalWithAnswerFn answers
          (verificationHash lay hint (layerEncodingInput lay tree leaf msg found))) = some digits := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits hint _ he
      simp only [layerCounterSearchHint, evalWithAnswerFn_pure] at he
      cases he
  | succ fuel ih =>
      intro counter found digits hint hlimit he
      simp only [layerCounterSearchHint, evalWithAnswerFn_bind] at he
      cases hd : producerDecode lay (encodingAnswer lay (evalWithAnswerFn answers
          (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))))) with
      | none =>
          simp only [hd] at he
          obtain ⟨hlo, hhi, hh, hv⟩ := ih (counter + 1) found digits hint (by omega) he
          exact ⟨by omega, by omega, hh, hv⟩
      | some values =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          have hc : (BitVec.ofNat 32 counter).toNat = counter := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          refine ⟨by rw [hc], by rw [hc]; omega, rfl, ?_⟩
          simpa only [verificationHash, evalWithAnswerFn_map, verificationAnswer_honest] using hd

/-- Every earlier row of a successful canonical search was rejected. -/
theorem layerCounterSearchHint_before (answers : QueryImpl Spec Id)
    (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter found digits hint, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (layerCounterSearchHint lay tree leaf msg counter fuel) =
        some (found, digits, hint) →
      ∀ i, counter ≤ i → i < found.toNat →
        producerDecode lay (encodingAnswer lay (evalWithAnswerFn answers
          (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 i))))) = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits hint _ he
      simp only [layerCounterSearchHint, evalWithAnswerFn_pure] at he
      cases he
  | succ fuel ih =>
      intro counter found digits hint hlimit he i hlo hhi
      simp only [layerCounterSearchHint, evalWithAnswerFn_bind] at he
      cases hd : producerDecode lay (encodingAnswer lay (evalWithAnswerFn answers
          (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))))) with
      | none =>
          by_cases hi : i = counter
          · simpa only [hi] using hd
          · simp only [hd] at he
            exact ih (counter + 1) found digits hint (by omega) he i (by omega) hhi
      | some values =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          have hc : (BitVec.ofNat 32 counter).toNat = counter := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega

/-- A producer-valid target cannot be opened with any permitted hint at a
row which the canonical producer rejected. -/
theorem top_rejected_no_witness (answer : HashOutput)
    (rejected : producerDecode 0 (encodingAnswer 0 answer) = none)
    (hint : BitVec 64) : producerDecode 0 (verificationAnswer 0 hint answer) = none := by
  have hr : Gated.choose topProducerWords Selector.blocked (Selector.splitEquiv answer) ∉
      topProducerWords := by
    rw [← encodingAnswer_top_choose, mem_topProducerWords, rejected]
    decide
  have he := Gated.rejected_row_no_read topProducerWords Selector.blocked
    (Selector.splitEquiv answer) hr (decide (hint &&& 16 = 16))
  rw [← Selector.branchRead_eq_read] at he
  change verificationAnswer 0 hint answer ∉ topProducerWords at he
  rw [mem_topProducerWords] at he
  cases hd : producerDecode 0 (verificationAnswer 0 hint answer) with
  | none => rfl
  | some digits => simp only [hd, Option.isSome_some, not_true_eq_false] at he

/-- The actual search prefix has the no-contact property needed by the
adaptive coupling, including attacker-chosen hints on earlier rows. -/
theorem top_search_before_no_witness (answers : QueryImpl Spec Id)
    (tree leaf : Nat) (msg : LayerMsg) (fuel counter : Nat)
    (found : BitVec 32) (digits : List Nat) (honestHint : BitVec 64)
    (limit : counter + fuel ≤ 2 ^ 32)
    (searched : evalWithAnswerFn answers (layerCounterSearchHint 0 tree leaf msg counter fuel) =
      some (found, digits, honestHint)) (i : Nat) (lo : counter ≤ i) (hi : i < found.toNat)
    (hint : BitVec 64) :
    producerDecode 0 (evalWithAnswerFn answers (verificationHash 0 hint
      (layerEncodingInput 0 tree leaf msg (BitVec.ofNat 32 i)))) = none := by
  have h := layerCounterSearchHint_before answers 0 tree leaf msg fuel counter found digits
    honestHint limit searched i lo hi
  simpa only [verificationHash, evalWithAnswerFn_map] using top_rejected_no_witness _ h hint

end ClaudeWCT.WCT9

#print axioms ClaudeWCT.WCT9.layerCounterSearchHint_some
#print axioms ClaudeWCT.WCT9.layerCounterSearchHint_before
#print axioms ClaudeWCT.WCT9.top_rejected_no_witness
#print axioms ClaudeWCT.WCT9.top_search_before_no_witness
