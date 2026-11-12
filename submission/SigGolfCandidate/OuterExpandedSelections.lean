import SigGolfCandidate.OuterExpandedShape
import SigGolfCandidate.OuterHintBridge
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExpansionSecurity
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.CanonicalExtract
theorem expanded_canonical_selections (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig) = some (output,w,ns))
    (hg : ∀ lay, Good answers (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers) (Paired.witEncF16 output w)
      (WCT9.digestIndex output) lay)
    (hf : (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1 =
        OuterCanonicalModel.commitment answers (WCT9.digestIndex output)) :
    ∃ (digits : List (List Nat)) (lows : List Bool),
      OuterLifted.SigGolfCandidate.Research.SharedForest.policyHintsValid (WCT9.digestIndex output) w.signature.policyHints digits lows = true ∧
      (∀ lay, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (OuterLifted.SigGolfCandidate.Research.SharedForest.hintFloor (WCT9.digestIndex output) w.signature.policyHints lay) (route (WCT9.digestIndex output) lay).2
        (route (WCT9.digestIndex output) lay).1
        (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        0 (WCT9.searchLimit lay)) = some (w.counters lay, digits.getD lay.val [], lows.getD lay.val true)) ∧
      ∀ lay, w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (digits.getD lay.val [])) := by
  obtain ⟨_, counter, result, c, _, hr, hvalid, hsig, _, hcs, hhigh⟩ := OuterExpandSelections.selections answers message pk sig output w ns he
  have hs := SigGolfCandidate.Research.SharedForest.recoverHintedLayers_selections answers (fillTopSignature sig 0) (WCT9.digestIndex output)
    (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4 le_rfl _ result hr
  let input : WCT9.LayerMsg := .pair
    (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.1
    (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.2
  have hsel : ∀ lay, evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay (OuterLifted.SigGolfCandidate.Research.SharedForest.hintFloor (WCT9.digestIndex output) w.signature.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers w.signature (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val [],
          result.lows.getD lay.val true) := by
    intro lay
    have hx := hs.2.2.2 lay lay.isLt
    rw [OuterHintBridge.hintFloor_eq] at hx
    change evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay (OuterLifted.SigGolfCandidate.Research.SharedForest.hintFloor (WCT9.digestIndex output) sig.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers (fillTopSignature sig 0) (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = _ at hx
    rw [recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt 0] at hx
    rw [hsig, hints_retained, recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt c]
    exact hx
  have hshape0 := OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.good_shape_witEncF16 answers output w hg
  have hi : WCT9.digestIndex output < 2^31 := Nat.mod_lt _ (by decide)
  have lower : ∀ n, n < 3 → OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers
      (routeLeaf (WCT9.digestIndex output) (Fin.ofNat 4 n)) =
      .pair (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).1
        (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).2 := by
    intro n hn
    have hm := OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.sourceMessages_lower answers (WCT9.digestIndex output) hi (n+1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel, Extract.honestPair_eq] using hm
  have hin : input = OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 3) := by
    dsimp only [input]
    rw [hf, OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.sourceMessages_bottom answers _ hi]
    rfl
  have hshapeL : ∀ lay : Layer, lay ≠ 0 → ∃ ds, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        (result.counters.getD lay.val 0)))) = some ds ∧
      w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 ds) := by
    intro lay hl
    simpa only [hcs lay] using hshape0 lay (honestHint_lower answers _ _ _ hl)
  have htop := OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.recoveredMessage_top_source answers w.signature (WCT9.digestIndex output) input result
    (fun lay => OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay)) hin lower hsel hshapeL
  -- The expander's hint is the producer's choice at the (source) top row.
  have hhint0 : HonestHint answers (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers) (Paired.witEncF16 output w)
      (WCT9.digestIndex output) 0 := by
    have hs0 := hsel 0
    rw [htop] at hs0
    have hlim := WCT9.searchLimit_le 0
    have hlow := (canonical_search_some' answers 0 (OuterLifted.SigGolfCandidate.Research.SharedForest.hintFloor (WCT9.digestIndex output) w.signature.policyHints 0)
      (route (WCT9.digestIndex output) 0).2 (route (WCT9.digestIndex output) 0).1
      (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0)) (WCT9.searchLimit 0) 0
      (result.counters.getD 0 0) (result.digits.getD 0 []) (result.lows.getD 0 true)
      (by unfold counterLimit at hlim; omega) hs0).2.2.1
    obtain ⟨-, hpad, hhi⟩ := hg 0
    obtain ⟨left, right, hm⟩ := OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.sourceMessages_pair answers (routeLeaf (WCT9.digestIndex output) 0)
    unfold HonestHint
    rw [Paired.wbcCtr_witEncF16, hpad, hhi, Paired.wtopHigh_witEncF16, hhigh]
    have hrow : pad64 (layerEncodingInputP 0 (route (WCT9.digestIndex output) 0).2
        (route (WCT9.digestIndex output) 0).1 (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0))
        (w.counters 0) 0 (wbcRight (Paired.witEncF16 output w)) 1) =
        pad64 (WCT9.layerEncodingInput 0 (route (WCT9.digestIndex output) 0).2 (route (WCT9.digestIndex output) 0).1
          (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0)) (w.counters 0)) := by
      rw [hm]; rfl
    rw [hrow, hcs 0, hlow]
    exact WCT9.verificationAnswer_honest 0 _
  have hshape' : ∀ lay, ∃ ds, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        (result.counters.getD lay.val 0)))) = some ds ∧
      w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 ds) := by
    intro lay
    by_cases hl : lay = 0
    · subst hl
      simpa only [hcs 0] using hshape0 0 hhint0
    · exact hshapeL lay hl
  have hall := OuterLifted.SigGolfCandidate.Research.SharedForest.recoveredSelections_canonical answers w.signature (WCT9.digestIndex output)
    input result (fun lay => OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    hin lower hsel hshape'
  refine ⟨result.digits, result.lows, ?_, ?_, fun lay => (hall lay).2⟩
  · rw [hsig, hints_retained]
    exact hvalid
  · intro lay
    rw [hcs lay]
    exact (hall lay).1
#print axioms OuterExpansionSecurity.expanded_canonical_selections
end OuterExpansionSecurity
