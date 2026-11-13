import SigGolfCandidate.OuterPreparedFacts
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterPreparedCost
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
attribute [local irreducible] SigGolfCandidate.T3.SearchCost.cost CanonicalPolicy.layerCounterSearchAt
theorem cost_eq {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : OuterPreparedFacts.PreparedSearchFacts answers cache index prepared forest result)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2) :
    cost answers (OuterSigning.searchPreparedLayers cache index prepared forest) =
      recoverySearchCost answers sig index forest +
        cost answers (signTop cache (route index 0).1 (result.digits.getD 0 [])) := by
  have hs0 := h.search0
  rw [OuterSigning.root_floor index] at hs0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  have hf1 := Nat.not_le.mpr h.floor1_lt
  have hf2 := Nat.not_le.mpr h.floor2_lt
  have hf3 := Nat.not_le.mpr h.floor3_lt
  dsimp only [OuterPreparedFacts.preparedResidual1, OuterPreparedFacts.preparedResidual2, OuterPreparedFacts.preparedResidual3] at hs1 hs2 hs3 hf1 hf2 hf3
  simp only [OuterSigning.searchPreparedLayers, cost_bind, OuterSigning.root_floor, hs0, hs1, hs2, hs3,
    hf1, hf2, hf3, if_false, cost_pure, Nat.add_zero]
  simp only [recoverySearchCost, recoverySearch, hh, h.hints_spec.2.1,
    h.hints_spec.2.2.1, h.hints_spec.2.2.2, hm0, hm1, hm2,
    show hintFloor index result.policyHints 0 = 16 from by simpa only [hintFloor,if_pos rfl,↓reduceIte] using OuterPreparedFacts.old_root_floor index,
    show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl,
    OuterPreparedFacts.preparedResidual1, OuterPreparedFacts.preparedResidual2, OuterPreparedFacts.preparedResidual3]
  omega

theorem recovery_cost_le {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : OuterPreparedFacts.PreparedSearchFacts answers cache index prepared forest result)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (other : Digest) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2)
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2) :
    cost answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) ≤
      cost answers (OuterSigning.searchPreparedLayers cache index prepared forest) + (13124 + 106485) := by
  have hs0 := h.search0
  rw [OuterSigning.root_floor index] at hs0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  rw [hm0] at hs0
  rw [hm1] at hs1
  rw [hm2] at hs2
  have hs : ∀ lay, evalWithAnswerFn answers (recoverySearch answers sig index forest lay) =
      some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) := by
    intro lay
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [recoverySearch, hh, h.hints_spec.2.1, h.hints_spec.2.2.1, h.hints_spec.2.2.2,
        show hintFloor index result.policyHints 0 = 16 from by simpa only [hintFloor,if_pos rfl,↓reduceIte] using OuterPreparedFacts.old_root_floor index,
        show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
        show (2 : Layer) ≠ 3 by decide, if_false, if_true,
        show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
        show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
        show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl]
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3
  have hc := recoverHintedLayers_cost_replay answers sig index other forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  have he := cost_eq h sig hh hm0 hm1 hm2
  omega

#print axioms cost_eq
#print axioms recovery_cost_le
end OuterPreparedCost
