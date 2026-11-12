import SigGolfCandidate.OuterSigning
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterPreparedFacts
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest

theorem old_root_floor (index : Nat) : Policy75Safe23.threshold 0 (SigGolfCandidate.Research.SharedForest.requiredCredit index)=18 := by
  rw [Policy75Safe23.threshold_top]
  have h:=SigGolfCandidate.Research.SharedForest.requiredCredit_bounds index
  omega

def preparedResidual1 (index : Nat) (result : CanonicalLayers) : Nat :=
  routeResidual index ((OuterSigning.requiredCredit index)) 0 (result.lows.getD 0 true) (result.digits.getD 0 [])

def preparedResidual2 (index : Nat) (result : CanonicalLayers) : Nat :=
  routeResidual index (preparedResidual1 index result) 1 (result.lows.getD 1 true) (result.digits.getD 1 [])

def preparedResidual3 (index : Nat) (result : CanonicalLayers) : Nat :=
  routeResidual index (preparedResidual2 index result) 2 (result.lows.getD 2 true) (result.digits.getD 2 [])

/-- The successful source program exposes exactly the four canonical searches,
with every lower threshold determined by its already selected ancestors. -/
structure PreparedSearchFacts (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers) : Prop where
  pieces_length : result.pieces.length = 4
  counters_length : result.counters.length = 4
  digits_length : result.digits.length = 4
  lows_length : result.lows.length = 4
  search0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) =
      some (result.counters.getD 0 0, result.digits.getD 0 [], result.lows.getD 0 true)
  search1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
    (Policy75Safe23.threshold 1 (preparedResidual1 index result)) (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) =
      some (result.counters.getD 1 0, result.digits.getD 1 [], result.lows.getD 1 true)
  search2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
    (Policy75Safe23.threshold 2 (preparedResidual2 index result)) (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) =
      some (result.counters.getD 2 0, result.digits.getD 2 [], result.lows.getD 2 true)
  search3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
    (Policy75Safe23.threshold 3 (preparedResidual3 index result)) (route index 3).2 (route index 3).1
    (.pair (forest).1 (forest).2) 0 (searchLimit 3)) =
      some (result.counters.getD 3 0, result.digits.getD 3 [], result.lows.getD 3 true)
  floor1_lt : Policy75Safe23.threshold 1 (preparedResidual1 index result) < 17
  floor2_lt : Policy75Safe23.threshold 2 (preparedResidual2 index result) < 24
  floor3_lt : Policy75Safe23.threshold 3 (preparedResidual3 index result) < 24
  residual_eq : result.residual = CanonicalPolicy.nextResidual (preparedResidual3 index result) 3
    (result.lows.getD 3 true) (result.digits.getD 3 [])
  hints_eq : result.policyHints = BitVec.ofNat 16
    (576 * Policy75Safe23.threshold 1 (preparedResidual1 index result) +
     24 * Policy75Safe23.threshold 2 (preparedResidual2 index result) +
     Policy75Safe23.threshold 3 (preparedResidual3 index result))
  pieces_eq : result.pieces = [
    evalWithAnswerFn answers (signTop cache (route index 0).1 (result.digits.getD 0 [])),
    preparedPieces 1 (route index 1).1 prepared.one (result.digits.getD 1 []),
    preparedPieces 2 (route index 2).1 prepared.two (result.digits.getD 2 []),
    preparedPieces 3 (route index 3).1 prepared.three (result.digits.getD 3 [])]

theorem searchPreparedLayers_some (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers)
    (he : evalWithAnswerFn answers (OuterSigning.searchPreparedLayers cache index prepared forest) = some result) :
    PreparedSearchFacts answers cache index prepared forest result := by
  unfold OuterSigning.searchPreparedLayers at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) with
  | none => simp only [hs0, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found0 =>
      obtain ⟨c0, d0, l0⟩ := found0
      simp only [hs0, evalWithAnswerFn_bind] at he
      let r1 := routeResidual index (OuterSigning.requiredCredit index) 0 l0 d0
      let f1 := Policy75Safe23.threshold 1 r1
      by_cases hf1 : f1 ≥ 17
      · dsimp only [r1, f1] at hf1
        simp only [hf1, if_true,
          evalWithAnswerFn_pure, reduceCtorEq] at he
      dsimp only [r1, f1] at hf1
      simp only [hf1, if_false,
        evalWithAnswerFn_bind] at he
      cases hs1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
        f1 (route index 1).2 (route index 1).1
        (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) with
      | none =>
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found1 =>
          obtain ⟨c1, d1, l1⟩ := found1
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_bind] at he
          let r2 := routeResidual index r1 1 l1 d1
          let f2 := Policy75Safe23.threshold 2 r2
          by_cases hf2 : f2 ≥ 24
          · dsimp only [r1, f1, r2, f2] at hf2
            simp only [hf2, if_true,
              evalWithAnswerFn_pure, reduceCtorEq] at he
          dsimp only [r1, f1, r2, f2] at hf2
          simp only [hf2, if_false,
            evalWithAnswerFn_bind] at he
          cases hs2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
            f2 (route index 2).2 (route index 2).1
            (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) with
          | none =>
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some found2 =>
              obtain ⟨c2, d2, l2⟩ := found2
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_bind] at he
              let r3 := routeResidual index r2 2 l2 d2
              let f3 := Policy75Safe23.threshold 3 r3
              by_cases hf3 : f3 ≥ 24
              · dsimp only [r1, f1, r2, f2, r3, f3] at hf3
                simp only [hf3, if_true,
                  evalWithAnswerFn_pure, reduceCtorEq] at he
              dsimp only [r1, f1, r2, f2, r3, f3] at hf3
              simp only [hf3, if_false,
                evalWithAnswerFn_bind] at he
              cases hs3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
                f3 (route index 3).2 (route index 3).1
                (.pair (forest).1 (forest).2) 0 (searchLimit 3)) with
              | none =>
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_pure, reduceCtorEq] at he
              | some found3 =>
                  obtain ⟨c3, d3, l3⟩ := found3
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_bind] at he
                  simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                  subst result
                  constructor
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                  · exact hs0
                  · exact hs1
                  · exact hs2
                  · exact hs3
                  · exact Nat.lt_of_not_ge hf1
                  · exact Nat.lt_of_not_ge hf2
                  · exact Nat.lt_of_not_ge hf3
                  · rfl
                  · rfl
                  · rfl

theorem PreparedSearchFacts.validDigits {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) (lay : Layer) :
    Cost.ValidDigits lay (result.digits.getD lay.val []) := by
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl
  · exact (canonical_search_valid_credit answers 0 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (0 : Layer); unfold counterLimit at hb; omega) h.search0).1
  · exact (canonical_search_valid_credit answers 1 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (1 : Layer); unfold counterLimit at hb; omega) h.search1).1
  · exact (canonical_search_valid_credit answers 2 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (2 : Layer); unfold counterLimit at hb; omega) h.search2).1
  · exact (canonical_search_valid_credit answers 3 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (3 : Layer); unfold counterLimit at hb; omega) h.search3).1

theorem PreparedSearchFacts.hints_spec {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    result.policyHints.toNat < 12288 ∧
      hintFloor index result.policyHints 1 = Policy75Safe23.threshold 1 (preparedResidual1 index result) ∧
      hintFloor index result.policyHints 2 = Policy75Safe23.threshold 2 (preparedResidual2 index result) ∧
      hintFloor index result.policyHints 3 = Policy75Safe23.threshold 3 (preparedResidual3 index result) := by
  rw [h.hints_eq]
  exact encodedHints_spec _ _ _ h.floor1_lt h.floor2_lt h.floor3_lt

theorem PreparedSearchFacts.hints_valid {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    OuterSigning.policyHintsValid index result.policyHints result.digits result.lows = true := by
  simp only [OuterSigning.policyHintsValid, decide_eq_true_eq]
  exact ⟨h.hints_spec.1, h.digits_length, h.hints_spec.2⟩

theorem PreparedSearchFacts.honest_pieces {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (lay : Layer) :
    result.pieces.getD lay.val ([], []) =
      wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val []) := by
  have hv := h.validDigits lay
  rw [h.pieces_eq, prepareRoots_result]
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
    simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hv ⊢
  · simp only [Fin.val_zero, List.getD_cons_zero]
    rw [eval_signTop_honest answers cache _ _ hcache (route_leaf_bound index 0) hv,
      SigGolfCandidate.Research.SharedForest.route_top_tree index hindex, wotsPieces_top]
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 1) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 2) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 3) (by decide) _ hv

theorem PreparedSearchFacts.recover_honest {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (hhints : sig.policyHints = result.policyHints)
    (hpieces : ∀ lay, sig.layers lay = piecesSignature lay (result.pieces.getD lay.val ([], []))) :
    ∃ folded nonces lowerNonces, evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ)
      4 (.pair forest.1 forest.2)) = some ⟨folded,
        treeValue (builtTree answers 0 0) 12 0, result.counters, result.digits, result.lows, nonces, lowerNonces⟩ := by
  have hpiece : ∀ lay, sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) := by
    intro lay
    rw [hpieces lay, h.honest_pieces hcache hindex lay]
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  simp only [prepareRoots_result, fixedPrepared_pair] at hs0 hs1 hs2
  have hs : ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor index sig.policyHints lay) (route index lay).2 (route index lay).1
      (if lay = 3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val + 1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val [],
        result.lows.getD lay.val true) := by
    intro lay
    rw [hhints]
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3,
        show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
        show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
        show (Fin.ofNat 4 3 : Layer) = 3 from rfl, Nat.reduceAdd, show (0 : Layer) ≠ 3 by decide,
        show (1 : Layer) ≠ 3 by decide, show (2 : Layer) ≠ 3 by decide, if_false, if_true]
    · simpa only [hintFloor,if_pos rfl,old_root_floor,OuterSigning.root_floor,↓reduceIte] using hs0
    · simpa only [h.hints_spec.2.1] using hs1
    · simpa only [h.hints_spec.2.2.1] using hs2
    · simpa only [h.hints_spec.2.2.2] using hs3
  have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2 := by
    intro lay hl
    exact recoverLayerPair_wotsPieces answers sig index lay hl _ (h.validDigits lay) (hpiece lay)
  have hr := recoverHintedLayers_replay answers sig index ((sig.layers 0).path topJ) forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hr
  have ht := topNode_wotsPieces answers sig index hindex _ (h.validDigits 0) (hpiece 0)
  simp only [layer_val_0] at ht
  rw [ht,
    list_four_getD result.counters 0 h.counters_length,
    list_four_getD result.digits [] h.digits_length,
    list_four_getD result.lows true h.lows_length] at hr
  exact ⟨_, _, _, hr⟩


#print axioms searchPreparedLayers_some
#print axioms PreparedSearchFacts.recover_honest
end OuterPreparedFacts
