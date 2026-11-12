import SigGolfCandidate.OuterCanonicalCount
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalForestCount
open SigGolfCandidate.T3.Security.Wots.Mask (queried_length_bind queried_length_pure)
open ClaudeWCT.W9.T3.Security.WPair.Counted (queried_length_ftsCoefs queried_length_free)
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Security.WPair ClaudeWCT.W9.T3.Security.WPair.Paired
variable {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs ⊆ U) (omega : ClaudeWCT.W9.CanonTable.Omega U)
theorem pair_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31)
    (pair : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank) (prev : PairRoot) :
    (SourceReplay.queried (wA hU omega hidden) (OuterForestMoment.pair index pair.val s aWord bWord prev)).length =
      (SourceReplay.queried (wA hU omega hidden') (OuterForestMoment.pair index pair.val s aWord bWord prev)).length := by
  have hp := pair.isLt
  unfold OuterForestMoment.pair
  simp only [←OuterCanonicalModel.coordinate_eq]
  refine queried_length_bind_rel (fun x y => x.1 = y.1) _ _
    (OuterCanonicalCount.coordinate_world hU omega hidden hidden' true index hindex (2 * pair.val) (by omega) _ _ _)
    ?_ (fun a a' ha => ?_)
  · beta_reduce
    rw [OuterCanonicalModel.coordinate_result, OuterCanonicalModel.coordinate_result]
    dsimp only
    exact OuterCanonicalWorld.nodes_world hU omega hidden hidden' true index hindex ⟨2 * pair.val, by omega⟩ (fun _ => prev)
  · beta_reduce at ha ⊢
    rw [queried_length_bind, queried_length_bind, queried_length_pure, queried_length_pure, ha]
    exact congrArg (· + 0) (OuterCanonicalCount.coordinate_world hU omega hidden hidden' false index hindex
      (2 * pair.val + 1) (by omega) _ _ _)

theorem forest_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31)
    (selected : ForestSelection) (words : ForestWords) :
    (SourceReplay.queried (wA hU omega hidden) (OuterForestMoment.forest index selected words)).length =
      (SourceReplay.queried (wA hU omega hidden') (OuterForestMoment.forest index selected words)).length := by
  have hfold := queried_length_foldlM_rel (A := wA hU omega hidden) (B := wA hU omega hidden')
    (fun (x y : List PairOpening × PairRoot) => x.2 = y.2)
    (fun (state : List PairOpening × PairRoot) pair => do
      let built ← OuterForestMoment.pair index pair.val (selected.pairs pair) (words.first pair) (words.second pair) state.2
      pure (state.1 ++ [built.1], built.2))
    (fun pair st st' hst => by
      beta_reduce at hst ⊢
      rw [queried_length_bind, queried_length_bind, queried_length_pure, queried_length_pure, hst]
      refine ⟨congrArg (· + 0) (pair_world hU omega hidden hidden' index hindex pair _ _ _ _), ?_⟩
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, OuterCanonicalModel.pair_result]
      exact OuterCanonicalWorld.root_world hU omega hidden hidden' index hindex pair _)
    (List.finRange 4) ([], ftsStart) ([], ftsStart) rfl
  unfold OuterForestMoment.forest
  refine queried_length_bind_rel (fun x y : List PairOpening × PairRoot => x.2 = y.2) _ _ hfold.1 hfold.2
    (fun st st' hst => ?_)
  beta_reduce at hst ⊢
  rw [queried_length_bind, queried_length_bind, queried_length_pure, queried_length_pure, hst]
  refine congrArg (· + 0) ?_
  unfold OuterForestMoment.singleton
  simp only [←OuterCanonicalModel.coordinate_eq]
  exact queried_length_bind_rel (fun _ _ => True) _ _
    (OuterCanonicalCount.coordinate_world hU omega hidden hidden' false index hindex 8 (by decide) _ _ _) trivial
    (fun _ _ _ => by rw [queried_length_pure, queried_length_pure])


#print axioms forest_world
end OuterCanonicalForestCount
