import SigGolfCandidate.T3.Secc.WotsExtractLayer

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem honestForest_eq_built (answers : Answers) (index : Nat) :
    Extract.honestForest answers index = evalWithAnswerFn answers
      (forestPk index ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)) := by
  have h1 : Extract.honestForest answers index =
      (answers (.inl (.inr (Extract.honestInput answers (.forest index))))).extractLsb' 0 128 := rfl
  have h2 : evalWithAnswerFn answers
      (forestPk index ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)) =
      (answers (.inl (.inr (pad64 (Extract.forestInput index
        ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)))))).extractLsb' 0 128 :=
    rfl
  rw [h1, h2, FtsExtract.honestInput_forest]
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
theorem WotsPrimitive.mono {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitive answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') : WotsPrimitive answers trace' := by
  rcases h with ⟨L, h⟩ | h | ⟨a, h⟩ | ⟨a, b, hab, h1, h2⟩ | ⟨a, hm, hc⟩
  · exact Or.inl ⟨L, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHit_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end SigGolfCandidate.T3.Security.Wots
