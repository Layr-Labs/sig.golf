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
theorem fts_structural (answers : Answers) (N : HashOutput) (w : WBytes) (hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)) =
      some (Extract.honestForest answers (N.toNat % 2 ^ 31))) :
    StructuralHitSrc answers (entriesOf answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)))) ∨
      FtsExtract.FtsShaped answers N w := by
  have h := FtsExtract.recoverFtsP_built_extract answers (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31)
    (selections N) _ (chosenOk_of N hS.1) hrun (honestForest_eq_built answers _)
  have hidx31 : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans hidx31 (by norm_num)
  rcases h with ⟨hq, hl⟩ | ⟨actual, hmem, ⟨hh, hsh⟩ | ⟨c, hc, l, n, hl, hn, hh, hsh⟩⟩
  · right
    refine ⟨fun q hq' => ?_, fun c hc j hj => ?_⟩
    · rcases hq q hq' with hf | ⟨c, hc, l, n, hl, hn, rfl⟩
      · exact Or.inl (by rw [hf, FtsExtract.honestInput_forest])
      · refine Or.inr ⟨c, hc, ?_⟩
        rcases FtsExtract.honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
        · exact Or.inl ⟨n, hn', by rw [he]⟩
        · exact Or.inr ⟨level, hlev, n, hn', by rw [he]⟩
    · obtain ⟨hs, hp0, hp1⟩ := hl c hc j hj
      have m21 : (c * 3 + j) % 21 = 3 * c + j := by rw [Nat.mod_eq_of_lt (by omega)]; ring
      have m22 : (3 * c + j) % 22 = 3 * c + j := Nat.mod_eq_of_lt (by omega)
      have m22' : (3 * c + j + 1) % 22 = 3 * c + j + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [witDecP, padDecP, m21, m22, m22'] at hs hp0 hp1
      exact ⟨hs, hp0, hp1⟩
  · left
    exact structuralHit_intro (.forest _) actual hidx hidx31 hmem (by rw [FtsExtract.honestInput_forest]; exact hh)
      (by rw [FtsExtract.honestInput_forest]; exact hsh) trivial
  · left
    rcases FtsExtract.honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
    · exact structuralHit_intro (.ftsLeaf _ c n) actual ⟨by omega, hidx, by omega⟩ ⟨hidx31, hc, hn'⟩ hmem
        (by rw [← he]; exact hh) (by rw [← he]; exact hsh) trivial
    · exact structuralHit_intro (.ftsNode _ c level n) actual
        ⟨by omega, hidx, hlev, by simpa only [Nat.sub_sub] using hn'⟩
        ⟨hidx31, hc, hlev, by simpa only [Nat.sub_sub] using hn'⟩ hmem (by rw [← he]; exact hh)
        (by rw [← he]; exact hsh) trivial
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
