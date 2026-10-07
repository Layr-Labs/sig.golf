import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layers
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Wct
import SigGolfCandidate.ClaudeWCT.WCT9.Forest

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem keygen_pk (answers : Answers) : (evalWithAnswerFn answers WCT9.Rev3.keygen).1 = honestRoot answers 0 0 := by
  unfold WCT9.Rev3.keygen WCT9.keygen keygen keygenPayload
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [Correctness.eval_buildTree_levels answers 0 0 0 [] (Cost.validDigits_nil 0)]
  unfold honestRoot
  rw [WCT9.wotsTree_top]
  rfl
theorem layersWalkSpec_holds : WctExtract.LayersWalkSpec
    (fun answers w index qs => HitIn answers qs ∨
      ∃ lay : Layer, Diverge answers w index lay qs ∧ ∀ l : Layer, l.val < lay.val → Good answers w index l)
    (fun answers w index => ∀ l : Layer, Good answers w index l) := by
  intro answers w index root qs hidx hq h
  rcases layersBC_walk answers w index root hidx h with hhit | ⟨lay, hdiv, hgood⟩ | ⟨hgood, hroot⟩
  · exact Or.inl (Or.inl (hhit.mono hq))
  · exact Or.inl (Or.inr ⟨lay, hdiv.mono hq, hgood⟩)
  · exact Or.inr ⟨hgood, hroot⟩
theorem verifyP_walk_extract (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (WCT9.digestIndex N) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (WCT9.digestIndex N) l) ∨
       ((∀ l : Layer, Good answers w (WCT9.digestIndex N) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
            honestForest answers (WCT9.digestIndex N) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
            q ∈ queried answers (verifyP m pk w))) := by
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases layersWalkSpec_holds answers w (WCT9.digestIndex N) _ _ (WCT9.digestIndex_lt N) hqL (hpk ▸ hlay) with
    (hhit | hdiv) | ⟨hgood, hroot⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl hdiv)
  · exact Or.inr (Or.inr ⟨hgood, hroot, hqF⟩)
theorem verifyP_extract_normal (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (WCT9.digestIndex N) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (WCT9.digestIndex N) l) ∨
       ((∀ l : Layer, Good answers w (WCT9.digestIndex N) l) ∧ WctExtract.WctHonest answers N w)) := by
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WctExtract.verifyP_extract layersWalkSpec_holds answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hhit | hev | hgood
  · exact Or.inl hhit
  · rcases hev with hhit | hdiv
    · exact Or.inl hhit
    · exact Or.inr (Or.inl hdiv)
  · exact Or.inr (Or.inr hgood)
theorem wctEnds_eq (answers : Answers) (index coord child : Nat) :
    wctEnds answers index coord child = List.ofFn (WCT9.chainEnd answers index coord child) := rfl
theorem ftsNodes_eq (answers : Answers) (index : Nat) (c : WCT9.Coord) :
    ftsNodes answers index c.val = WCT9.coordNodes answers index c := rfl
theorem ftsPair_eq (answers : Answers) (index : Nat) (c : WCT9.Coord) :
    ftsPair answers index c.val = WCT9.coordinatePair answers index c := by
  unfold ftsPair ftsLevels WCT9.coordinatePair
  rw [WCT9.heapLevels_value _ 6 0 (by decide) (by decide), WCT9.heapLevels_value _ 6 1 (by decide) (by decide),
    ftsNodes_eq]
  rfl
theorem ftsPairsHonest_eq (answers : Answers) (index : Nat) :
    ftsPairsHonest answers index = List.ofFn (WCT9.coordinatePair answers index) := by
  apply List.ext_getElem (by simp [ftsPairsHonest])
  intro i hi _
  simp only [ftsPairsHonest, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact ftsPair_eq answers index ⟨i, by simpa [ftsPairsHonest] using hi⟩
theorem honestForest_eq (answers : Answers) (index : Nat) :
    honestForest answers index = WCT9.honestForest answers index := by
  unfold honestForest WCT9.honestForest
  rw [ftsPairsHonest_eq]
theorem honestPair_eq (answers : Answers) (lay : Layer) (tree : Nat) :
    honestPair answers lay tree = WCT9.builtPair answers lay tree := rfl
theorem honestRoot_top (answers : Answers) :
    honestRoot answers 0 0 = treeValue (builtTree answers 0 0) 12 0 := by
  unfold honestRoot
  rw [WCT9.wotsTree_top]
  rfl
end ClaudeWCT.W9.T3M.Extract
