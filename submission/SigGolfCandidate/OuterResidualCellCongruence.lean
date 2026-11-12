import SigGolfCandidate.OuterResidualPadCongruence
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualCellCongruence
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues OuterResidualPadModel
open OuterResidualGroundChildren (childSlots)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (wTrialDeps mem_wTrialDeps wctItem)
open ClaudeWCT.W9.T3.Security.LargeResidual (ftsLeafSlot)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (ftsChild padCoord childWTrialDeps)
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (cellValues ftsChildVal_congr)
open OuterResidualValueLaws (wActiveV_congr)
attribute [local instance] Classical.propDecidable
theorem cellValues_congr (N : Node) (v v' : Coord → Digest)
    (hdep : ∀ c ∈ cellDepsP N, v c = v' c) : cellValues N v = cellValues N v' := by
  have h : ∀ cs ∈ childSlots N, v cs.1 = v' cs.1 := by
    intro cs hcs
    apply hdep
    cases N with
    | node n => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.mem_cellDeps_of_slot (N := .node n) hcs
    | wctNode n => exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.mpr ⟨cs, hcs, rfl⟩))))
    | wctLeaf L => exact List.mem_append_left _ (List.mem_map.mpr ⟨cs,hcs,rfl⟩)
    | _ => exact List.mem_map.mpr ⟨cs, hcs, rfl⟩
  cases N with
  | chain p => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.cellValues_congr (.chain p) v v' hdep

  | leaf L => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.cellValues_congr (.leaf L) v v' hdep

  | node n => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.cellValues_congr (.node n) v v' hdep

  | wctChain p => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.cellValues_congr (.wctChain p) v v' hdep

  | wctLeaf L =>
      have hfg : (fun t : Fin 6 => v (wctItem (L.index, L.coord, L.child, t) 4)) =
          fun t : Fin 6 => v' (wctItem (L.index, L.coord, L.child, t) 4) := by
        funext t
        exact h (wctItem (L.index, L.coord, L.child, t) 4, ftsLeafSlot t.val) (by
          simp only [childSlots]
          exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨t, rfl⟩))
      have hp := OuterResidualPadCongruence.padValue_congr v v' L.index L.coord (L.child.val%2) 0
        (fun c hc=>h (c,2) (by simp [childSlots,hc]))
        (fun c hc=>hdep c (List.mem_append_right _ (List.mem_append_left _ hc)))
      simp only [cellValues,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellValues.match_1,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots._sparseCasesOn_1, padVals]
      rw [hfg, hp]
  | wctNode n =>
      have hdw : ∀ c ∈ wTrialDeps n, v c = v' c := fun c hc =>
        hdep c (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hc))))
      have hdl : ∀ c ∈ childWTrialDeps n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val), v c = v' c :=
        fun c hc => hdep c (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hc)))
      have hdr : ∀ c ∈ childWTrialDeps n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1), v c = v' c :=
        fun c hc => hdep c (List.mem_append_left _ (List.mem_append_right _ hc))
      have ha : WActiveV v n ↔ WActiveV v' n := wActiveV_congr (fun h1 j hj => hdw _ (mem_wTrialDeps h1 hj))
      simp only [cellValues,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellValues.match_1,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots._sparseCasesOn_1]
      by_cases hav : WActiveV v n
      swap
      · rw [if_neg hav, if_neg (fun h' => hav (ha.mpr h'))]
      have hlt : ¬ Paired.wTrialCap n.1.coord.val n.1.level.val ≤ n.1.nonce.val := by have := hav.1; omega
      have h1 : ftsChildVal v n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val) =
          ftsChildVal v' n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val) := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val) with
        | none => unfold ftsChildVal; rw [hc]; rfl
        | some c => exact ftsChildVal_congr hc (h (c, 0) (by simp [childSlots, hc, hlt])) hdl
      have h2 : ftsChildVal v n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1) =
          ftsChildVal v' n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1) := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1) with
        | none => unfold ftsChildVal; rw [hc]; rfl
        | some c => exact ftsChildVal_congr hc (h (c, 3) (by simp [childSlots, hc, hlt])) hdr
      have h3 : (if n.1.level.val = 4 then (padVals v n.1.index n.1.coord (n.1.idx.val/2)).2
            else if OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val then
              BitVec.ofNat 128 (n.1.nonce.val % 2 ^ 64) else 0) =
          (if n.1.level.val = 4 then (padVals v' n.1.index n.1.coord (n.1.idx.val/2)).2
            else if OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val then
              BitVec.ofNat 128 (n.1.nonce.val % 2 ^ 64) else 0) := by
        split_ifs with hl
        · exact OuterResidualPadCongruence.padValue_congr v v' n.1.index n.1.coord (n.1.idx.val/2) 1
            (fun c hc=>h (c,2) (by simp only [childSlots,if_neg hlt,if_pos hl,hc]; exact List.mem_append_right _ (by simp)))
            (fun c hc=>hdep c (List.mem_append_right _ (List.mem_append_right _ hc)))
        · rfl
        · rfl
      rw [if_pos hav, if_pos (ha.mp hav), h1, h2, h3]
  | forest index => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.cellValues_congr (.forest index) v v' hdep

#print axioms cellValues_congr
end OuterResidualCellCongruence
