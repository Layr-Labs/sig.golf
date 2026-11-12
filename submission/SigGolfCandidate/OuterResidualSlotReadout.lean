import SigGolfCandidate.OuterResidualDependencyLaws
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualSlotReadout
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues OuterResidualPadModel
open OuterResidualGroundChildren (childSlots)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (ActiveV)
open ClaudeWCT.W9.T3.Security.LargeResidual (ftsLeafSlot)
open SigGolfCandidate.T3.Security.LargeResidual (slotValue)
open ClaudeWCT.W9.T3M
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (cellValues)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (ftsChild padCoord)
open SigGolfCandidate.T3.Security.LargeResidual (slotValue_block4)
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3M.SecurityInputs (nodeInputP pad64_block4)
attribute [local instance] Classical.propDecidable
theorem slot_cellValues (N : Node) (v : Coord → Digest)
    (hN : ∀ n, N = .node n → ActiveV v n ∧ ∀ cs ∈ childSlots N, v (selCoordV v cs.1) = v cs.1)
    (hW : ∀ n, N = .wctNode n → WActiveV v n) :
    ∀ cs ∈ childSlots N, (v (selCoordV v cs.1) = v cs.1) →
      slotValue (cellValues N v) cs.2 = v cs.1 := by
  intro cs hcs hsel
  cases N with
  | chain p => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.slot_cellValues (.chain p) v (fun _ h => by cases h) cs hcs

  | leaf L => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.slot_cellValues (.leaf L) v (fun _ h => by cases h) cs hcs

  | node n => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.slot_cellValues (.node n) v hN cs hcs

  | wctChain p => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.slot_cellValues (.wctChain p) v (fun _ h => by cases h) cs hcs

  | wctLeaf L =>
      simp only [childSlots, List.mem_append] at hcs
      rcases hcs with hcs | hcs
      · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hcs
        simp only [cellValues,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellValues.match_1,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots._sparseCasesOn_1, Extract.wctLeafInputP]
        rw [ClaudeWCT.W9.T3.Security.LargeResidual.slotValue_ftsLeafP _ _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellValues.match_1,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots._sparseCasesOn_1, Extract.wctLeafInputP]
        rw [ClaudeWCT.W9.T3.Security.LargeResidual.slotValue_ftsLeaf_pad]
        unfold padVals; rw [hc]; exact hsel
  | wctNode n =>
      have ha := hW n rfl
      have hlt : ¬ Paired.wTrialCap n.1.coord.val n.1.level.val ≤ n.1.nonce.val := by have := ha.1; omega
      simp only [childSlots, if_neg hlt, List.mem_append] at hcs
      rcases hcs with (hcs | hcs) | hcs
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellValues.match_1,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots._sparseCasesOn_1, if_pos ha, nodeInputP, pad64_block4]
        refine ((slotValue_block4 _ _ _ _).1).trans ?_
        unfold ftsChildVal; rw [hc]; exact hsel
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellValues.match_1,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots._sparseCasesOn_1, if_pos ha, nodeInputP, pad64_block4]
        refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        unfold ftsChildVal; rw [hc]; exact hsel
      · split_ifs at hcs with hl
        · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
          obtain ⟨c, hc, rfl⟩ := hcs
          simp only [cellValues,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellValues.match_1,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots._sparseCasesOn_1, if_pos ha, nodeInputP, pad64_block4, if_pos hl]
          refine ((slotValue_block4 _ _ _ _).2.1).trans ?_
          unfold padVals; rw [hc]; exact hsel
        · simp at hcs
  | forest index => exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.slot_cellValues (.forest index) v (fun _ h => by cases h) cs hcs

#print axioms slot_cellValues
end OuterResidualSlotReadout
