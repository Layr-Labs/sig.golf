import SigGolfCandidate.OuterCanonTreeSelection
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ChainGraph (Address Point Seeds)
attribute [local instance] Classical.propDecidable
section Honest
variable {answers : Answers} {labels : Labels}
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    Wots.honestChainValueW answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      valueW (seedsOf (secretsOf answers)) (chainLabels labels) a step := by
  have hx := sourceW_chain answers (seedsOf (secretsOf answers)) (chainLabels labels) (agrees_chain h) a 0
    step (by omega)
  rw [valueW_zero, seedsOf_secretsOf, Nat.zero_add] at hx
  exact hx
theorem maxDigit_le_seven (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split_ifs <;> decide
/-- C3: the honest chain of the current scheme after `m + 1` steps is the used half (`Pos.proj`: the high half for
the last step of a lower chain 0) of step `m`'s label. -/
theorem chainValueW_succ (h : Agrees answers labels) (a : Address) (m : Fin 7) :
    Wots.honestChainValueW answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) (m.val + 1) =
      (Node.chain (a, m)).toPos.proj (labels (.chain (a, m))) := by
  have hm := m.isLt
  rw [← Wots.honestChainValueW_succ, chainValue_eq h a m.val (by omega)]
  have hrow : pad64 (WCT9.chainInputW a.layer a.tree.val a.leaf.val a.chain.val m.val
      (valueW (seedsOf (secretsOf answers)) (chainLabels labels) a m.val)) =
      cell (secretsOf answers) (.chain (a, m)) labels := by
    simp only [cell, OuterCanonBase.cell]
    rw [inputW, priorW_eq_valueW]
    exact WCT9.chainInputW_padded _ _ _ _ _ _
  have hp : (Node.chain (a, m)).toPos.proj = WCT9.halfOf (WCT9.chainHigh a.layer a.chain.val m.val) := rfl
  rw [hp, hrow, h (.chain (a, m))]
/-- C3: a revealed chain value is the seed (digit 0) or the used half of the label of the step before it. -/
theorem leafValue_eq (h : Agrees answers labels) (L : LeafPos) (digits : List Nat) (i : Nat) (hi : i < 58)
    (hdigit : digits.getD i 0 ≤ 7) :
    WCT9.wotsValue answers L.lay L.tree.val L.leaf.val digits i =
      if digits.getD i 0 = 0 then seedsOf (secretsOf answers) ⟨L.lay, L.tree, L.leaf, fin58 i⟩
      else (Node.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(digits.getD i 0 - 1) % 7, Nat.mod_lt _ (by decide)⟩)).toPos.proj
        (labels (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(digits.getD i 0 - 1) % 7, Nat.mod_lt _ (by decide)⟩))) := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have he : WCT9.wotsValue answers L.lay L.tree.val L.leaf.val digits i =
      Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
        (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val) (digits.getD i 0) := by
    unfold WCT9.wotsValue Wots.honestChainValueW; rw [hval]
  rw [he]
  split_ifs with h0
  · rw [h0, Wots.honestChainValueW_zero, seedsOf_secretsOf]
  · obtain ⟨m, hm⟩ : ∃ m, digits.getD i 0 = m + 1 := ⟨digits.getD i 0 - 1, by omega⟩
    have hmod : (digits.getD i 0 - 1) % 7 = m := by rw [hm]; exact Nat.mod_eq_of_lt (by omega)
    have hx := chainValueW_succ h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ ⟨m, by omega⟩
    simp only [hmod]
    exact (congrArg (Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
      (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val)) hm).trans hx
/-- C3: a chain end is the used half (`Pos.proj`, the high half for lower chain 0) of its last step's label. -/
theorem leafEnd_eq (h : Agrees answers labels) (L : LeafPos) (i : Nat) (hi : i < 58) :
    WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val i = endLabel (secretsOf answers) labels L i := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hm1 : 1 ≤ maxDigit L.lay i := by unfold maxDigit; split_ifs <;> decide
  have hm7 := maxDigit_le_seven L.lay i
  obtain ⟨m, hm⟩ : ∃ m, maxDigit L.lay i = m + 1 := ⟨maxDigit L.lay i - 1, by omega⟩
  have hmod : (maxDigit L.lay i - 1) % 7 = m := by rw [hm]; exact Nat.mod_eq_of_lt (by omega)
  have he : WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val i =
      Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
        (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val) (maxDigit L.lay i) := by
    unfold WCT9.wotsEnd Wots.honestChainValueW; rw [hval]
  have hx := chainValueW_succ h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ ⟨m, by omega⟩
  rw [he, hm, hx]
  unfold endLabel endPt
  simp only [hmod]
theorem leafEnds_eq (h : Agrees answers labels) (L : LeafPos) :
    (List.range (chainCount L.lay)).map (WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val) =
      (List.range (chainCount L.lay)).map (endLabel (secretsOf answers) labels L) := by
  apply List.map_congr_left
  intro i hi
  exact leafEnd_eq h L i (lt_of_lt_of_le (List.mem_range.mp hi) (chainCount_bound L.lay))
/-- C2: a leaf value is the used half (`Pos.proj`) of its leaf label. -/
theorem leafRoot_eq (h : Agrees answers labels) (L : SrcLeaf) :
    WCT9.wotsRoot answers L.1.lay L.1.tree.val L.1.leaf.val = (Node.leaf L).toPos.proj (labels (.leaf L)) := by
  unfold WCT9.wotsRoot
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  rw [Wots.eval_halfHash', leafEnds_eq h L.1]
  exact congrArg (WCT9.halfOf (WCT9.lowerHigh L.1.lay.val L.1.leaf.val)) (h (.leaf L))
theorem treeNodeAt_some (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hlevel : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) (ht : tree.val < 2 ^ treeBits lay)
    (hroot : lay = 0 ∨ level + 1 < height lay) :
    ∃ n : TreeNode, treeNodeAt lay tree level c = some n ∧ n.1.lay = lay ∧ n.1.tree = tree ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold treeNodeAt
  rw [dif_pos ⟨hlevel, hc, ht, hroot⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem builtTree_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (hlevel : level ≤ height lay) (hc : c < 2 ^ (height lay - level)) (ht : tree.val < 2 ^ treeBits lay)
    (hroot : lay = 0 ∨ level < height lay) :
    treeValue (WCT9.wotsTree answers lay tree.val) level c = treeLabel labels lay tree level c := by
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 2 ^ height lay := by simpa using hc
      have h4096 : c < 4096 := lt_of_lt_of_le hc' (by
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide)
              (SigGolfCandidate.T3M.Extract.height_le lay)
          _ = 4096 := by norm_num)
      rw [WCT9.wotsTree_leaf answers lay tree.val c hc']
      have hr := leafRoot_eq h ⟨⟨lay, tree, ⟨c, h4096⟩⟩, ⟨ht, hc'⟩⟩
      unfold treeLabel leafAt
      rw [if_pos rfl, dif_pos ⟨hc', ht⟩]
      exact hr
  | succ level ih =>
      intro c hc
      have hlt : level < height lay := by omega
      have hsub : height lay - (level + 1) = height lay - level - 1 := by omega
      have hc1 : c < 2 ^ (height lay - level - 1) := by rw [← hsub]; exact hc
      have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      obtain ⟨n, hn, -, -, -, -⟩ := treeNodeAt_some lay tree level c hlt hc1 ht (by omega)
      have hs := (tree_step (fun m => h (.node m)) lay tree level c n hn
        (ih (by omega) (by omega) (2 * c) (by omega)) (ih (by omega) (by omega) (2 * c + 1) (by omega))).2
      refine hs.trans ?_
      unfold treeLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
theorem honestRoot_eq (h : Agrees answers labels) :
    Extract.honestRoot answers 0 0 = treeLabel labels 0 0 (height 0) 0 :=
  builtTree_eq h 0 0 (height 0) 0 le_rfl (by simp) (by decide) (Or.inl rfl)
theorem honestRoot_label (h : Agrees answers labels) :
    Extract.honestRoot answers 0 0 = (labels (.node rootNode)).extractLsb' 0 128 := by
  rw [honestRoot_eq h, treeLabel_root]
theorem honestPair_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31))
    (ht : tree.val < 2 ^ treeBits lay) :
    Extract.honestPair answers lay tree.val =
      (treeLabel labels lay tree (height lay - 1) 0, treeLabel labels lay tree (height lay - 1) 1) := by
  have hpos := height_pos lay
  have hpow : 2 ≤ 2 ^ (height lay - (height lay - 1)) := by
    rw [show height lay - (height lay - 1) = 1 by omega]; norm_num
  unfold Extract.honestPair
  rw [builtTree_eq h lay tree (height lay - 1) 0 (by omega) (by omega) ht (Or.inr (by omega)),
    builtTree_eq h lay tree (height lay - 1) 1 (by omega) (by omega) ht (Or.inr (by omega))]

end Honest
#print axioms builtTree_eq
end OuterCanonBase.Paired
