import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraph
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents

namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot leafValue)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
  SigGolfCandidate.T3.buildLevels Correctness.builtTree ClaudeWCT.WCT9.heapBuild
theorem wctSeed_eq (answers : Answers) (a : WctAddr) :
    Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = wctSeedOf answers a := by
  unfold wctSeedOf
  rw [secretsOf_wct]
  rfl
theorem wctSeed_secrets (answers : Answers) (a : WctAddr) :
    Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = wctSeedsOf (secretsOf answers) a :=
  wctSeed_eq answers a
section Honest
variable {answers : Answers} {labels : Labels}
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    honestChainValue answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a step := by
  have hx := ChainGraph.source_chain answers (seedsOf (secretsOf answers)) (chainLabels labels) (agrees_chain h) a 0
    step (by omega)
  rw [ChainGraph.value_zero, seedsOf_secretsOf, Nat.zero_add] at hx
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
  rw [← Wots.honestChainValueW_succ, Wots.honestChainValueW_eq (step := m.val) (Or.inr (Or.inr (by omega))),
    chainValue_eq h a m.val (by omega)]
  have hrow : pad64 (chainInput a.layer a.tree.val a.leaf.val a.chain.val m.val
      (ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a m.val)) =
      cell (secretsOf answers) (.chain (a, m)) labels := by
    have hr : ∀ v, chainInput a.layer a.tree.val a.leaf.val a.chain.val m.val v = ChainGraph.row (a, m) v :=
      fun _ => rfl
    simp only [cell]
    rw [ChainGraph.input, ChainGraph.prior_eq_value, hr, ChainGraph.row_pad64]
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
  have hcorrect := WCT9.wotsTree_correct answers lay tree.val
  obtain ⟨-, -, hnodes⟩ := hcorrect
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
      have hrec := hnodes level hlt c (by rw [hsub]; exact hc1)
      have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hchild : ∀ j, j < 2 * c + 2 → treeValue (WCT9.wotsTree answers lay tree.val) level j =
          treeLabel labels lay tree level j := by
        intro j hj
        exact ih (by omega) (by omega) j (by omega)
      obtain ⟨n, hn, hlay, htree, hlev, hidx⟩ := treeNodeAt_some lay tree level c hlt hc1 ht (by omega)
      change ((WCT9.wotsTree answers lay tree.val).getD (level + 1) []).getD c 0 = _
      rw [hrec]
      unfold WCT9.lowerNodeHash WCT9.lowerHash
      rw [Wots.eval_halfHash']
      unfold treeLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      simp only
      have hinput : cell (secretsOf answers) (.node n) labels =
          pad64 (WCT9.merkleNodeInput lay.val tree.val (2 ^ (height lay - (level + 1)) + c)
            (((WCT9.wotsTree answers lay tree.val).getD level []).getD (2 * c) 0)
            (((WCT9.wotsTree answers lay tree.val).getD level []).getD (2 * c + 1) 0)) := by
        have h1 := hchild (2 * c) (by omega)
        have h2 := hchild (2 * c + 1) (by omega)
        unfold treeValue at h1 h2
        rw [h1, h2]
        obtain ⟨⟨nlay, ntree, nlevel, nidx⟩, hv⟩ := n
        simp only at hlay htree hlev hidx
        subst hlay htree
        simp only [cell]
        rw [hlev, hidx, show height nlay - level - 1 = height nlay - (level + 1) by omega]
      have hhigh : (Node.node n).toPos.high = WCT9.lowerHigh lay.val (2 ^ (height lay - (level + 1)) + c) := by
        obtain ⟨⟨nlay, ntree, nlevel, nidx⟩, hv⟩ := n
        simp only at hlay htree hlev hidx
        subst hlay
        simp only [Node.toPos, Extract.Pos.high]
        rw [hlev, hidx, show height nlay - level - 1 = height nlay - (level + 1) by omega]
      rw [← hinput, ← hhigh]
      exact congrArg (fun output : HashOutput => (Node.node n).toPos.proj output) (h (.node n))
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
theorem wctValue_eq (h : Agrees answers labels) (a : WctAddr) (s : Nat) (hs : s ≤ 4) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s = wctValueL (secretsOf answers) labels a s := by
  induction s with
  | zero =>
      unfold Extract.wctValue
      rw [WCT9.eval_chain_walk]
      change Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = _
      rw [wctSeed_secrets]
      rfl
  | succ s ih =>
      have ih' := ih (by omega)
      unfold Extract.wctValue at ih' ⊢
      rw [WCT9.eval_chain_walk] at ih' ⊢
      change WCT9.shortAnswer answers (WCT9.chainInput a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val (0 + s)
        (WCT9.walk _ 0 s _)) = _
      rw [ih', Nat.zero_add]
      have hcell := h (.wctChain (a, ⟨s, by omega⟩))
      simp only [cell] at hcell
      unfold WCT9.shortAnswer
      rw [hcell]
      have hnode : (Node.wctChain (a, ⟨(s + 1 - 1) % 4, Nat.mod_lt _ (by decide)⟩) : Node) =
          .wctChain (a, ⟨s, by omega⟩) := by
        congr
        simp only [Nat.add_sub_cancel]
        exact Nat.mod_eq_of_lt (by omega)
      unfold wctValueL
      rw [if_neg (by omega), hnode]
theorem wctEnd_eq (h : Agrees answers labels) (a : WctAddr) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val 4 = wctEndLabel labels a := by
  rw [wctValue_eq h a 4 le_rfl, wctValueL_three]
theorem wctEnds_eq (h : Agrees answers labels) (L : WctLeafPos) :
    Extract.wctEnds answers L.index.val L.coord.val L.child.val =
      List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t) := by
  unfold Extract.wctEnds
  congr 1
  funext t
  exact wctEnd_eq h (L.index, L.coord, L.child, t)
theorem childRoot_eq (h : Agrees answers labels) (L : WctLeafPos)
    (hprev : Extract.ftsPrev answers L.index.val L.coord.val = ftsPrevLabel labels L.index L.coord) :
    WCT9.childRoot answers L.index.val L.coord.val L.child.val (Extract.ftsPrev answers L.index.val L.coord.val).1 =
      (labels (.wctLeaf L)).extractLsb' 0 128 := by
  have hends : (List.ofFn fun i : Fin 6 => WCT9.chainEnd answers L.index.val L.coord.val L.child.val i) =
      Extract.wctEnds answers L.index.val L.coord.val L.child.val := rfl
  have hleaf : ∀ pad ends, WCT9.leafHashP L.index.val L.coord.val L.child.val pad ends =
      shortHash (Extract.wctLeafInputP L.index.val L.coord.val L.child.val pad ends) := by
    intro pad ends
    unfold WCT9.leafHashP WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
    simp only [List.flatMap_cons, List.append_assoc]
  unfold WCT9.childRoot
  rw [hleaf, hends, wctEnds_eq h L, hprev]
  change (answers (.inl (.inr (pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
    (ftsPrevLabel labels L.index L.coord).1
    (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t))))))).extractLsb' 0 128 = _
  exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.wctLeaf L))
theorem ftsNodeAt_some (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hlevel : level < 6)
    (hc : c < 2 ^ (7 - level - 1)) :
    ∃ n : WctNodePos, ftsNodeAt index coord level c = some n ∧ n.1.index = index ∧ n.1.coord = coord ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold ftsNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem eval_wctTopHash (coord index heap : Nat) (l p r : Digest) :
    evalWithAnswerFn answers (WCT9.wctTopHash coord index heap l p r) =
      (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord) index heap l p r))))).extractLsb' 128 128 :=
  rfl
theorem ftsTree_eqP (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 9)
    (hprev : Extract.ftsPrev answers index.val coord.val = ftsPrevLabel labels index coord) (level c : Nat)
    (hlevel : level ≤ 6) (hc : c < 2 ^ (7 - level)) :
    treeValue (Extract.ftsLevels answers index.val coord.val) level c = ftsLabel labels index coord level c := by
  have hinv := WCT9.heap_complete answers index.val coord.val (Extract.ftsPrev answers index.val coord.val).2
    (Extract.ftsLeaves answers index.val coord.val) (by simp [Extract.ftsLeaves])
  have hleaves : ∀ j (hj : j < 128), (Extract.ftsLeaves answers index.val coord.val).getD j 0 =
      (labels (.wctLeaf ⟨index, coord, ⟨j, hj⟩⟩)).extractLsb' 0 128 := by
    intro j hj
    unfold Extract.ftsLeaves
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hj), List.getElem_ofFn]
    exact childRoot_eq h ⟨index, coord, ⟨j, hj⟩⟩ hprev
  unfold Extract.ftsLevels Extract.ftsNodes
  generalize evalWithAnswerFn answers (WCT9.heapBuild index.val coord.val
    (Extract.ftsPrev answers index.val coord.val).2 (Extract.ftsLeaves answers index.val coord.val)) = X at hinv ⊢
  obtain ⟨-, hleaf, hnode⟩ := hinv
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 128 := by simpa using hc
      rw [WCT9.heapLevels_value X 0 c (by decide) (by simpa using hc)]
      rw [show 2 ^ (7 - 0) + c = 128 + c by norm_num, hleaf (128 + c) (by omega) (by omega),
        Nat.add_sub_cancel_left, hleaves c hc']
      unfold ftsLabel
      rw [if_pos rfl, dif_pos hc']
  | succ level ih =>
      intro c hc
      have hlt : level < 6 := by omega
      have hsub : 7 - (level + 1) = 7 - level - 1 := by omega
      have hc1 : c < 2 ^ (7 - level - 1) := by rw [← hsub]; exact hc
      have hpow : 2 ^ (7 - level) = 2 * 2 ^ (7 - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpos : 2 ≤ 2 ^ (7 - level - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (7 - level - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hle : 2 ^ (7 - level - 1) ≤ 64 :=
        (Nat.pow_le_pow_right (by decide) (by omega : 7 - level - 1 ≤ 6)).trans (by decide)
      have hchild : ∀ j, j < 2 * c + 2 → treeValue (WCT9.heapLevels X) level j = ftsLabel labels index coord level j := by
        intro j hj
        exact ih (by omega) j (by omega)
      obtain ⟨n, hn, hindex, hcoord, hlev, hidx⟩ := ftsNodeAt_some index coord level c hlt hc1
      have hrhs : ftsLabel labels index coord (level + 1) c = if level + 1 = 6 then
          (labels (.wctNode n)).extractLsb' 128 128 else (labels (.wctNode n)).extractLsb' 0 128 := by
        unfold ftsLabel
        rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      have hinput : cell (secretsOf answers) (.wctNode n) labels =
          pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2 ^ (7 - level - 1) + c)
            (ftsLabel labels index coord level (2 * c))
            (if level = 5 then (ftsPrevLabel labels index coord).2 else 0)
            (ftsLabel labels index coord level (2 * c + 1))) := by
        obtain ⟨⟨nindex, ncoord, nlevel, nidx⟩, hv⟩ := n
        simp only at hindex hcoord hlev hidx
        subst hindex hcoord
        simp only [cell]
        rw [hlev, hidx]
      rw [hrhs, WCT9.heapLevels_value X (level + 1) c (by omega) hc, hsub]
      have hl := WCT9.heapLevels_value X level (2 * c) (by omega) (by omega)
      have hr := WCT9.heapLevels_value X level (2 * c + 1) (by omega) (by omega)
      rw [hnode (2 ^ (7 - level - 1) + c) (by omega) (by omega) (by omega)]
      have e1 : 2 * (2 ^ (7 - level - 1) + c) = 2 ^ (7 - level) + 2 * c := by omega
      rw [e1, show 2 ^ (7 - level) + 2 * c + 1 = 2 ^ (7 - level) + (2 * c + 1) by omega, ← hl, ← hr,
        hchild (2 * c) (by omega), hchild (2 * c + 1) (by omega)]
      by_cases h5 : level = 5
      · subst h5
        rw [if_pos rfl, WCT9.wctHeapNode_top (by norm_num at hc1 ⊢; omega), eval_wctTopHash, hprev]
        rw [if_pos rfl] at hinput
        rw [← hinput]
        exact congrArg (fun output : HashOutput => output.extractLsb' 128 128) (h (.wctNode n))
      · rw [if_neg (by omega), WCT9.wctHeapNode_low (by
          have : 4 ≤ 2 ^ (7 - level - 1) := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (7 - level - 1) := Nat.pow_le_pow_right (by decide) (by omega)
          omega), WCT9.wctNodeHash, nodeHash_eq_shortHash, eval_shortHash]
        rw [if_neg h5] at hinput
        rw [← hinput]
        exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.wctNode n))
theorem ftsPrev_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    ∀ c (hc : c < 9), Extract.ftsPrev answers index.val c = ftsPrevLabel labels index ⟨c, hc⟩
  | 0, _ => by
    unfold ftsPrevLabel
    rw [dif_pos rfl]; rfl
  | c + 1, hc => by
    have ih := ftsPrev_eq h index c (by omega)
    have hpair : Extract.ftsPair answers index.val c = Extract.ftsPrev answers index.val (c + 1) := by
      unfold Extract.ftsPair Extract.ftsLevels
      rw [WCT9.heapLevels_value _ 6 0 (by decide) (by decide), WCT9.heapLevels_value _ 6 1 (by decide) (by decide)]
      rfl
    rw [← hpair]
    unfold Extract.ftsPair
    rw [ftsTree_eqP h index ⟨c, by omega⟩ ih 6 0 le_rfl (by decide),
      ftsTree_eqP h index ⟨c, by omega⟩ ih 6 1 le_rfl (by decide)]
    unfold ftsPrevLabel
    rw [dif_neg (by simp)]
    rfl
theorem ftsTree_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hlevel : level ≤ 6) (hc : c < 2 ^ (7 - level)) :
    treeValue (Extract.ftsLevels answers index.val coord.val) level c = ftsLabel labels index coord level c :=
  ftsTree_eqP h index coord (ftsPrev_eq h index coord.val coord.isLt) level c hlevel hc
theorem ftsPair_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 9) :
    Extract.ftsPair answers index.val coord.val = (ftsLabel labels index coord 6 0, ftsLabel labels index coord 6 1) := by
  unfold Extract.ftsPair
  rw [ftsTree_eq h index coord 6 0 le_rfl (by decide), ftsTree_eq h index coord 6 1 le_rfl (by decide)]
theorem ftsPairs_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    Extract.ftsPairsHonest answers index.val =
      (List.range 9).map fun coord => (ftsLabel labels index (fin9 coord) 6 0, ftsLabel labels index (fin9 coord) 6 1) := by
  unfold Extract.ftsPairsHonest
  apply List.map_congr_left
  intro coord hcoord
  have hc : coord < 9 := List.mem_range.mp hcoord
  have hval : (fin9 coord).val = coord := Nat.mod_eq_of_lt hc
  have hx := ftsPair_eq h index (fin9 coord)
  rw [hval] at hx
  exact hx
/-- The honest L3 message (nested FTS r1-1) in labels: the high halves of coordinate 8's two top nodes. -/
theorem honestTop_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    Extract.honestTop answers index.val = (ftsLabel labels index 8 6 0, ftsLabel labels index 8 6 1) :=
  ftsPair_eq h index 8
theorem honestInput_eq (h : Agrees answers labels) (node : Node) :
    Extract.honestInput answers node.toPos = cell (secretsOf answers) node labels := by
  cases node with
  | chain p =>
      simp only [Node.toPos, Extract.honestInput]
      rw [chainValue_eq h p.1 p.2.val (by have := p.2.isLt; omega)]
      change pad64 (ChainGraph.row p _) = ChainGraph.row p (ChainGraph.prior _ p _)
      rw [ChainGraph.row_pad64, ChainGraph.prior_eq_value]
  | leaf L =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [leafEnds_eq h L.1]
  | node n =>
      obtain ⟨⟨lay, tree, level, idx⟩, hv1, hv2, hv3, hv4⟩ := n
      change level.val < height lay at hv1
      change idx.val < 2 ^ (height lay - level.val - 1) at hv2
      change tree.val < 2 ^ treeBits lay at hv3
      change lay = 0 ∨ level.val + 1 < height lay at hv4
      simp only [Node.toPos, Extract.honestInput, cell]
      have hpow : 2 ^ (height lay - level.val) = 2 * 2 ^ (height lay - level.val - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [builtTree_eq h lay tree level.val (2 * idx.val) (by omega) (by omega) hv3 (by omega),
        builtTree_eq h lay tree level.val (2 * idx.val + 1) (by omega) (by omega) hv3 (by omega)]
  | wctChain p =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [wctValue_eq h p.1 p.2.val (by have := p.2.isLt; omega), Extract.pad64_wctChainInput]
  | wctLeaf L =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [wctEnds_eq h L, ftsPrev_eq h L.index L.coord.val L.coord.isLt]
  | wctNode n =>
      obtain ⟨⟨index, coord, level, idx⟩, hv⟩ := n
      have hv' : idx.val < 2 ^ (7 - level.val - 1) := hv
      simp only [Node.toPos, Extract.honestInput, cell]
      have hpow : 2 ^ (7 - level.val) = 2 * 2 ^ (7 - level.val - 1) := by
        have := level.isLt
        rw [← pow_succ']; congr 1; omega
      rw [ftsTree_eq h index coord level.val (2 * idx.val) (by have := level.isLt; omega) (by omega),
        ftsTree_eq h index coord level.val (2 * idx.val + 1) (by have := level.isLt; omega) (by omega),
        ftsPrev_eq h index coord.val coord.isLt]
  | forest index =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [ftsPairs_eq h index]
theorem honest_answer (h : Agrees answers labels) (node : Node) :
    answers (.inl (.inr (Extract.honestInput answers node.toPos))) = labels node := by
  rw [honestInput_eq h node]
  exact h node
end Honest
end ClaudeWCT.W9.T3.Security.CanonGraph

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
open ChainGraph (Address Point Seeds)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
  SigGolfCandidate.T3.buildLevels Correctness.builtTree ClaudeWCT.WCT9.heapBuild
def Agrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ node, answers (.inl (.inr (cell (secretsOf answers) node labels))) = labels node
theorem secretsOf_eager (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput) :
    secretsOf (eagerAnswers privateTable U publicTable) = privateSecrets privateTable := rfl
theorem eagerAnswers_mem (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput)
    (x : U) : eagerAnswers privateTable U publicTable (.inl (.inr x.val)) = publicTable x :=
  finiteHashAnswer_none ∅ U publicTable x.val x.property rfl
theorem agrees_of_programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (answers : Answers)
    (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x) :
    Agrees answers labels := by
  intro node
  have h := hpub (cellIn U hU (secretsOf answers) node labels)
  rw [programmed_at] at h
  exact h
theorem eager_programmed_agrees (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (other : OtherHalves) (labels : Labels) (residual : U → HashOutput) :
    Agrees (eagerAnswers (privateEquiv.symm (secrets, other)) U (programmed U hU secrets labels residual)) labels := by
  apply agrees_of_programmed U hU _ labels residual
  intro x
  rw [secretsOf_eager, privateSecrets_symm, eagerAnswers_mem]
theorem agrees_chain {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    ChainGraph.Agrees answers (seedsOf (secretsOf answers)) (chainLabels labels) :=
  fun point => h (.chain point)

section Honest
variable {answers : Answers} {labels : Labels}
-- Stage 2 (C2/C3, #866): the paired honest section follows the #866 legacy section above (`chainValueW_succ`,
-- `leafValue_eq`/`leafEnd_eq` through `Pos.proj` of the last chain step, `leafRoot_eq` through `Pos.proj` of the
-- leaf label, `builtTree_eq` with `lowerNodeHash`); `Paired.cell` is `CanonGraph.cell` on the lower nodes.
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    honestChainValue answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a step := by
  have hx := ChainGraph.source_chain answers (seedsOf (secretsOf answers)) (chainLabels labels) (agrees_chain h) a 0
    step (by omega)
  rw [ChainGraph.value_zero, seedsOf_secretsOf, Nat.zero_add] at hx
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
  rw [← Wots.honestChainValueW_succ, Wots.honestChainValueW_eq (step := m.val) (Or.inr (Or.inr (by omega))),
    chainValue_eq h a m.val (by omega)]
  have hrow : pad64 (chainInput a.layer a.tree.val a.leaf.val a.chain.val m.val
      (ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a m.val)) =
      cell (secretsOf answers) (.chain (a, m)) labels := by
    have hr : ∀ v, chainInput a.layer a.tree.val a.leaf.val a.chain.val m.val v = ChainGraph.row (a, m) v :=
      fun _ => rfl
    simp only [cell, CanonGraph.cell]
    rw [ChainGraph.input, ChainGraph.prior_eq_value, hr, ChainGraph.row_pad64]
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
  have hcorrect := WCT9.wotsTree_correct answers lay tree.val
  obtain ⟨-, -, hnodes⟩ := hcorrect
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
      have hrec := hnodes level hlt c (by rw [hsub]; exact hc1)
      have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hchild : ∀ j, j < 2 * c + 2 → treeValue (WCT9.wotsTree answers lay tree.val) level j =
          treeLabel labels lay tree level j := by
        intro j hj
        exact ih (by omega) (by omega) j (by omega)
      obtain ⟨n, hn, hlay, htree, hlev, hidx⟩ := treeNodeAt_some lay tree level c hlt hc1 ht (by omega)
      change ((WCT9.wotsTree answers lay tree.val).getD (level + 1) []).getD c 0 = _
      rw [hrec]
      unfold WCT9.lowerNodeHash WCT9.lowerHash
      rw [Wots.eval_halfHash']
      unfold treeLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      simp only
      have hinput : cell (secretsOf answers) (.node n) labels =
          pad64 (WCT9.merkleNodeInput lay.val tree.val (2 ^ (height lay - (level + 1)) + c)
            (((WCT9.wotsTree answers lay tree.val).getD level []).getD (2 * c) 0)
            (((WCT9.wotsTree answers lay tree.val).getD level []).getD (2 * c + 1) 0)) := by
        have h1 := hchild (2 * c) (by omega)
        have h2 := hchild (2 * c + 1) (by omega)
        unfold treeValue at h1 h2
        rw [h1, h2]
        obtain ⟨⟨nlay, ntree, nlevel, nidx⟩, hv⟩ := n
        simp only at hlay htree hlev hidx
        subst hlay htree
        simp only [cell, CanonGraph.cell]
        rw [hlev, hidx, show height nlay - level - 1 = height nlay - (level + 1) by omega]
      have hhigh : (Node.node n).toPos.high = WCT9.lowerHigh lay.val (2 ^ (height lay - (level + 1)) + c) := by
        obtain ⟨⟨nlay, ntree, nlevel, nidx⟩, hv⟩ := n
        simp only at hlay htree hlev hidx
        subst hlay
        simp only [Node.toPos, Extract.Pos.high]
        rw [hlev, hidx, show height nlay - level - 1 = height nlay - (level + 1) by omega]
      rw [← hinput, ← hhigh]
      exact congrArg (fun output : HashOutput => (Node.node n).toPos.proj output) (h (.node n))
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
theorem wctValue_eq (h : Agrees answers labels) (a : WctAddr) (s : Nat) (hs : s ≤ 4) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s = wctValueL (secretsOf answers) labels a s := by
  induction s with
  | zero =>
      unfold Extract.wctValue
      rw [WCT9.eval_chain_walk]
      change Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = _
      rw [wctSeed_secrets]
      rfl
  | succ s ih =>
      have ih' := ih (by omega)
      unfold Extract.wctValue at ih' ⊢
      rw [WCT9.eval_chain_walk] at ih' ⊢
      change WCT9.shortAnswer answers (WCT9.chainInput a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val (0 + s)
        (WCT9.walk _ 0 s _)) = _
      rw [ih', Nat.zero_add]
      have hcell := h (.wctChain (a, ⟨s, by omega⟩))
      simp only [cell,CanonGraph.cell] at hcell
      unfold WCT9.shortAnswer
      rw [hcell]
      have hnode : (Node.wctChain (a, ⟨(s + 1 - 1) % 4, Nat.mod_lt _ (by decide)⟩) : Node) =
          .wctChain (a, ⟨s, by omega⟩) := by
        congr
        simp only [Nat.add_sub_cancel]
        exact Nat.mod_eq_of_lt (by omega)
      unfold wctValueL
      rw [if_neg (by omega), hnode]
theorem wctEnd_eq (h : Agrees answers labels) (a : WctAddr) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val 4 = wctEndLabel labels a := by
  rw [wctValue_eq h a 4 le_rfl, wctValueL_three]
theorem wctEnds_eq (h : Agrees answers labels) (L : WctLeafPos) :
    Extract.wctEnds answers L.index.val L.coord.val L.child.val =
      List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t) := by
  unfold Extract.wctEnds
  congr 1
  funext t
  exact wctEnd_eq h (L.index, L.coord, L.child, t)

end Honest
#print axioms wctEnds_eq
#print axioms honestPair_eq
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem rawLeaf_lt (coord child : Nat) (hc : child<128) : rawLeaf coord child<128 := by
  unfold rawLeaf
  split_ifs <;> omega

theorem pads_raw_branch (labels : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (child : Nat) (hc : child<128) :
    pads labels index coord (child/64)=pads labels index coord (rawLeaf coord.val child%2) := by
  unfold pads
  split_ifs with hz ho
  · rfl
  · have hn:¬first coord.val := by unfold first;omega
    have he:rawLeaf coord.val child%2=child/64 := by unfold rawLeaf;rw [if_neg hn];omega
    rw [he]
  · rfl

#print axioms pads_raw_branch

def topLevel (coord : Fin 9) : Nat := if first coord.val then 5 else 6

/-- The source heap recurrence, expressed with the fixed projection of its address. -/
def NodesRec (answers : Answers) (labels : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (nodes : Array Digest) : Prop :=
  ∀ level, level<topLevel coord → ∀ c,c<2^(6-level) →
    nodes.getD (2^(6-level)+c) 0 =
      Extract.Paired.proj (.wctNode index.val coord.val level c)
        (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val
          (2^(6-level)+c) (nodes.getD (2*(2^(6-level)+c)) 0)
          (if level=4 then (pads labels index coord (c/2)).2 else 0)
          (nodes.getD (2*(2^(6-level)+c)+1) 0))))))

theorem nodes_label (answers : Answers) (labels : Labels) (ha : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (nodes : Array Digest)
    (hleaf : ∀c,c<128 → nodes.getD (128+c) 0=ftsLabel labels index coord 0 c)
    (hnode : NodesRec answers labels index coord nodes)
    (level c : Nat) (hl : level≤topLevel coord) (hc : c<2^(7-level)) :
    nodes.getD (2^(7-level)+c) 0=ftsLabel labels index coord level c := by
  have ht:topLevel coord≤6 := by unfold topLevel;split_ifs <;> omega
  induction level generalizing c with
  | zero=> exact hleaf c (by simpa using hc)
  | succ level ih=>
    have hl6:level<6 := by omega
    have hsub:7-(level+1)=6-level := by omega
    have hc':c<2^(6-level) := by simpa only [hsub] using hc
    have hpow:2^(7-level)=2*2^(6-level) := by rw [←pow_succ'];congr 1;omega
    have hleft : nodes.getD (2^(7-level)+2*c) 0=ftsLabel labels index coord level (2*c) := by
      apply ih <;> omega
    have hright : nodes.getD (2^(7-level)+(2*c+1)) 0=ftsLabel labels index coord level (2*c+1) := by
      apply ih <;> omega
    have hrec:=hnode level (by omega) c hc'
    have haddr:2*(2^(6-level)+c)=2^(7-level)+2*c := by rw [hpow];omega
    have haddr':2*(2^(6-level)+c)+1=2^(7-level)+(2*c+1) := by rw [hpow];omega
    rw [haddr,hleft] at hrec
    rw [show 2^(7-level)+2*c+1=2^(7-level)+(2*c+1) by omega,hright] at hrec
    obtain ⟨n,hn,hindex,hcoord,hlevel,hidx⟩:=CanonGraph.ftsNodeAt_some index coord level c hl6
      (by simpa only [show 7-level-1=6-level by omega] using hc')
    have hcell:cell (secretsOf answers) (.wctNode n) labels =
        pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level)+c)
          (ftsLabel labels index coord level (2*c))
          (if level=4 then (pads labels index coord (c/2)).2 else 0)
          (ftsLabel labels index coord level (2*c+1))) := by
      simp only [cell,hindex,hcoord,hlevel,hidx,show 7-level-1=6-level by omega]
    have he:=ha (.wctNode n)
    rw [hcell] at he
    rw [he] at hrec
    rw [hsub,hrec]
    unfold ftsLabel
    rw [if_neg (by omega : level+1≠0),show level+1-1=level by omega,hn]

#print axioms nodes_label
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem sharedNode_eval (answers : Answers) (index : Fin (2^31)) (coord : Fin 9)
    (ps : Nat → Digest×Digest) (left right : Digest) (level c : Nat)
    (hl : level<topLevel coord) (hc : c<2^(6-level)) :
    evalWithAnswerFn answers (Research.SharedForest.sharedNode (decide (first coord.val)) coord.val index.val
      (2^(6-level)+c) ps left right) =
      Extract.Paired.proj (.wctNode index.val coord.val level c)
        (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val
          (2^(6-level)+c) left (if level=4 then (ps (c/2)).2 else 0) right))))) := by
  have hl6:level<6 := by unfold topLevel at hl;split_ifs at hl <;> omega
  have hu : Extract.Paired.first coord.val = true → level < 5 := by
    intro hf
    have hf' : first coord.val := of_decide_eq_true hf
    simp only [topLevel, if_pos hf'] at hl
    exact hl
  have hd : decide (first coord.val) = Extract.Paired.first coord.val := rfl
  rw [hd, Extract.Paired.sharedNode_eq_nodeProgramP index.val coord.val level c coord.isLt hl6 hc hu ps left right,
    Extract.Paired.eval_nodeProgram]
  have hpad : (if level=4 then (ps ((2^(6-level)+c)/2-2)).2 else (0:Digest)) =
      (if level=4 then (ps (c/2)).2 else 0) := by
    by_cases h4 : level=4
    · subst level
      rw [if_pos rfl, if_pos rfl, show (2^(6-4)+c)/2-2=c/2 by norm_num; omega]
    · rw [if_neg h4, if_neg h4]
  rw [hpad]
  rfl
#print axioms sharedNode_eval
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

/-- C1: the honest leaf (heap `128 + physical`) is the fixed projection of its label. -/
theorem childRoot_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels) (L : WctLeafPos) :
    WCT9.childRootH answers (128 + Extract.Paired.physical L.coord.val L.child.val)
      L.index.val L.coord.val L.child.val (pads labels L.index L.coord (L.child.val%2)).1 =
      Extract.Paired.proj (.wctLeaf L.index.val L.coord.val L.child.val) (labels (.wctLeaf L)) := by
  have hends : (List.ofFn fun i : Fin 6 => WCT9.chainEnd answers L.index.val L.coord.val L.child.val i) =
      Extract.wctEnds answers L.index.val L.coord.val L.child.val := rfl
  have hleaf : ∀ pad ends, WCT9.leafHashH (128 + Extract.Paired.physical L.coord.val L.child.val)
      L.index.val L.coord.val L.child.val pad ends =
      WCT9.ftsHash (128 + Extract.Paired.physical L.coord.val L.child.val)
        (Extract.wctLeafInputP L.index.val L.coord.val L.child.val pad ends) := by
    intro pad ends
    unfold WCT9.leafHashH WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
    simp only [List.flatMap_cons, List.append_assoc]
  unfold WCT9.childRootH
  rw [hleaf,hends,wctEnds_eq h L,WCT9.eval_ftsHash,Extract.Paired.proj_wctLeaf]
  exact congrArg (WCT9.ftsHalf (128 + Extract.Paired.physical L.coord.val L.child.val)) (h (.wctLeaf L))

theorem physical_rawLeaf (coord : Fin 9) (c : Nat) (hc : c<128) :
    Extract.Paired.physical coord.val (rawLeaf coord.val c)=c := by
  unfold Extract.Paired.physical Research.SharedForest.physicalChild Extract.Paired.first rawLeaf
  by_cases hf : first coord.val
  · have hf' : decide (coord.val<8 ∧ coord.val%2=0)=true := decide_eq_true hf
    simp only [hf', if_pos hf, ↓reduceIte]
  · have hf' : decide (coord.val<8 ∧ coord.val%2=0)=false := decide_eq_false hf
    simp only [hf', if_neg hf, Bool.false_eq_true, ↓reduceIte]
    omega

theorem rawChild_eq (coord child : Nat) :
    Research.SharedForest.rawChild (decide (first coord)) child=rawLeaf coord child := by
  simp only [Research.SharedForest.rawChild,rawLeaf,decide_eq_true_eq]

theorem source_leaves_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b) (c : Nat) (hc : c<128) :
    (Research.SharedForest.sharedLeaves answers (decide (first coord.val)) index.val coord.val ps).getD c 0 =
      ftsLabel labels index coord 0 c := by
  unfold Research.SharedForest.sharedLeaves
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact hc),List.getElem_ofFn]
  rw [rawChild_eq,hps _ (by omega),pads_raw_branch labels index coord c hc]
  have he:=childRoot_eq answers labels h ⟨index,coord,⟨rawLeaf coord.val c,rawLeaf_lt _ _ hc⟩⟩
  simp only [physical_rawLeaf coord c hc] at he
  unfold ftsLabel
  rw [if_pos rfl,dif_pos (rawLeaf_lt _ _ hc)]
  exact he

theorem source_nodes_rec (answers : Answers) (labels : Labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b) :
    NodesRec answers labels index coord
      (Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps) := by
  intro level hl c hc
  have hl6:level<6 := by unfold topLevel at hl;split_ifs at hl <;> omega
  have hr : Research.SharedForest.heapCut (decide (first coord.val))≤2^(6-level)+c ∧
      2^(6-level)+c<128 := by
    interval_cases level <;> norm_num at hc ⊢
    all_goals unfold Research.SharedForest.heapCut
    all_goals split_ifs with hf <;> try omega
    all_goals have hf':first coord.val := of_decide_eq_true hf
    all_goals simp only [topLevel,if_pos hf'] at hl
    all_goals omega
  have hg:=Research.SharedForest.sharedNodes_graph answers (decide (first coord.val)) index.val coord.val ps
  have he:=hg.2.2 (2^(6-level)+c) hr.1 hr.2 (by have:=Research.SharedForest.heapCut_bounds (decide (first coord.val));omega)
  have hpad : (if level=4 then (ps (c/2)).2 else (0:Digest))=
      (if level=4 then (pads labels index coord (c/2)).2 else 0) := by
    by_cases h4:level=4
    · subst level
      have hc4:c<4 := by simpa using hc
      rw [if_pos rfl,hps _ (by omega),if_pos rfl]
    · rw [if_neg h4,if_neg h4]
  exact he.trans ((sharedNode_eval answers index coord ps _ _ level c hl hc).trans
    (congrArg (fun pad:Digest=>Extract.Paired.proj (.wctNode index.val coord.val level c)
      (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level)+c)
        ((Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps).getD (2*(2^(6-level)+c)) 0)
        pad
        ((Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps).getD (2*(2^(6-level)+c)+1) 0))))))) hpad))

theorem source_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b)
    (level c : Nat) (hl : level≤topLevel coord) (hc : c<2^(7-level)) :
    (Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps).getD
      (2^(7-level)+c) 0=ftsLabel labels index coord level c := by
  apply nodes_label answers labels h index coord _ _ (source_nodes_rec answers labels index coord ps hps) level c hl hc
  intro j hj
  have hg:=Research.SharedForest.sharedNodes_graph answers (decide (first coord.val)) index.val coord.val ps
  rw [hg.2.1 (128+j) (by omega) (by omega),Nat.add_sub_cancel_left]
  exact source_leaves_label answers labels h index coord ps hps j hj
#print axioms source_nodes_label
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

def pairLabel (labels : Labels) (index : Fin (2^31)) (pair : Fin 5) : Digest×Digest :=
  if h:pair.val=0 then WCT9.ftsStart else
    let coord:Fin 9:=⟨2*pair.val-1,by have:=pair.isLt;omega⟩
    (ftsLabel labels index coord 6 0,ftsLabel labels index coord 6 1)

theorem pads_even (labels : Labels) (index : Fin (2^31)) (pair : Fin 5) (branch : Nat) :
    pads labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ branch=pairLabel labels index pair := by
  fin_cases pair <;> rfl

theorem pads_odd (labels : Labels) (index : Fin (2^31)) (pair : Fin 4) (branch : Nat) :
    pads labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ branch=
      (ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ 5 (2*branch),
       ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ 5 (2*branch+1)) := by
  fin_cases pair <;> rfl

theorem firstNodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (pair : Fin 4) (prev : Digest×Digest)
    (hp : prev=pairLabel labels index ⟨pair.val,by have:=pair.isLt;omega⟩)
    (level c : Nat) (hl : level≤5) (hc : c<2^(7-level)) :
    (Research.SharedForest.firstNodes answers index.val pair.val prev).getD (2^(7-level)+c) 0=
      ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ level c := by
  let coord:Fin 9:=⟨2*pair.val,by have:=pair.isLt;omega⟩
  have hf:first coord.val := by dsimp[coord];unfold first;omega
  have hpads:∀b,b<2 → prev=pads labels index coord b := by
    intro b hb
    exact hp.trans (pads_even labels index ⟨pair.val,by have:=pair.isLt;omega⟩ b).symm
  have he:=source_nodes_label answers labels h index coord (fun _=>prev) hpads level c
    (by simpa only [topLevel,if_pos hf] using hl) hc
  simpa only [coord,Research.SharedForest.firstNodes,decide_eq_true hf] using he

theorem secondNodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (pair : Fin 4) (prev : Digest×Digest)
    (hp : prev=pairLabel labels index ⟨pair.val,by have:=pair.isLt;omega⟩)
    (level c : Nat) (hl : level≤6) (hc : c<2^(7-level)) :
    (Research.SharedForest.secondNodes answers index.val pair.val prev).getD (2^(7-level)+c) 0=
      ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ level c := by
  let coord:Fin 9:=⟨2*pair.val+1,by have:=pair.isLt;omega⟩
  have hf:¬first coord.val := by dsimp[coord];unfold first;omega
  have hpads:∀b,b<2 → Research.SharedForest.nodesPair
      (Research.SharedForest.firstNodes answers index.val pair.val prev) b=pads labels index coord b := by
    intro b hb
    rw [pads_odd labels index pair b]
    unfold Research.SharedForest.nodesPair
    apply Prod.ext
    · exact firstNodes_label answers labels h index pair prev hp 5 (2*b) (by decide) (by norm_num;omega)
    · simpa only [show 2^(7-5)+(2*b+1)=5+2*b by norm_num;omega] using firstNodes_label answers labels h index pair prev hp 5 (2*b+1) (by decide) (by norm_num;omega)
  have he:=source_nodes_label answers labels h index coord
    (Research.SharedForest.nodesPair (Research.SharedForest.firstNodes answers index.val pair.val prev))
    hpads level c (by simpa only [topLevel,if_neg hf] using hl) hc
  simpa only [coord,Research.SharedForest.secondNodes,decide_eq_false hf] using he
#print axioms firstNodes_label
#print axioms secondNodes_label
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

theorem pairLabel_succ (labels : Labels) (index : Fin (2^31)) (pair : Fin 4) :
    pairLabel labels index ⟨pair.val+1,by have:=pair.isLt;omega⟩ =
      (ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ 6 0,
       ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ 6 1) := by
  fin_cases pair <;> rfl

theorem pairPrev_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) : ∀n,(hn:n≤4) →
      Extract.Paired.pairPrev answers index.val n=pairLabel labels index ⟨n,by omega⟩
  | 0,_=>rfl
  | n+1,hn=>by
    have ih:=pairPrev_label answers labels h index n (by omega)
    rw [Extract.Paired.pairPrev,pairLabel_succ labels index ⟨n,by omega⟩]
    apply Prod.ext
    · exact secondNodes_label answers labels h index ⟨n,by omega⟩ _ ih 6 0 (by decide) (by decide)
    · exact secondNodes_label answers labels h index ⟨n,by omega⟩ _ ih 6 1 (by decide) (by decide)

theorem source_pads_even (answers : Answers) (index : Nat) (pair : Fin 5) (branch : Nat) :
    Extract.Paired.pads answers index (2*pair.val) branch=Extract.Paired.pairPrev answers index pair.val := by
  fin_cases pair <;> rfl

theorem source_pads_odd (answers : Answers) (index : Nat) (pair : Fin 4) (branch : Nat) :
    Extract.Paired.pads answers index (2*pair.val+1) branch=
      Research.SharedForest.nodesPair
        (Research.SharedForest.firstNodes answers index pair.val (Extract.Paired.pairPrev answers index pair.val)) branch := by
  fin_cases pair <;> rfl

theorem source_pads_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (hb:branch<2) :
    Extract.Paired.pads answers index.val coord.val branch=pads labels index coord branch := by
  by_cases he:coord.val%2=0
  · let p:Fin 5:=⟨coord.val/2,by have:=coord.isLt;omega⟩
    have hc:coord=⟨2*p.val,by have:=p.isLt;omega⟩:=by apply Fin.ext;dsimp[p];omega
    rw [hc]
    rw [source_pads_even,pads_even,pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)]
  · let p:Fin 4:=⟨coord.val/2,by have:=coord.isLt;omega⟩
    have hc:coord=⟨2*p.val+1,by have:=p.isLt;omega⟩:=by apply Fin.ext;dsimp[p];omega
    rw [hc]
    rw [source_pads_odd,pads_odd]
    unfold Research.SharedForest.nodesPair
    apply Prod.ext
    · exact firstNodes_label answers labels h index p _
        (pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)) 5 (2*branch) (by decide) (by norm_num;omega)
    · simpa only [show 2^(7-5)+(2*branch+1)=5+2*branch by norm_num;omega] using firstNodes_label answers labels h index p _
        (pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)) 5 (2*branch+1) (by decide) (by norm_num;omega)
#print axioms pairPrev_label
#print axioms source_pads_label
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

theorem nodes_source (answers : Answers) (index : Nat) (coord : Fin 9) :
    Extract.Paired.nodes answers index coord.val = Research.SharedForest.sharedNodes (answers)
      (decide (first coord.val)) index coord.val (Extract.Paired.pads answers index coord.val) := by
  fin_cases coord <;> simp only [Extract.Paired.nodes,Extract.Paired.first,first,Research.SharedForest.firstNodes,Research.SharedForest.secondNodes]
  all_goals norm_num
  all_goals first | rfl | (congr 1;funext b;simp only [Extract.Paired.pads,Extract.Paired.first,Research.SharedForest.firstNodes];rfl)

theorem actual_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : level≤topLevel coord) (hc:c<2^(7-level)) :
    (Extract.Paired.nodes answers index.val coord.val).getD (2^(7-level)+c) 0=
      ftsLabel labels index coord level c := by
  rw [nodes_source]
  exact source_nodes_label answers labels h index coord _ (source_pads_label answers labels h index coord) level c hl hc

theorem actual_leaf_pad (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (raw : Fin 128) :
    Extract.Paired.pads answers index.val coord.val (Extract.Paired.physical coord.val raw.val/64)=
      pads labels index coord (raw.val%2) := by
  have hp:Extract.Paired.physical coord.val raw.val<128 :=
    Research.SharedForest.physicalChild_lt _ _ raw.isLt
  rw [source_pads_label answers labels h index coord _ (by omega),pads_raw_branch labels index coord _ hp]
  congr 1
  have he:rawLeaf coord.val (Extract.Paired.physical coord.val raw.val)=raw.val := by
    rw [←rawChild_eq]
    exact Research.SharedForest.raw_physical_child _ _ raw.isLt
  rw [he]
#print axioms actual_nodes_label
#print axioms actual_leaf_pad
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph SigGolfCandidate.T3.Security.Wots SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

theorem honestInput_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    Extract.Paired.honestInput answers node.toPos=cell (secretsOf answers) node labels := by
  cases node with
  | chain p=>
      simp only [Node.toPos,Extract.Paired.honestInput,Extract.honestInput]
      rw [chainValue_eq h p.1 p.2.val (by have:=p.2.isLt;omega)]
      change pad64 (SigGolfCandidate.T3.Security.ChainGraph.row p _)=SigGolfCandidate.T3.Security.ChainGraph.row p (SigGolfCandidate.T3.Security.ChainGraph.prior _ p _)
      rw [SigGolfCandidate.T3.Security.ChainGraph.row_pad64,SigGolfCandidate.T3.Security.ChainGraph.prior_eq_value]
  | leaf L=>
      simp only [Node.toPos,Extract.Paired.honestInput,Extract.honestInput,cell,CanonGraph.cell]
      rw [leafEnds_eq h L.1]
  | node n=>
      obtain ⟨⟨lay,tree,level,idx⟩,hv1,hv2,hv3,hv4⟩:=n
      change level.val<height lay at hv1
      change idx.val<2^(height lay-level.val-1) at hv2
      change tree.val<2^Extract.treeBits lay at hv3
      change lay=0 ∨ level.val+1<height lay at hv4
      simp only [Node.toPos,Extract.Paired.honestInput,Extract.honestInput,cell,CanonGraph.cell]
      have hpow:2^(height lay-level.val)=2*2^(height lay-level.val-1) := by
        rw [←pow_succ'];congr 1;omega
      rw [builtTree_eq h lay tree level.val (2*idx.val) (by omega) (by omega) hv3 (by omega),
        builtTree_eq h lay tree level.val (2*idx.val+1) (by omega) (by omega) hv3 (by omega)]
  | wctChain p=>
      simp only [Node.toPos,Extract.Paired.honestInput,Extract.honestInput,cell,CanonGraph.cell]
      rw [wctValue_eq h p.1 p.2.val (by have:=p.2.isLt;omega),Extract.pad64_wctChainInput]
  | wctLeaf L=>
      simp only [Node.toPos,Extract.Paired.honestInput,cell]
      rw [wctEnds_eq h L,actual_leaf_pad answers labels h L.index L.coord L.child]
  | wctNode n=>
      obtain ⟨⟨index,coord,level,idx⟩,hv⟩:=n
      have hv':idx.val<2^(7-level.val-1):=hv
      have hl6:=level.isLt
      have ht:level.val≤topLevel coord := by
        unfold topLevel
        split_ifs with hf
        · have hused:=hb.2 (by change decide (first coord.val)=true;exact decide_eq_true hf)
          omega
        · omega
      have hpow:2^(7-level.val)=2*2^(6-level.val) := by
        rw [←pow_succ'];congr 1;omega
      have hsub:7-level.val-1=6-level.val := by omega
      rw [hsub] at hv'
      simp only [Node.toPos,Extract.Paired.honestInput,cell,hsub]
      change pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level.val)+idx.val)
        ((Extract.Paired.nodes answers index.val coord.val).getD (2*(2^(6-level.val)+idx.val)) 0)
        (if level.val=4 then (Extract.Paired.pads answers index.val coord.val ((2^(6-level.val)+idx.val)/2-2)).2 else 0)
        ((Extract.Paired.nodes answers index.val coord.val).getD (2*(2^(6-level.val)+idx.val)+1) 0))= _
      rw [show 2*(2^(6-level.val)+idx.val)=2^(7-level.val)+2*idx.val by omega,
        show 2^(7-level.val)+2*idx.val+1=2^(7-level.val)+(2*idx.val+1) by omega,
        actual_nodes_label answers labels h index coord level.val (2*idx.val) ht (by omega),
        actual_nodes_label answers labels h index coord level.val (2*idx.val+1) ht (by omega)]
      by_cases h4:level.val=4
      · rw [if_pos h4,h4]
        have hi:idx.val<4 := by simpa [h4] using hv'
        rw [show (2^(6-4)+idx.val)/2-2=idx.val/2 by norm_num;omega,
          source_pads_label answers labels h index coord _ (by omega),if_pos rfl]
      · rw [if_neg h4,if_neg h4]
  | forest index=>exact hb.elim

theorem honest_answer (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    answers (.inl (.inr (Extract.Paired.honestInput answers node.toPos)))=labels node := by
  rw [honestInput_eq answers labels h node hb]
  exact h node
#print axioms honestInput_eq
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open Correctness (Answers)
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def completeNonforest (answers : Answers) (labels : Labels) : Labels := fun node =>
  if Used node then labels node else answers (.inl (.inr (Paired.cell (secretsOf answers) node labels)))
noncomputable def completeLabels (answers : Answers) (labels : Labels) : Labels
  | .forest i => answers (.inl (.inr (Paired.cell (secretsOf answers) (.forest i) (completeNonforest answers labels))))
  | node => completeNonforest answers labels node

theorem completeNonforest_used (answers : Answers) (labels : Labels) (node : Node) (hu : Used node) :
    completeNonforest answers labels node=labels node := if_pos hu

theorem completeLabels_nonforest (answers : Answers) (labels : Labels) (node : Node)
    (hnf : ∀i,node≠.forest i) :
    completeLabels answers labels node=completeNonforest answers labels node := by
  cases node <;> first | rfl | exact (hnf _ rfl).elim

theorem completeLabels_used (answers : Answers) (labels : Labels) (node : Node) (hu : Used node) :
    completeLabels answers labels node=labels node := by
  rw [completeLabels_nonforest answers labels node (by intro i hi; subst node; exact hu)]
  exact completeNonforest_used answers labels node hu

theorem completeLabels_agrees {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    Paired.Agrees answers (completeLabels answers labels) := by
  intro node
  by_cases hnf : ∀i,node≠.forest i
  · have hc := cell_congr_nonforest (secretsOf answers) node hnf (completeLabels answers labels) labels
      (fun other hu _ => completeLabels_used answers labels other hu)
    rw [hc,completeLabels_nonforest answers labels node hnf]
    by_cases hu : Used node
    · rw [completeNonforest_used answers labels node hu]
      exact h node hu
    · simp only [completeNonforest, if_neg hu]
  · push_neg at hnf
    obtain ⟨i,hi⟩ := hnf
    subst node
    have hc : Paired.cell (secretsOf answers) (.forest i) (completeLabels answers labels) =
        Paired.cell (secretsOf answers) (.forest i) (completeNonforest answers labels) := by
      apply Paired.cell_congr
      intro other hd
      apply completeLabels_nonforest
      intro j hj
      subst other
      simp only [Node.depth,lt_self_iff_false] at hd
    change answers (.inl (.inr (Paired.cell _ _ _))) = answers (.inl (.inr (Paired.cell _ _ _)))
    rw [hc]

theorem honestInput_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    Extract.Paired.honestInput answers node.toPos=Paired.cell (secretsOf answers) node labels := by
  rw [Paired.honestInput_eq answers (completeLabels answers labels) (completeLabels_agrees h) node hb]
  exact cell_congr _ node ((used_iff_bounded node).2 hb) _ _
    (fun other hu _ => completeLabels_used answers labels other hu)

theorem honest_answer (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    answers (.inl (.inr (Extract.Paired.honestInput answers node.toPos)))=labels node := by
  rw [honestInput_eq answers labels h node hb]
  exact h node ((used_iff_bounded node).2 hb)

theorem treeLabel_complete (answers : Answers) (labels : Labels)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel (completeLabels answers labels) lay tree level c=treeLabel labels lay tree level c :=
  treeLabel_congr _ _ _ _ _ _ (fun other hu _ => completeLabels_used answers labels other hu)

theorem ftsLabel_complete (answers : Answers) (labels : Labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hl : first coord.val → level≤5) :
    Paired.ftsLabel (completeLabels answers labels) index coord level c=Paired.ftsLabel labels index coord level c :=
  ftsLabel_congr _ _ _ _ _ _ hl (fun other hu _ => completeLabels_used answers labels other hu)

theorem honestPair_eq {answers : Answers} {labels : Labels} (h : Agrees answers labels)
    (lay : Layer) (tree : Fin (2^31)) (ht : tree.val<2^Extract.treeBits lay) :
    Extract.honestPair answers lay tree.val =
      (treeLabel labels lay tree (height lay-1) 0,treeLabel labels lay tree (height lay-1) 1) := by
  rw [Paired.honestPair_eq (completeLabels_agrees h) lay tree ht,
    treeLabel_complete,treeLabel_complete]

theorem actual_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : level≤Paired.topLevel coord) (hc : c<2^(7-level)) :
    (Extract.Paired.nodes answers index.val coord.val).getD (2^(7-level)+c) 0=
      Paired.ftsLabel labels index coord level c := by
  rw [Paired.actual_nodes_label answers (completeLabels answers labels) (completeLabels_agrees h) index coord level c hl hc]
  apply ftsLabel_complete
  intro hf
  unfold Paired.topLevel at hl
  rw [if_pos hf] at hl
  omega
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
