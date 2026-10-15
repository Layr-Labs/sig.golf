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
theorem leafValue_eq (h : Agrees answers labels) (L : LeafPos) (digits : List Nat) (i : Nat) (hi : i < 58)
    (hdigit : digits.getD i 0 ≤ 7) :
    WCT9.wotsValue answers L.lay L.tree.val L.leaf.val digits i =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) ⟨L.lay, L.tree, L.leaf, fin58 i⟩
        (digits.getD i 0) := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hx := chainValue_eq h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ (digits.getD i 0) hdigit
  simp only [hval] at hx
  exact hx
theorem leafEnd_eq (h : Agrees answers labels) (L : LeafPos) (i : Nat) (hi : i < 58) :
    WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val i = endLabel (secretsOf answers) labels L i := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hx := chainValue_eq h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ (maxDigit L.lay i) (maxDigit_le_seven L.lay i)
  simp only [hval] at hx
  exact hx
theorem leafEnds_eq (h : Agrees answers labels) (L : LeafPos) :
    (List.range (chainCount L.lay)).map (WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val) =
      (List.range (chainCount L.lay)).map (endLabel (secretsOf answers) labels L) := by
  apply List.map_congr_left
  intro i hi
  exact leafEnd_eq h L i (lt_of_lt_of_le (List.mem_range.mp hi) (chainCount_bound L.lay))
theorem leafRoot_eq (h : Agrees answers labels) (L : SrcLeaf) :
    WCT9.wotsRoot answers L.1.lay L.1.tree.val L.1.leaf.val = (labels (.leaf L)).extractLsb' 0 128 := by
  unfold WCT9.wotsRoot
  rw [show leafHash L.1.lay L.1.tree.val L.1.leaf.val ((List.range (chainCount L.1.lay)).map
      (WCT9.wotsEnd answers L.1.lay L.1.tree.val L.1.leaf.val)) =
      shortHash (Extract.leafInput L.1.lay L.1.tree.val L.1.leaf.val
      ((List.range (chainCount L.1.lay)).map (WCT9.wotsEnd answers L.1.lay L.1.tree.val L.1.leaf.val))) from rfl,
    eval_shortHash, leafEnds_eq h L.1]
  exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.leaf L))
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
      rw [hrec, nodeHash_eq_shortHash, eval_shortHash]
      unfold treeLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      simp only
      have hinput : cell (secretsOf answers) (.node n) labels =
          pad64 (nodeInputP 3 lay.val tree.val (2 ^ (height lay - (level + 1)) + c)
            (((WCT9.wotsTree answers lay tree.val).getD level []).getD (2 * c) 0) 0
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
      rw [← hinput]
      exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.node n))
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
theorem childRoot_eq (h : Agrees answers labels) (L : WctLeafPos) :
    WCT9.childRoot answers L.index.val L.coord.val L.child.val = (labels (.wctLeaf L)).extractLsb' 0 128 := by
  have hends : (List.ofFn fun i : Fin 6 => WCT9.chainEnd answers L.index.val L.coord.val L.child.val i) =
      Extract.wctEnds answers L.index.val L.coord.val L.child.val := rfl
  have hleaf : ∀ ends : List Digest, WCT9.leafHash L.index.val L.coord.val L.child.val ends =
      shortHash (Extract.wctLeafInput L.index.val L.coord.val L.child.val ends) := by
    intro ends
    unfold WCT9.leafHash Extract.wctLeafInput Extract.listInput
    simp only [List.flatMap_cons, WCT9.bytesLE_zero16, List.append_assoc]
  unfold WCT9.childRoot
  rw [hleaf, hends, wctEnds_eq h L]
  change (answers (.inl (.inr (pad64 (Extract.wctLeafInput L.index.val L.coord.val L.child.val
    (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t))))))).extractLsb' 0 128 = _
  exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.wctLeaf L))
theorem ftsNodeAt_some (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hlevel : level < 6)
    (hc : c < 2 ^ (7 - level - 1)) :
    ∃ n : WctNodePos, ftsNodeAt index coord level c = some n ∧ n.1.index = index ∧ n.1.coord = coord ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold ftsNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem ftsTree_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hlevel : level ≤ 6) (hc : c < 2 ^ (7 - level)) :
    treeValue (Extract.ftsLevels answers index.val coord.val) level c = ftsLabel labels index coord level c := by
  have hinv := WCT9.heap_complete answers index.val coord.val (Extract.ftsLeaves answers index.val coord.val)
    (by simp [Extract.ftsLeaves])
  have hleaves : ∀ j (hj : j < 128), (Extract.ftsLeaves answers index.val coord.val).getD j 0 =
      (labels (.wctLeaf ⟨index, coord, ⟨j, hj⟩⟩)).extractLsb' 0 128 := by
    intro j hj
    unfold Extract.ftsLeaves
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hj), List.getElem_ofFn]
    exact childRoot_eq h ⟨index, coord, ⟨j, hj⟩⟩
  unfold Extract.ftsLevels Extract.ftsNodes
  generalize evalWithAnswerFn answers (WCT9.heapBuild index.val coord.val
    (Extract.ftsLeaves answers index.val coord.val)) = X at hinv ⊢
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
      have hrhs : ftsLabel labels index coord (level + 1) c = (labels (.wctNode n)).extractLsb' 0 128 := by
        unfold ftsLabel
        rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      have hinput : cell (secretsOf answers) (.wctNode n) labels =
          pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2 ^ (7 - level - 1) + c)
            (ftsLabel labels index coord level (2 * c)) 0 (ftsLabel labels index coord level (2 * c + 1))) := by
        obtain ⟨⟨nindex, ncoord, nlevel, nidx⟩, hv⟩ := n
        simp only at hindex hcoord hlev hidx
        subst hindex hcoord
        simp only [cell]
        rw [hlev, hidx]
      rw [hrhs, WCT9.heapLevels_value X (level + 1) c (by omega) hc, hsub]
      have hl := WCT9.heapLevels_value X level (2 * c) (by omega) (by omega)
      have hr := WCT9.heapLevels_value X level (2 * c + 1) (by omega) (by omega)
      rw [hnode (2 ^ (7 - level - 1) + c) (by omega) (by omega) (by omega), WCT9.wctNodeHash, nodeHash_eq_shortHash,
        eval_shortHash]
      have e1 : 2 * (2 ^ (7 - level - 1) + c) = 2 ^ (7 - level) + 2 * c := by omega
      rw [e1, show 2 ^ (7 - level) + 2 * c + 1 = 2 ^ (7 - level) + (2 * c + 1) by omega, ← hl, ← hr,
        hchild (2 * c) (by omega), hchild (2 * c + 1) (by omega)]
      rw [← hinput]
      exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.wctNode n))
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
theorem honestForest_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    Extract.honestForest answers index.val = (labels (.forest index)).extractLsb' 0 128 := by
  unfold Extract.honestForest
  rw [show WCT9.forestPk index.val (Extract.ftsPairsHonest answers index.val) =
      shortHash (Extract.forestInput index.val (Extract.ftsPairsHonest answers index.val)) from rfl,
    eval_shortHash, ftsPairs_eq h index]
  exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.forest index))
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
      rw [wctEnds_eq h L]
  | wctNode n =>
      obtain ⟨⟨index, coord, level, idx⟩, hv⟩ := n
      have hv' : idx.val < 2 ^ (7 - level.val - 1) := hv
      simp only [Node.toPos, Extract.honestInput, cell]
      have hpow : 2 ^ (7 - level.val) = 2 * 2 ^ (7 - level.val - 1) := by
        have := level.isLt
        rw [← pow_succ']; congr 1; omega
      rw [ftsTree_eq h index coord level.val (2 * idx.val) (by have := level.isLt; omega) (by omega),
        ftsTree_eq h index coord level.val (2 * idx.val + 1) (by have := level.isLt; omega) (by omega)]
  | forest index =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [ftsPairs_eq h index]
theorem honest_answer (h : Agrees answers labels) (node : Node) :
    answers (.inl (.inr (Extract.honestInput answers node.toPos))) = labels node := by
  rw [honestInput_eq h node]
  exact h node
end Honest
end ClaudeWCT.W9.T3.Security.CanonGraph
