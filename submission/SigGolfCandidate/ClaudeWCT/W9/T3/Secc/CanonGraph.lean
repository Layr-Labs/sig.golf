import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header

namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure LeafPos where
  lay : Layer
  tree : Fin (2^31)
  leaf : Fin 4096
  deriving DecidableEq, Fintype
export ClaudeWCT.W9.T3M.Extract (treeBits)
def LeafPos.Source (L : LeafPos) : Prop := L.tree.val < 2 ^ treeBits L.lay ∧ L.leaf.val < 2 ^ height L.lay
instance instDecidablePredLeafPosSource : DecidablePred LeafPos.Source := fun L => by unfold LeafPos.Source; infer_instance
theorem LeafPos.Source.routed {L : LeafPos} (h : L.Source) :
    L.leaf.val < 2 ^ height L.lay ∧ L.tree.val * 2 ^ height L.lay + L.leaf.val < 2 ^ 32 :=
  ⟨h.2, lt_trans (ClaudeWCT.W9.T3M.Extract.routed_lt_of_treeBits h.1 h.2) (by norm_num)⟩
abbrev SrcLeaf := {L : LeafPos // L.Source}
structure TreeNodeRaw where
  lay : Layer
  tree : Fin (2^31)
  level : Fin 12
  idx : Fin 2048
  deriving DecidableEq, Fintype
def TreeNodeRaw.Valid (n : TreeNodeRaw) : Prop :=
  n.level.val < height n.lay ∧ n.idx.val < 2 ^ (height n.lay - n.level.val - 1) ∧
    n.tree.val < 2 ^ treeBits n.lay ∧ (n.lay = 0 ∨ n.level.val + 1 < height n.lay)
instance instDecidablePredTreeNodeRawValid : DecidablePred TreeNodeRaw.Valid := fun n => by unfold TreeNodeRaw.Valid; infer_instance
abbrev TreeNode := {n : TreeNodeRaw // n.Valid}
abbrev WctAddr := Fin (2 ^ 31) × Fin 9 × Fin 128 × Fin 6
abbrev WctPoint := WctAddr × Fin 4
structure WctLeafPos where
  index : Fin (2^31)
  coord : Fin 9
  child : Fin 128
  deriving DecidableEq, Fintype
structure WctNodeRaw where
  index : Fin (2^31)
  coord : Fin 9
  level : Fin 6
  idx : Fin 64
  deriving DecidableEq, Fintype
def WctNodeRaw.Valid (n : WctNodeRaw) : Prop := n.idx.val < 2 ^ (7 - n.level.val - 1)
instance instDecidablePredWctNodeRawValid : DecidablePred WctNodeRaw.Valid := fun n => by unfold WctNodeRaw.Valid; infer_instance
abbrev WctNodePos := {n : WctNodeRaw // n.Valid}
inductive Node where
  | chain (point : Point)
  | leaf (pos : SrcLeaf)
  | node (pos : TreeNode)
  | wctChain (point : WctPoint)
  | wctLeaf (pos : WctLeafPos)
  | wctNode (pos : WctNodePos)
  | forest (index : Fin (2^31))
  deriving DecidableEq, Fintype
attribute [local irreducible] ChainGraph.instFintypeAddress
def Node.depth : Node → Nat
  | .chain p => p.2.val
  | .leaf _ => 7
  | .node n => 8 + n.1.level.val
  | .wctChain p => p.2.val
  | .wctLeaf _ => 4
  | .wctNode n => 5 + n.1.level.val
  | .forest _ => 11
/-- Coefficient index of the FTS seed families (campaign X1, stage A): `(index, coord, j)`, `j < 102`. -/
abbrev WctCoef := Fin (2 ^ 31) × Fin 9 × Fin 102
/-- Hidden secrets: leaf-family coefficients (by address: an address with chain `j < famCount layer` is coefficient
`j` of its leaf, campaign X1 stage B for lower leaves, campaign T8D for top leaves) and FTS family coefficients. WOTS and
FTS seeds are not secrets themselves but evaluations (`seedsOf`, `wctSeedsOf`) of the coefficient families. -/
abbrev SecretIndex := Address ⊕ WctCoef
abbrev Secrets := SecretIndex → Digest
abbrev Labels := Node → HashOutput
theorem chainCount_lower {lay : Layer} (h : lay ≠ 0) : chainCount lay = 43 := by
  revert h; fin_cases lay <;> decide
theorem famCount_lt_58 (lay : Layer) : WCT9.famCount lay < 58 := by
  have := WCT9.famCount_le lay; omega
/-- The coefficient family of leaf `(lay, tree, leaf)`: the secrets of its chains `j < famCount lay`. -/
def leafFamily (secrets : Secrets) (lay : Layer) (tree : Fin (2 ^ 31)) (leaf : Fin 4096) :
    Fin (WCT9.famCount lay) → Digest :=
  fun j => secrets (.inl ⟨lay, tree, leaf, ⟨j.val, lt_trans j.isLt (famCount_lt_58 lay)⟩⟩)
/-- WOTS seeds: the leaf family at `chain + 1` (every layer). -/
def seedsOf (secrets : Secrets) : Seeds := fun a =>
  ClaudeWCT.Arith.familyEval (List.ofFn (leafFamily secrets a.layer a.tree a.leaf)) (a.chain.val + 1)
/-- The coefficient family of FTS coordinate `(index, coord)`. -/
def wctFamily (secrets : Secrets) (index : Fin (2 ^ 31)) (coord : Fin 9) : Fin 102 → Digest :=
  fun j => secrets (.inr (index, coord, j))
/-- FTS seed of chain `a`: its family evaluated at `ftsPoint child chain` in GF(2^128). -/
def wctSeedsOf (secrets : Secrets) : WctAddr → Digest := fun a =>
  ClaudeWCT.Arith.familyEval (List.ofFn (wctFamily secrets a.1 a.2.1)) (WCT9.ftsPoint a.2.2.1.val a.2.2.2.val)
def chainLabels (labels : Labels) : ChainGraph.Labels := fun point => labels (.chain point)
def fin58 (i : Nat) : Fin 58 := ⟨i % 58, Nat.mod_lt _ (by decide)⟩
def fin9 (i : Nat) : Fin 9 := ⟨i % 9, Nat.mod_lt _ (by decide)⟩
def endLabel (secrets : Secrets) (labels : Labels) (L : LeafPos) (i : Nat) : Digest :=
  ChainGraph.value (seedsOf secrets) (chainLabels labels) ⟨L.lay, L.tree, L.leaf, fin58 i⟩ (maxDigit L.lay i)
def wctValueL (secrets : Secrets) (labels : Labels) (a : WctAddr) (s : Nat) : Digest :=
  if s = 0 then wctSeedsOf secrets a
  else (labels (.wctChain (a, ⟨(s - 1) % 4, Nat.mod_lt _ (by decide)⟩))).extractLsb' 0 128
def wctEndLabel (labels : Labels) (a : WctAddr) : Digest := (labels (.wctChain (a, 3))).extractLsb' 0 128
/-- The chain end (campaign T8: position 4; the name is kept from the 3-step code). -/
theorem wctValueL_three (secrets : Secrets) (labels : Labels) (a : WctAddr) :
    wctValueL secrets labels a 4 = wctEndLabel labels a := rfl
def treeNodeAt (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option TreeNode :=
  if h : level < height lay ∧ c < 2 ^ (height lay - level - 1) ∧ tree.val < 2 ^ treeBits lay ∧
      (lay = 0 ∨ level + 1 < height lay) then
    some ⟨⟨lay, tree, ⟨level, lt_of_lt_of_le h.1 (SigGolfCandidate.T3M.Extract.height_le lay)⟩,
      ⟨c, lt_of_lt_of_le h.2.1 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := SigGolfCandidate.T3M.Extract.height_le lay; omega)
          _ = 2048 := by norm_num)⟩⟩, h⟩
  else none
theorem height_le_12 (lay : Layer) : 2 ^ height lay ≤ 4096 :=
  (Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)).trans (by norm_num)
def leafAt (lay : Layer) (tree : Fin (2^31)) (c : Nat) : Option SrcLeaf :=
  if h : c < 2 ^ height lay ∧ tree.val < 2 ^ treeBits lay then
    some ⟨⟨lay, tree, ⟨c, lt_of_lt_of_le h.1 (height_le_12 lay)⟩⟩, ⟨h.2, h.1⟩⟩
  else none
def treeLabel (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  if level = 0 then
    (match leafAt lay tree c with
     | some L => (labels (.leaf L)).extractLsb' 0 128
     | none => 0)
  else
    match treeNodeAt lay tree (level - 1) c with
    | some n => (labels (.node n)).extractLsb' 0 128
    | none => 0
def ftsNodeAt (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Option WctNodePos :=
  if h : level < 6 ∧ c < 2 ^ (7 - level - 1) then
    some ⟨⟨index, coord, ⟨level, h.1⟩, ⟨c, lt_of_lt_of_le h.2 (by
      calc 2 ^ (7 - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 64 := by norm_num)⟩⟩, h.2⟩
  else none
def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 128 then (labels (.wctLeaf ⟨index, coord, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match ftsNodeAt index coord (level - 1) c with
    | some n => (labels (.wctNode n)).extractLsb' 0 128
    | none => 0
def cell (secrets : Secrets) : Node → Labels → HashInput
  | .chain p, labels => ChainGraph.input (seedsOf secrets) p (chainLabels labels)
  | .leaf L, labels => pad64 (Extract.leafInput L.1.lay L.1.tree.val L.1.leaf.val
      ((List.range (chainCount L.1.lay)).map (endLabel secrets labels L.1)))
  | .node n, labels => pad64 (nodeInputP 3 n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)) 0
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)))
  | .wctChain p, labels => WCT9.chainInput p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
      (wctValueL secrets labels p.1 p.2.val)
  | .wctLeaf L, labels => pad64 (Extract.wctLeafInput L.index.val L.coord.val L.child.val
      (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t)))
  | .wctNode n, labels => pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2 ^ (7 - n.1.level.val - 1) + n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)) 0
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)))
  | .forest index, labels => pad64 (Extract.forestInput index.val
      ((List.range 9).map fun coord => (ftsLabel labels index (fin9 coord) 6 0, ftsLabel labels index (fin9 coord) 6 1)))
def Node.toPos : Node → Extract.Pos
  | .chain p => .chain p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val
  | .leaf L => .leaf L.1.lay L.1.tree.val L.1.leaf.val
  | .node n => .node n.1.lay n.1.tree.val n.1.level.val n.1.idx.val
  | .wctChain p => .wctChain p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
  | .wctLeaf L => .wctLeaf L.index.val L.coord.val L.child.val
  | .wctNode n => .wctNode n.1.index.val n.1.coord.val n.1.level.val n.1.idx.val
  | .forest index => .forest index.val
def SourcePos : Extract.Pos → Prop
  | .chain _ tree leaf i step => tree < 2 ^ 31 ∧ leaf < 4096 ∧ i < 58 ∧ step < 7
  | .leaf lay tree leaf => tree < 2 ^ treeBits lay ∧ leaf < 2 ^ height lay
  | .node lay tree level nd => tree < 2 ^ treeBits lay ∧ level < height lay ∧ nd < 2 ^ (height lay - level - 1) ∧
      (lay = 0 ∨ level + 1 < height lay)
  | .forest index => index < 2 ^ 31
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6 ∧ step < 4
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
theorem treeBits_lt (lay : Layer) : 2 ^ treeBits lay ≤ 2 ^ 31 :=
  Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide)
theorem source_routed_lt {lay : Layer} {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay) (hl : leaf < 2 ^ height lay) :
    tree * 2 ^ height lay + leaf < 2 ^ 31 := by
  fin_cases lay <;> simp [treeBits, Extract.treeBits, height] at ht hl ⊢ <;> omega
theorem source_tree_zero {lay : Layer} {tree : Nat} (ht : tree < 2 ^ treeBits lay) : lay = 0 → tree = 0 := by
  rintro rfl; simpa [treeBits, Extract.treeBits] using ht
theorem toPos_bounded (node : Node) : node.toPos.Bounded := by
  cases node with
  | chain p =>
      have := p.1.tree.isLt; have := p.1.leaf.isLt; have := p.1.chain.isLt; have := p.2.isLt
      exact ⟨by omega, by omega, by omega, by omega⟩
  | leaf L =>
      have := source_routed_lt L.2.1 L.2.2
      exact ⟨L.2.2, by omega⟩
  | node n =>
      have := n.1.tree.isLt
      exact ⟨by omega, n.2.1, n.2.2.2.2, source_tree_zero n.2.2.2.1, n.2.2.1⟩
  | wctChain p => exact ⟨p.1.1.isLt, p.1.2.1.isLt, p.1.2.2.1.isLt, p.1.2.2.2.isLt, p.2.isLt⟩
  | wctLeaf L => exact ⟨L.index.isLt, L.coord.isLt, L.child.isLt⟩
  | wctNode n => exact ⟨n.1.index.isLt, n.1.coord.isLt, n.1.level.isLt, n.2⟩
  | forest index => have := index.isLt; change index.val < 2 ^ 40; omega
theorem toPos_injective : Function.Injective Node.toPos := by
  intro left right h
  cases left with
  | chain p =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i q
      simp only [Extract.Pos.chain.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hp : p = q := Prod.ext (ChainGraph.Address.ext h1 (Fin.ext h2) (Fin.ext h3) (Fin.ext h4)) (Fin.ext h5)
      rw [hp]
  | leaf L =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i M
      simp only [Extract.Pos.leaf.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨⟨lay, tree, leaf⟩, hL⟩ := L; obtain ⟨⟨lay', tree', leaf'⟩, hM⟩ := M
      simp only at h1 h2 h3
      subst h1
      have e2 := Fin.ext h2; have e3 := Fin.ext h3
      subst e2 e3
      rfl
  | node n =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i m
      simp only [Extract.Pos.node.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨⟨lay, tree, level, idx⟩, hn⟩ := n
      obtain ⟨⟨lay', tree', level', idx'⟩, hm⟩ := m
      simp only at h1 h2 h3 h4
      subst h1
      have e2 := Fin.ext h2; have e3 := Fin.ext h3; have e4 := Fin.ext h4
      subst e2 e3 e4
      rfl
  | wctChain p =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i q
      simp only [Extract.Pos.wctChain.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      obtain ⟨⟨i, k, j, t⟩, s⟩ := p
      obtain ⟨⟨i', k', j', t'⟩, s'⟩ := q
      simp only at h1 h2 h3 h4 h5
      rw [Fin.ext h1, Fin.ext h2, Fin.ext h3, Fin.ext h4, Fin.ext h5]
  | wctLeaf L =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i M
      simp only [Extract.Pos.wctLeaf.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      cases L; cases M
      simp only at h1 h2 h3
      rw [Fin.ext h1, Fin.ext h2, Fin.ext h3]
  | wctNode n =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i m
      simp only [Extract.Pos.wctNode.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨⟨index, coord, level, idx⟩, hn⟩ := n
      obtain ⟨⟨index', coord', level', idx'⟩, hm⟩ := m
      simp only at h1 h2 h3 h4
      have e1 := Fin.ext h1; have e2 := Fin.ext h2; have e3 := Fin.ext h3; have e4 := Fin.ext h4
      subst e1 e2 e3 e4
      rfl
  | forest index =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i index'
      simp only [Extract.Pos.forest.injEq] at h
      rw [Fin.ext h]
theorem exists_toPos {p : Extract.Pos} (hp : SourcePos p) : ∃ node : Node, node.toPos = p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      exact ⟨.chain (⟨lay, ⟨tree, h1⟩, ⟨leaf, h2⟩, ⟨i, h3⟩⟩, ⟨step, h4⟩), rfl⟩
  | leaf lay tree leaf =>
      obtain ⟨h1, h2⟩ := hp
      exact ⟨.leaf ⟨⟨lay, ⟨tree, lt_of_lt_of_le h1 (treeBits_lt lay)⟩, ⟨leaf, lt_of_lt_of_le h2 (height_le_12 lay)⟩⟩,
        ⟨h1, h2⟩⟩, rfl⟩
  | node lay tree level nd =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have hl : level < 12 := lt_of_lt_of_le h2 (SigGolfCandidate.T3M.Extract.height_le lay)
      have hn : nd < 2048 := lt_of_lt_of_le h3 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := SigGolfCandidate.T3M.Extract.height_le lay; omega)
          _ = 2048 := by norm_num)
      exact ⟨.node ⟨⟨lay, ⟨tree, lt_of_lt_of_le h1 (treeBits_lt lay)⟩, ⟨level, hl⟩, ⟨nd, hn⟩⟩, h2, h3, h1, h4⟩, rfl⟩
  | forest index => exact ⟨.forest ⟨index, hp⟩, rfl⟩
  | wctChain index coord child t step =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hp
      exact ⟨.wctChain ((⟨index, h1⟩, ⟨coord, h2⟩, ⟨child, h3⟩, ⟨t, h4⟩), ⟨step, h5⟩), rfl⟩
  | wctLeaf index coord child =>
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨.wctLeaf ⟨⟨index, h1⟩, ⟨coord, h2⟩, ⟨child, h3⟩⟩, rfl⟩
  | wctNode index coord level nd =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have hn : nd < 64 := lt_of_lt_of_le h4 (by
        calc 2 ^ (7 - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 64 := by norm_num)
      exact ⟨.wctNode ⟨⟨⟨index, h1⟩, ⟨coord, h2⟩, ⟨level, h3⟩, ⟨nd, hn⟩⟩, h4⟩, rfl⟩
theorem hdrBlock_cell (secrets : Secrets) (node : Node) (labels : Labels) :
    Extract.hdrBlock (cell secrets node labels) = bytesLE 16 node.toPos.hdr := by
  cases node with
  | chain p =>
      change Extract.hdrBlock (chainInput p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val _) = _
      rw [Extract.hdrBlock_wotsChainInput]
      rfl
  | leaf L =>
      simp only [cell]
      rw [Extract.hdrBlock_leafInput]
      rfl
  | node n =>
      simp only [cell]
      rw [Extract.hdrBlock_nodeInputP]
      rfl
  | wctChain p =>
      simp only [cell]
      rw [Extract.hdrBlock_wctChainInput]
      rfl
  | wctLeaf L =>
      simp only [cell]
      rw [Extract.hdrBlock_wctLeafInput]
      rfl
  | wctNode n =>
      simp only [cell]
      rw [Extract.hdrBlock_nodeInputP]
      rfl
  | forest index =>
      simp only [cell]
      rw [Extract.hdrBlock_forestInput]
      rfl
theorem cell_separated (secrets : Secrets) : Separated (cell secrets) := by
  intro left right hne before after heq
  have h1 := hdrBlock_cell secrets left before
  have h2 := hdrBlock_cell secrets right after
  rw [heq] at h1
  exact hne (toPos_injective (Extract.Pos.hdr_injective (toPos_bounded left) (toPos_bounded right)
    (bytesLE_injective (h1.symm.trans h2))))
theorem treeNodeAt_level {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {n : TreeNode}
    (h : treeNodeAt lay tree level c = some n) : n.1.level.val = level := by
  unfold treeNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem ftsNodeAt_level {index : Fin (2^31)} {coord : Fin 9} {level c : Nat} {n : WctNodePos}
    (h : ftsNodeAt index coord level c = some n) : n.1.level.val = level := by
  unfold ftsNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem treeLabel_congr (left right : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ other : Node, other.depth < 8 + level → left other = right other) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L =>
        simp only
        rw [h _ (by simp only [Node.depth]; omega)]
  · cases hn : treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        rw [h _ (by simp only [Node.depth]; rw [treeNodeAt_level hn]; omega)]
theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (h : ∀ other : Node, other.depth < 5 + level → left other = right other) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [h _ (by simp only [Node.depth]; omega)]
  · rfl
  · cases hn : ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        rw [h _ (by simp only [Node.depth]; rw [ftsNodeAt_level hn]; omega)]
theorem cell_congr (secrets : Secrets) (node : Node) (left right : Labels)
    (h : ∀ other : Node, other.depth < node.depth → left other = right other) :
    cell secrets node left = cell secrets node right := by
  cases node with
  | chain p =>
      change ChainGraph.input (seedsOf secrets) p (chainLabels left) =
        ChainGraph.input (seedsOf secrets) p (chainLabels right)
      unfold ChainGraph.input ChainGraph.prior
      split_ifs with hz
      · rfl
      · have hd := h (.chain (ChainGraph.predecessor p)) (by
          simp only [Node.depth, ChainGraph.predecessor]; omega)
        simp only [chainLabels, hd]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets left L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets right L.1) := by
        apply List.map_congr_left
        intro i _
        unfold endLabel ChainGraph.value
        split_ifs
        · rfl
        · simp only [chainLabels]
          rw [h _ (by simp only [Node.depth]; exact Nat.mod_lt _ (by decide))]
      simp only [cell, hends]
  | node n =>
      have hl := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hr := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      simp only [cell, hl, hr]
  | wctChain p =>
      have hv : wctValueL secrets left p.1 p.2.val = wctValueL secrets right p.1 p.2.val := by
        unfold wctValueL
        split_ifs with hz
        · rfl
        · rw [h _ (by simp only [Node.depth]; have := p.2.isLt; omega)]
      simp only [cell, hv]
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel left (L.index, L.coord, L.child, t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel right (L.index, L.coord, L.child, t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [h _ (by simp only [Node.depth]; decide)]
      simp only [cell, hends]
  | wctNode n =>
      have hl := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hr := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      simp only [cell, hl, hr]
  | forest index =>
      have hroots : ((List.range 9).map fun coord =>
            (ftsLabel left index (fin9 coord) 6 0, ftsLabel left index (fin9 coord) 6 1)) =
          ((List.range 9).map fun coord =>
            (ftsLabel right index (fin9 coord) 6 0, ftsLabel right index (fin9 coord) 6 1)) := by
        apply List.map_congr_left
        intro coord _
        rw [ftsLabel_congr left right index (fin9 coord) 6 0
            (fun other ho => h other (show other.depth < 11 by omega)),
          ftsLabel_congr left right index (fin9 coord) 6 1
            (fun other ho => h other (show other.depth < 11 by omega))]
      simp only [cell, hroots]
theorem posOf_cell (secrets : Secrets) (node : Node) (labels : Labels) :
    Extract.posOf (cell secrets node labels) = some node.toPos :=
  Extract.posOf_eq (toPos_bounded node) (hdrBlock_cell secrets node labels)
theorem cell_eq_of_posOf {input : HashInput} {node node' : Node} (secrets : Secrets) (labels : Labels)
    (hpos : Extract.posOf input = some node.toPos) (h : input = cell secrets node' labels) : node' = node := by
  subst h
  rw [posOf_cell] at hpos
  exact toPos_injective (Option.some.inj hpos)
theorem height_pos (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide
def rootNode : TreeNode :=
  ⟨⟨0, 0, ⟨height 0 - 1, by decide⟩, ⟨0, by decide⟩⟩, by decide⟩
def ftsTopNode (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) : WctNodePos :=
  ⟨⟨index, coord, ⟨5, by decide⟩, ⟨b.val, by have := b.isLt; omega⟩⟩, show b.val < 2 ^ (7 - 5 - 1) by
    have := b.isLt; omega⟩
theorem height_ge_two (lay : Layer) : 2 ≤ height lay := by fin_cases lay <;> decide
def topNode (lay : Layer) (tree : Fin (2^31)) (ht : tree.val < 2 ^ treeBits lay) (b : Fin 2) : TreeNode :=
  ⟨⟨lay, tree, ⟨height lay - 2, by have := SigGolfCandidate.T3M.Extract.height_le lay; omega⟩,
    ⟨b.val, by have := b.isLt; omega⟩⟩,
    ⟨show height lay - 2 < height lay by have := height_ge_two lay; omega, by
      have := height_ge_two lay
      show b.val < 2 ^ (height lay - (height lay - 2) - 1)
      rw [show height lay - (height lay - 2) - 1 = 1 by omega]
      have := b.isLt; omega, ht, Or.inr (by have := height_ge_two lay; show height lay - 2 + 1 < height lay; omega)⟩⟩
theorem treeLabel_top (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (ht : tree.val < 2 ^ treeBits lay)
    (b : Fin 2) :
    treeLabel labels lay tree (height lay - 1) b.val = (labels (.node (topNode lay tree ht b))).extractLsb' 0 128 := by
  have h2 := height_ge_two lay
  unfold treeLabel
  rw [if_neg (by omega)]
  have hv : height lay - 1 - 1 < height lay ∧ b.val < 2 ^ (height lay - (height lay - 1 - 1) - 1) ∧
      tree.val < 2 ^ treeBits lay ∧ (lay = 0 ∨ height lay - 1 - 1 + 1 < height lay) := by
    refine ⟨by omega, ?_, ht, Or.inr (by omega)⟩
    rw [show height lay - (height lay - 1 - 1) - 1 = 1 by omega]
    have := b.isLt; omega
  unfold treeNodeAt
  rw [dif_pos hv]
  have e : height lay - 1 - 1 = height lay - 2 := by omega
  simp only [e]
  rfl
theorem treeLabel_root (labels : Labels) :
    treeLabel labels 0 0 (height 0) 0 = (labels (.node rootNode)).extractLsb' 0 128 := by
  unfold treeLabel
  rw [if_neg (by decide)]
  unfold treeNodeAt
  rw [dif_pos (by decide)]
  rfl
theorem ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    ftsLabel labels index coord 6 b.val = (labels (.wctNode (ftsTopNode index coord b))).extractLsb' 0 128 := by
  unfold ftsLabel
  rw [if_neg (by omega)]
  unfold ftsNodeAt
  rw [dif_pos (show 6 - 1 < 6 ∧ b.val < 2 ^ (7 - (6 - 1) - 1) by have := b.isLt; omega)]
  rfl
noncomputable def canonInputs : Finset HashInput :=
  (Finset.univ : Finset (Secrets × Labels × Node)).image fun x => cell x.1 x.2.2 x.2.1
attribute [irreducible] canonInputs
theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels ∈ canonInputs := by
  rw [canonInputs]
  exact Finset.mem_image.mpr ⟨(secrets, labels, node), Finset.mem_univ _, rfl⟩
theorem cell_length_le (secrets : Secrets) (node : Node) (labels : Labels) :
    (cell secrets node labels).length ≤ 4096 := by
  cases node with
  | chain p =>
      change (ChainGraph.row p _).length ≤ 4096
      rw [ChainGraph.row_length]; omega
  | leaf L =>
      simp only [cell, Extract.leafInput]
      rw [Cost.pad64_length, SigGolfCandidate.T3.leafInput_length]
      have hc : chainCount L.1.lay ≤ 58 := chainCount_bound L.1.lay
      simp only [List.length_map, List.length_range]
      split_ifs <;> omega
  | node n =>
      simp only [cell]
      rw [pad64_nodeInputP, nodeInputP, block4]
      simp only [List.length_append, bytesLE_length]; omega
  | wctChain p =>
      simp only [cell, WCT9.chainInput, zero16, List.length_append, List.length_replicate, bytesLE_length]
      omega
  | wctLeaf L =>
      simp only [cell, Extract.wctLeafInput]
      rw [Cost.pad64_length, Extract.listInput_length']
      simp only [List.length_cons, List.length_drop, List.length_ofFn]
      omega
  | wctNode n =>
      simp only [cell]
      rw [pad64_nodeInputP, nodeInputP, block4]
      simp only [List.length_append, bytesLE_length]; omega
  | forest index =>
      simp only [cell, Extract.forestInput]
      rw [Cost.pad64_length, WCT9.forestInput_length _ _ (by simp)]
      omega
theorem canonInputs_subset_publicUniverse : canonInputs ⊆ SeccLaw.publicUniverse := by
  intro input hinput
  rw [canonInputs, Finset.mem_image] at hinput
  obtain ⟨x, -, rfl⟩ := hinput
  exact SeccLaw.mem_publicUniverse _ (cell_length_le _ _ _)
noncomputable def cellIn (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (node : Node) (labels : Labels) : U :=
  ⟨cell secrets node labels, hU (cell_mem secrets node labels)⟩
theorem cellIn_separated (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) :
    Separated (cellIn U hU secrets) := by
  intro left right hne before after heq
  exact cell_separated secrets left right hne before after (congrArg Subtype.val heq)
theorem cellIn_injective (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) (labels : Labels) :
    Function.Injective (fun node => cellIn U hU secrets node labels) := by
  intro left right heq
  by_contra hne
  exact cellIn_separated U hU secrets left right hne labels labels heq
noncomputable def order : List Node :=
  (Finset.univ : Finset Node).toList.mergeSort (fun left right => decide (left.depth ≤ right.depth))
attribute [irreducible] order
theorem order_nodup : order.Nodup := by
  unfold order
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
theorem mem_order (node : Node) : node ∈ order := by
  rw [order, List.mem_mergeSort]
  simp
theorem order_sorted : order.Pairwise (fun left right => left.depth ≤ right.depth) := by
  have h := List.pairwise_mergeSort
    (le := fun left right : Node => decide (left.depth ≤ right.depth))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp [Bool.or_eq_true]; omega)
    (Finset.univ : Finset Node).toList
  simpa only [order, decide_eq_true_eq] using h
def advance (node : Node) (output : HashOutput) (labels : Labels) : Labels := Function.update labels node output
noncomputable def graph (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (table : U → HashOutput) : Labels :=
  read (cellIn U hU secrets) advance table order (fun _ => 0)
noncomputable def programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => cellIn U hU secrets node labels) labels residual order
section Laws
variable (U : Finset HashInput) (hU : canonInputs ⊆ U)
noncomputable local instance instSampleableTypeHashOutput_canonGraph : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem programmed_at (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (node : Node) :
    programmed U hU secrets labels residual (cellIn U hU secrets node labels) = labels node :=
  patch_at _ (cellIn_injective U hU secrets labels) labels residual order node (mem_order node)
theorem programmed_other (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, query.val ≠ cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node _ heq
  exact hquery node (congrArg Subtype.val heq)
theorem read_eq_plant (secrets : Secrets) (nodes : List Node) (hnodup : nodes.Nodup) (before : Labels) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (read (cellIn U hU secrets) advance table nodes before, table)] =
      𝒮[plant (cellIn U hU secrets) advance nodes before] :=
  evalDist_read_eq_plant (cellIn U hU secrets) advance (cellIn_separated U hU secrets) nodes hnodup before
theorem replay_eq_programmed (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : Labels) (hagrees : ∀ node, node ∉ nodes → before node = labels node) :
    replay (cellIn U hU secrets) advance labels residual nodes before =
      (labels, patch (fun node => cellIn U hU secrets node labels) labels residual nodes) := by
  induction nodes generalizing before with
  | nil =>
      have hbefore : before = labels := funext fun node => hagrees node (by simp)
      rw [hbefore]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : cellIn U hU secrets first before = cellIn U hU secrets first labels := by
        apply Subtype.ext
        apply cell_congr
        intro other hother
        apply hagrees
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · rw [heq] at hother; omega
        · have := hdepth _ hmem; omega
      have hafter : ∀ node, node ∉ rest → advance first (labels first) before node = labels node := by
        intro node hnode
        unfold advance
        by_cases heq : node = first
        · subst node; rw [Function.update_self]
        · rw [Function.update_of_ne heq]
          exact hagrees node (fun hmem => (List.mem_cons.mp hmem).elim heq hnode)
      rw [replay, ih hsorted _ hafter, patch, hinput]
theorem plant_eq_uniform_programmed (secrets : Secrets) :
    𝒮[plant (cellIn U hU secrets) advance order (fun _ => 0)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] := by
  rw [evalDist_plant_eq_replay _ _ _ order_nodup]
  apply evalSPMF_bind_congr_left
  intro labels
  apply evalSPMF_bind_congr_left
  intro residual
  rw [replay_eq_programmed U hU secrets labels residual order order_sorted _
    (fun node hnode => (hnode (mem_order node)).elim)]
  rfl
theorem graph_eq_uniform_programmed (secrets : Secrets) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (graph U hU secrets table, table)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] :=
  (read_eq_plant U hU secrets order order_nodup _).trans (plant_eq_uniform_programmed U hU secrets)
theorem graph_bind_eq_uniform_programmed {Result : Type} (secrets : Secrets)
    (next : Labels → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (graph U hU secrets table) table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next labels (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
    law >>= fun result => 𝒮[next result.1 result.2]) (graph_eq_uniform_programmed U hU secrets)
  simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h
theorem uniform_bind_programmed {Result : Type} (secrets : Secrets) (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] :=
  graph_bind_eq_uniform_programmed U hU secrets (fun _ table => next table)
end Laws
def fullHalf (n : Nat) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩
/-- Half-cell of FTS coefficient `(index, coord, j)`: half `j % 2` of `ftsSeedPair index coord (j / 2)`. -/
def wctCoefCoordinate (c : WctCoef) : ChainGraph.HalfCoordinate :=
  (.inl (WCT9.ftsSeedHeader c.2.1.val c.1.val (c.2.2.val / 2)), fullHalf c.2.2.val)
/-- Half-cell of secret `a`: coefficient `chain < famCount layer` of a leaf is the packed half
`famOrdinal layer leaf chain` of `lowerSeedPair layer tree`; other addresses get distinct unused cells. -/
def seedCoordinateP (a : Address) : ChainGraph.HalfCoordinate :=
  if a.chain.val < WCT9.famCount a.layer then
    (.inl (WCT9.lowerSeedHeader a.layer a.tree.val (WCT9.famOrdinal a.layer a.leaf.val a.chain.val / 2)),
      fullHalf (WCT9.famOrdinal a.layer a.leaf.val a.chain.val))
  else (.inl (header 0 a.layer.val a.tree.val (a.chain.val / 2) (a.leaf.val + 1)), fullHalf a.chain.val)
def secretCoordinate : SecretIndex → ChainGraph.HalfCoordinate := Sum.elim seedCoordinateP wctCoefCoordinate
theorem fullHalf_val (n : Nat) : (fullHalf n).val = n % 2 := rfl
theorem famOrdinal_pair_lt' (a : Address) : WCT9.famOrdinal a.layer a.leaf.val a.chain.val / 2 < 2 ^ 32 := by
  have h1 := a.leaf.isLt; have h2 := a.chain.isLt
  have h3 := WCT9.famCount_le a.layer
  have : WCT9.famCount a.layer * a.leaf.val ≤ 24 * 4096 := Nat.mul_le_mul h3 (by omega)
  unfold WCT9.famOrdinal
  omega
theorem wctCoefCoordinate_injective : Function.Injective wctCoefCoordinate := by
  intro left right heq
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  simp only [wctCoefCoordinate, fullHalf_val, Sum.inl.injEq] at hp hh
  obtain ⟨⟨i, hi⟩, ⟨k, hk⟩, ⟨j, hj⟩⟩ := left
  obtain ⟨⟨i', hi'⟩, ⟨k', hk'⟩, ⟨j', hj'⟩⟩ := right
  simp only at hp hh
  obtain ⟨e1, e2, e3⟩ := WCT9.ftsSeedHeader_injective (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hp
  have e4 : j = j' := by omega
  subst e1 e2 e4
  rfl
theorem seedCoordinateP_injective : Function.Injective seedCoordinateP := by
  intro left right heq
  have hl := left.layer.isLt; have hr := right.layer.isLt
  have hlt := left.tree.isLt; have hrt := right.tree.isLt
  have hli := left.leaf.isLt; have hri := right.leaf.isLt
  have hlc := left.chain.isLt; have hrc := right.chain.isLt
  have pl := famOrdinal_pair_lt' left; have pr := famOrdinal_pair_lt' right
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  unfold seedCoordinateP at hp hh
  by_cases hc : left.chain.val < WCT9.famCount left.layer <;>
    by_cases hc' : right.chain.val < WCT9.famCount right.layer
  · rw [if_pos hc, if_pos hc'] at hp hh
    simp only [fullHalf_val, Sum.inl.injEq] at hp hh
    unfold WCT9.lowerSeedHeader at hp
    obtain ⟨-, e1, e2, e3, -⟩ := header_injective (by decide) (by omega) (by omega) pl (by omega)
      (by decide) (by omega) (by omega) pr (by omega) hp
    have elay : left.layer = right.layer := Fin.ext e1
    rw [elay] at e3 hh hc
    have eo : WCT9.famOrdinal right.layer left.leaf.val left.chain.val =
        WCT9.famOrdinal right.layer right.leaf.val right.chain.val := by omega
    obtain ⟨e4, e5⟩ := WCT9.famOrdinal_inj hc hc' eo
    exact ChainGraph.Address.ext elay (Fin.ext e2) (Fin.ext e4) (Fin.ext e5)
  · exfalso
    rw [if_pos hc, if_neg hc'] at hp
    simp only [Sum.inl.injEq, WCT9.lowerSeedHeader] at hp
    have := (header_injective (by decide) (by omega) (by omega) pl (by omega)
      (by decide) (by omega) (by omega) (by omega) (by omega) hp).2.2.2.2
    omega
  · exfalso
    rw [if_neg hc, if_pos hc'] at hp
    simp only [Sum.inl.injEq, WCT9.lowerSeedHeader] at hp
    have := (header_injective (by decide) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by omega) (by omega) pr (by omega) hp).2.2.2.2
    omega
  · rw [if_neg hc, if_neg hc'] at hp hh
    simp only [fullHalf_val, Sum.inl.injEq] at hp hh
    obtain ⟨-, e1, e2, e3, e4⟩ := header_injective (by decide) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by omega) (by omega) (by omega) (by omega) hp
    exact ChainGraph.Address.ext (Fin.ext e1) (Fin.ext e2) (Fin.ext (by omega)) (Fin.ext (by omega))
theorem seedCoordinateP_ne_wct (a : Address) (g : WctCoef) : seedCoordinateP a ≠ wctCoefCoordinate g := by
  intro heq
  have hp := congrArg Prod.fst heq
  unfold seedCoordinateP wctCoefCoordinate at hp
  split_ifs at hp
  · exact WCT9.ftsSeedHeader_ne_lowerSeedHeader _ _ _ _ _ _ (Sum.inl.inj hp).symm
  · exact WCT9.ftsSeedHeader_ne_tag _ _ _ 0 _ _ _ _ (by decide) (Sum.inl.inj hp).symm
theorem secretCoordinate_injective : Function.Injective secretCoordinate := by
  intro left right heq
  cases left with
  | inl a =>
      cases right with
      | inl b => exact congrArg Sum.inl (seedCoordinateP_injective heq)
      | inr g => exact (seedCoordinateP_ne_wct a g heq).elim
  | inr f =>
      cases right with
      | inl b => exact (seedCoordinateP_ne_wct b f heq.symm).elim
      | inr g => exact congrArg Sum.inr (wctCoefCoordinate_injective heq)
def privateSecrets (table : FullGame.FullTable) : Secrets := ChainGraph.halves table ∘ secretCoordinate
abbrev OtherHalf := {coordinate : ChainGraph.HalfCoordinate // coordinate ∉ Set.range secretCoordinate}
abbrev OtherHalves := OtherHalf → Digest
noncomputable def splitEquiv : ChainGraph.HalfTable ≃ Secrets × OtherHalves :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range secretCoordinate)).symm.trans
    ((Equiv.ofInjective secretCoordinate secretCoordinate_injective).symm.sumCongr (Equiv.refl OtherHalf)))
    (Equiv.refl Digest)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
theorem splitEquiv_fst (table : ChainGraph.HalfTable) : (splitEquiv table).1 = table ∘ secretCoordinate := by
  funext index
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]
noncomputable def privateEquiv : FullGame.FullTable ≃ Secrets × OtherHalves :=
  ChainGraph.halvesEquiv.trans splitEquiv
theorem privateEquiv_fst (table : FullGame.FullTable) : (privateEquiv table).1 = privateSecrets table :=
  splitEquiv_fst (ChainGraph.halves table)
theorem privateSecrets_symm (secrets : Secrets) (other : OtherHalves) :
    privateSecrets (privateEquiv.symm (secrets, other)) = secrets := by
  rw [← privateEquiv_fst, Equiv.apply_symm_apply]
def layerMsgEquiv : WCT9.LayerMsg ≃ Digest ⊕ (Digest × Digest) where
  toFun
    | .forest d => .inl d
    | .pair l r => .inr (l, r)
  invFun
    | .inl d => .forest d
    | .inr p => .pair p.1 p.2
  left_inv m := by cases m <;> rfl
  right_inv x := by rcases x with d | ⟨l, r⟩ <;> rfl
set_option warn.classDefReducibility false in
noncomputable def layerMsgFintype : Fintype WCT9.LayerMsg := Fintype.ofEquiv _ layerMsgEquiv.symm
attribute [irreducible] layerMsgFintype
abbrev EncKey := (Layer × Fin (2^31) × Fin 4096 × WCT9.LayerMsg) × Fin (2^22)
def encQuery (key : EncKey) : HashInput :=
  pad64 (WCT9.layerEncodingInput key.1.1 key.1.2.1.val key.1.2.2.1.val key.1.2.2.2 (BitVec.ofNat 32 key.2.val))
set_option warn.classDefReducibility false in
noncomputable def encodingKeyFintype : Fintype EncKey :=
  @instFintypeProd _ _ (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance layerMsgFintype))) inferInstance
attribute [irreducible] encodingKeyFintype
noncomputable def encInputs : Finset HashInput :=
  (@Finset.univ _ encodingKeyFintype).image encQuery
attribute [irreducible] encInputs
theorem encQuery_mem (key : EncKey) : encQuery key ∈ encInputs := by
  rw [encInputs]
  exact Finset.mem_image_of_mem _ (@Finset.mem_univ _ encodingKeyFintype key)
theorem encQuery_length (key : EncKey) : (encQuery key).length = 64 := by
  obtain ⟨⟨lay, tree, leaf, msg⟩, c⟩ := key
  cases msg <;> simp [encQuery, WCT9.layerEncodingInput, encodingInput, WCT9.pairEncodingInputP, pad64,
    bytesLE_length]
theorem encInputs_subset_publicUniverse : encInputs ⊆ SeccLaw.publicUniverse := by
  intro input hinput
  rw [encInputs, Finset.mem_image] at hinput
  obtain ⟨key, -, rfl⟩ := hinput
  apply SeccLaw.mem_publicUniverse
  rw [encQuery_length]
  unfold SeccLaw.maxInputLength
  omega
section PrivateLaws
noncomputable local instance instFintypeCoordinate_canonGraph : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_canonGraph : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeHashOutput_canonGraph_1 : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels_1 : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeOtherHalves : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance instFintypeSecrets_canonGraph : Fintype Secrets := inferInstance
noncomputable local instance instFintypeOtherHalves_canonGraph : Fintype OtherHalves := inferInstance
noncomputable local instance instSampleableTypeProdSecretsOtherHalves : SampleableType (Secrets × OtherHalves) :=
  @SampleableType.ofFintype _ (instFintypeProd Secrets OtherHalves) _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem uniform_private_split :
    𝒮[privateEquiv <$> ($ᵗ FullGame.FullTable : ProbComp _)] =
      𝒮[do let secrets ← ($ᵗ Secrets : ProbComp _); let other ← ($ᵗ OtherHalves : ProbComp _); pure (secrets, other)] :=
  (evalSPMF_map_bijective_uniform_cross (α := FullGame.FullTable) (β := Secrets × OtherHalves)
    privateEquiv privateEquiv.bijective).trans (FullGame.uniform_product (A := Secrets) (B := OtherHalves)).symm
theorem private_bind {Result : Type} (next : FullGame.FullTable → ProbComp Result) :
    𝒮[do let table ← ($ᵗ FullGame.FullTable : ProbComp _); next table] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        next (privateEquiv.symm (secrets, other))] := by
  have h := congrArg (fun law : SPMF (Secrets × OtherHalves) =>
    law >>= fun result => 𝒮[next (privateEquiv.symm result)]) uniform_private_split
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply] using h
theorem tables_bind {Result : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (privateEquiv.symm (secrets, other)) (programmed U hU secrets labels residual)] := by
  rw [private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)]
  apply evalSPMF_bind_congr_left
  intro secrets
  apply evalSPMF_bind_congr_left
  intro other
  exact uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)
abbrev LowLabels := Node → Digest
noncomputable def labelPairEquiv : Labels ≃ LowLabels × LowLabels :=
  (Equiv.arrowCongr (Equiv.refl Node) ChainGraph.outputEquiv).trans
    (Equiv.arrowProdEquivProdArrow Node (fun _ => Digest) (fun _ => Digest))
noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => ChainGraph.joinOutput (low node) (high node)
theorem labelPairEquiv_symm (low high : LowLabels) : labelPairEquiv.symm (low, high) = joinLabels low high := rfl
theorem joinLabels_low (low high : LowLabels) (node : Node) :
    (joinLabels low high node).extractLsb' 0 128 = low node := ChainGraph.joinOutput_low _ _
noncomputable local instance instSampleableTypeLowLabels : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdLowLabels : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _
theorem labels_bind {Result : Type} (next : Labels → ProbComp Result) :
    𝒮[do let labels ← ($ᵗ Labels : ProbComp _); next labels] =
      𝒮[do
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        next (joinLabels low high)] := by
  have hpair : 𝒮[labelPairEquiv <$> ($ᵗ Labels : ProbComp _)] =
      𝒮[do let low ← ($ᵗ LowLabels : ProbComp _); let high ← ($ᵗ LowLabels : ProbComp _); pure (low, high)] :=
    (evalSPMF_map_bijective_uniform_cross (α := Labels) (β := LowLabels × LowLabels)
      labelPairEquiv labelPairEquiv.bijective).trans (FullGame.uniform_product (A := LowLabels) (B := LowLabels)).symm
  have h := congrArg (fun law : SPMF (LowLabels × LowLabels) =>
    law >>= fun result => 𝒮[next (labelPairEquiv.symm result)]) hpair
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply, labelPairEquiv_symm] using h
end PrivateLaws
noncomputable def eagerAnswers (privateTable : FullGame.FullTable) (U : Finset HashInput)
    (publicTable : U → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => finiteHashAnswer ∅ U publicTable input
  | .inr coordinate => privateTable coordinate
def halfAnswer (answers : Answers) (c : ChainGraph.HalfCoordinate) : Digest :=
  if c.2.val = 0 then (answers (.inr c.1)).extractLsb' 0 128 else (answers (.inr c.1)).extractLsb' 128 128
def secretsOf (answers : Answers) : Secrets := fun idx => halfAnswer answers (secretCoordinate idx)
def wctSeedOf (answers : Answers) (a : WctAddr) : Digest := wctSeedsOf (secretsOf answers) a
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
theorem halfAnswer_pair (answers : Answers) (tag lay tree position index : Nat) (i : Fin 2) :
    halfAnswer answers (.inl (header tag lay tree position index), i) =
      if i.val = 0 then (evalWithAnswerFn answers (privatePair tag lay tree position index)).1
      else (evalWithAnswerFn answers (privatePair tag lay tree position index)).2 := rfl
theorem secretsOf_coef (answers : Answers) (c : WctCoef) :
    secretsOf answers (.inr c) = WCT9.ftsCoef answers c.1.val c.2.1.val c.2.2 := by
  change halfAnswer answers (wctCoefCoordinate c) = _
  unfold wctCoefCoordinate WCT9.ftsCoef WCT9.seedHalf WCT9.ftsSeedHeader WCT9.ftsSeedPair
  rw [halfAnswer_pair, fullHalf_val]
theorem wctFamily_secretsOf (answers : Answers) (index : Fin (2 ^ 31)) (coord : Fin 9) :
    wctFamily (secretsOf answers) index coord = WCT9.ftsCoef answers index.val coord.val :=
  funext fun j => secretsOf_coef answers (index, coord, j)
theorem secretsOf_wct (answers : Answers) (a : WctAddr) :
    wctSeedsOf (secretsOf answers) a = WCT9.seed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2 := by
  unfold wctSeedsOf WCT9.seed
  rw [wctFamily_secretsOf]
/-- A coefficient secret is the packed half `famCoefN` the signer reads (stage B lower, T8D top). -/
theorem secretsOf_fam (answers : Answers) (a : Address) (hc : a.chain.val < WCT9.famCount a.layer) :
    secretsOf answers (.inl a) = WCT9.famCoefN answers a.layer a.tree.val a.leaf.val a.chain.val := by
  change halfAnswer answers (seedCoordinateP a) = _
  unfold seedCoordinateP WCT9.famCoefN WCT9.seedHalf WCT9.lowerSeedHeader WCT9.lowerSeedPair
  rw [if_pos hc, halfAnswer_pair, fullHalf_val]
theorem leafFamily_secretsOf (answers : Answers) (lay : Layer) (tree : Fin (2 ^ 31)) (leaf : Fin 4096) :
    leafFamily (secretsOf answers) lay tree leaf = WCT9.famCoef answers lay tree.val leaf.val :=
  funext fun j => secretsOf_fam answers ⟨lay, tree, leaf, ⟨j.val, lt_trans j.isLt (famCount_lt_58 lay)⟩⟩ j.isLt
theorem seedsOf_secretsOf (answers : Answers) (a : Address) :
    seedsOf (secretsOf answers) a = WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val := by
  unfold seedsOf
  rw [leafFamily_secretsOf answers, WCT9.wotsSeed_fam]
end ClaudeWCT.W9.T3.Security.CanonGraph
