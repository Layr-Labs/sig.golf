import SigGolfCandidate.T3_Secc_SeccLaw
import SigGolfCandidate.T3_Secc_WotsEvents
import SigGolfCandidate.ClaudeWCT_W9_T3M_Extract_Header
import SigGolfCandidate.ClaudeWCT_WCT9_FamLayout

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
/-- A tree node. Top-nonce layer (r3-lean-nonsec): `nonce` indexes the keygen nonce trials of a top node (rejection
sampling cell); every other position uses only `nonce = 0`, and every other `(position, nonce)` is a phantom node
(a 192-byte cell outside every position). -/
structure TreeNodeRaw where
  lay : Layer
  tree : Fin (2^31)
  level : Fin 12
  idx : Fin 2048
  nonce : Fin 212992
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
  | .node n => 8 + n.1.level.val * 2 ^ 18 + n.1.nonce.val
  | .wctChain p => p.2.val
  | .wctLeaf L => 4 + 7 * L.coord.val
  | .wctNode n => 5 + 7 * n.1.coord.val + n.1.level.val
  | .forest _ => 70
/-- Coefficient index of the FTS seed families (campaign X1, stage A): `(index, coord, j)`, `j < 54`. -/
abbrev WctCoef := Fin (2 ^ 31) × Fin 9 × Fin 54
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
/-- The family of a leaf, as an address slot (secret coefficient `j` of family `f` sits at address
`(lay, tree, f, j)`; today one family per leaf, `famOf_today`). -/
def famSlot (lay : Layer) (leaf : Fin 4096) : Fin 4096 :=
  ⟨WCT9.famOf lay leaf.val, WCT9.famOf_lt leaf.isLt⟩
/-- Packed ordinal of coefficient `j` of family `f` (`famOrdinal lay leaf j = famOrd lay (famOf lay leaf) j`). -/
def famOrd (lay : Layer) (f j : Nat) : Nat := WCT9.famBase lay * f + j
theorem famOrdinal_eq (lay : Layer) (leaf j : Nat) :
    WCT9.famOrdinal lay leaf j = famOrd lay (WCT9.famOf lay leaf) j := rfl
/-- The coefficient family of leaf `(lay, tree, leaf)`: the secrets `(lay, tree, famOf leaf, j)`, `j < famSize`. -/
def leafFamily (secrets : Secrets) (lay : Layer) (tree : Fin (2 ^ 31)) (leaf : Fin 4096) :
    Fin (WCT9.famSize lay (WCT9.famOf lay leaf.val)) → Digest :=
  fun j => secrets (.inl ⟨lay, tree, famSlot lay leaf, ⟨j.val, lt_trans j.isLt (WCT9.famSize_lt_58 lay _)⟩⟩)
/-- WOTS seeds: the leaf family at `famPoint layer leaf chain` (every layer). -/
def seedsOf (secrets : Secrets) : Seeds := fun a =>
  ClaudeWCT.Arith.familyEval (List.ofFn (leafFamily secrets a.layer a.tree a.leaf))
    (WCT9.famPoint a.layer a.leaf.val a.chain.val)
/-- The coefficient family of FTS coordinate `(index, coord)`. -/
def wctFamily (secrets : Secrets) (index : Fin (2 ^ 31)) (coord : Fin 9) : Fin 54 → Digest :=
  fun j => secrets (.inr (index, coord, j))
/-- FTS seed of chain `a`: its family evaluated at `ftsPoint child chain` in GF(2^128). -/
def wctSeedsOf (secrets : Secrets) : WctAddr → Digest := fun a =>
  ClaudeWCT.Arith.familyEval (List.ofFn (wctFamily secrets a.1 a.2.1)) (WCT9.ftsPoint a.2.2.1.val a.2.2.2.val)
def chainLabels (labels : Labels) : ChainGraph.Labels := fun point => labels (.chain point)
/-! ### Pairing stage 1: chain rows of the current scheme

A chain point's cell is `WCT9.chainInputW` (F rows `0 | hdr | 0 | v`, G rows `v | hdr | 0 | 0`), and its input value
is the half `chainHigh` of the previous step's label (the HIGH half for steps `0..5` of a G chain). -/
def rowW (point : Point) (value : Digest) : HashInput :=
  WCT9.chainInputW point.1.layer point.1.tree.val point.1.leaf.val point.1.chain.val point.2.val value
theorem rowW_length (point : Point) (value : Digest) : (rowW point value).length = 64 :=
  WCT9.chainInputW_length _ _ _ _ _ _
theorem rowW_pad64 (point : Point) (value : Digest) : pad64 (rowW point value) = rowW point value :=
  WCT9.chainInputW_padded _ _ _ _ _ _
/-- The half of step `m`'s output that chain `address` reads. -/
def stepHigh (address : Address) (m : Nat) : Bool := WCT9.chainHigh address.layer address.chain.val m
def priorW (seeds : Seeds) (point : Point) (labels : ChainGraph.Labels) : Digest :=
  if point.2.val = 0 then seeds point.1
  else WCT9.halfOf (stepHigh point.1 (point.2.val - 1)) (labels (ChainGraph.predecessor point))
def inputW (seeds : Seeds) (point : Point) (labels : ChainGraph.Labels) : HashInput :=
  rowW point (priorW seeds point labels)
def valueW (seeds : Seeds) (labels : ChainGraph.Labels) (address : Address) (step : Nat) : Digest :=
  if step = 0 then seeds address
  else WCT9.halfOf (stepHigh address (step - 1)) (labels (address, ⟨(step - 1) % 7, Nat.mod_lt _ (by decide)⟩))
theorem valueW_zero (seeds : Seeds) (labels : ChainGraph.Labels) (address : Address) :
    valueW seeds labels address 0 = seeds address := by simp [valueW]
theorem valueW_succ (seeds : Seeds) (labels : ChainGraph.Labels) (address : Address) (step : Fin 7) :
    valueW seeds labels address (step.val + 1) = WCT9.halfOf (stepHigh address step.val) (labels (address, step)) := by
  simp [valueW, Nat.mod_eq_of_lt step.isLt]
theorem priorW_eq_valueW (seeds : Seeds) (labels : ChainGraph.Labels) (point : Point) :
    priorW seeds point labels = valueW seeds labels point.1 point.2.val := by
  have hmod : (point.2.val - 1) % 7 = point.2.val - 1 := Nat.mod_eq_of_lt (by have := point.2.isLt; omega)
  simp only [priorW, valueW, ChainGraph.predecessor, hmod]
def AgreesW (answers : Answers) (seeds : Seeds) (labels : ChainGraph.Labels) : Prop :=
  ∀ point, answers (.inl (.inr (inputW seeds point labels))) = labels point
theorem sourceW_step (answers : Answers) (seeds : Seeds) (labels : ChainGraph.Labels) (h : AgreesW answers seeds labels)
    (address : Address) (step : Fin 7) :
    evalWithAnswerFn answers (WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val
      step.val 1 (valueW seeds labels address step.val)) = valueW seeds labels address (step.val + 1) := by
  have hin : inputW seeds (address, step) labels = rowW (address, step) (valueW seeds labels address step.val) := by
    rw [inputW, priorW_eq_valueW]
  have hh := h (address, step)
  rw [hin] at hh
  have hc : WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val step.val 1
      (valueW seeds labels address step.val) =
        WCT9.halfHash (stepHigh address step.val) (rowW (address, step) (valueW seeds labels address step.val)) := by
    simp [WCT9.chainW, List.range'_succ, rowW, stepHigh]
  rw [hc, valueW_succ]
  cases hs : stepHigh address step.val
  · change WCT9.halfOf false (answers (.inl (.inr (pad64 (rowW (address, step) _))))) = _
    rw [rowW_pad64, hh]
  · change WCT9.halfOf true (answers (.inl (.inr (pad64 (rowW (address, step) _))))) = _
    rw [rowW_pad64, hh]
theorem sourceW_chain (answers : Answers) (seeds : Seeds) (labels : ChainGraph.Labels) (h : AgreesW answers seeds labels)
    (address : Address) (start count : Nat) (hbound : start + count ≤ 7) :
    evalWithAnswerFn answers (WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val
      start count (valueW seeds labels address start)) = valueW seeds labels address (start + count) := by
  induction count with
  | zero => simp [WCT9.chainW]
  | succ count ih =>
      rw [show start + (count + 1) = start + count + 1 by omega]
      have hadd : WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val start (count + 1)
          (valueW seeds labels address start) =
          (WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val start count
            (valueW seeds labels address start) >>=
            WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val (start + count) 1) := by
        unfold WCT9.chainW
        rw [← List.range'_append_1, List.foldlM_append]
      rw [hadd, evalWithAnswerFn_bind, ih (by omega)]
      exact sourceW_step answers seeds labels h address ⟨start + count, by omega⟩
def fin58 (i : Nat) : Fin 58 := ⟨i % 58, Nat.mod_lt _ (by decide)⟩
def fin9 (i : Nat) : Fin 9 := ⟨i % 9, Nat.mod_lt _ (by decide)⟩
def Node.toPos : Node → Extract.Pos
  | .chain p => .chain p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val
  | .leaf L => .leaf L.1.lay L.1.tree.val L.1.leaf.val
  | .node n => .node n.1.lay n.1.tree.val n.1.level.val n.1.idx.val
  | .wctChain p => .wctChain p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
  | .wctLeaf L => .wctLeaf L.index.val L.coord.val L.child.val
  | .wctNode n => .wctNode n.1.index.val n.1.coord.val n.1.level.val n.1.idx.val
  | .forest index => .forest index.val
/-- The last chain point of chain `i` of leaf `L` (step `maxDigit - 1`). -/
def endPt (L : LeafPos) (i : Nat) : Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)
/-- The chain end the leaf reads: the used half (`Pos.proj`) of the last step's label (C3: the high half for chain
0 of a lower layer). -/
def endLabel (_secrets : Secrets) (labels : Labels) (L : LeafPos) (i : Nat) : Digest :=
  (Node.chain (endPt L i)).toPos.proj (labels (.chain (endPt L i)))
def wctValueL (secrets : Secrets) (labels : Labels) (a : WctAddr) (s : Nat) : Digest :=
  if s = 0 then wctSeedsOf secrets a
  else projHalf (WCT9.ftsChainHigh a.2.2.2.val ((s - 1) % 4))
    (labels (.wctChain (a, ⟨(s - 1) % 4, Nat.mod_lt _ (by decide)⟩)))
def wctEndLabel (labels : Labels) (a : WctAddr) : Digest := (labels (.wctChain (a, 3))).extractLsb' 0 128
/-- The chain end (campaign T8: position 4; the name is kept from the 3-step code). -/
theorem wctValueL_three (secrets : Secrets) (labels : Labels) (a : WctAddr) :
    wctValueL secrets labels a 4 = wctEndLabel labels a := by
  unfold wctValueL wctEndLabel
  rw [if_neg (by decide)]
  show projHalf (WCT9.ftsChainHigh a.2.2.2.val 3) (labels (.wctChain (a, 3))) = _
  rw [WCT9.ftsChainHigh_three]
  rfl
def treeNodeAt (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option TreeNode :=
  if h : level < height lay ∧ c < 2 ^ (height lay - level - 1) ∧ tree.val < 2 ^ treeBits lay ∧
      (lay = 0 ∨ level + 1 < height lay) then
    some ⟨⟨lay, tree, ⟨level, lt_of_lt_of_le h.1 (SigGolfCandidate.T3M.Extract.height_le lay)⟩,
      ⟨c, lt_of_lt_of_le h.2.1 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := SigGolfCandidate.T3M.Extract.height_le lay; omega)
          _ = 2048 := by norm_num)⟩, 0⟩, h⟩
  else none
theorem height_le_12 (lay : Layer) : 2 ^ height lay ≤ 4096 :=
  (Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)).trans (by norm_num)
def leafAt (lay : Layer) (tree : Fin (2^31)) (c : Nat) : Option SrcLeaf :=
  if h : c < 2 ^ height lay ∧ tree.val < 2 ^ treeBits lay then
    some ⟨⟨lay, tree, ⟨c, lt_of_lt_of_le h.1 (height_le_12 lay)⟩⟩, ⟨h.2, h.1⟩⟩
  else none
/-! ### Top-nonce layer: rejection-sampling cells (r3-lean-nonsec)
The nodes `(position, nonce)` of a top node at children level `level < 11` are its keygen nonce trials. With labels
`L`, trial `k` *fails* when the used half of its label misses the zero test; it is *active* when it is inside the cap
and every earlier trial failed. The selected trial `sel` is the first passing one (the last one when none passes),
and the tree value of the position is the used half of the selected trial's label. Every other position has only the
active trial `nonce = 0`. -/
/-- Trials of position `(lay, level)`: `cap_(level+1) = 104 · 2^(level+1)` on the top tree below the root, else 1. -/
def trialCap (lay : Layer) (level : Nat) : Nat := if lay = 0 ∧ level < 11 then topNonceCap (level + 1) else 1
theorem trialCap_pos (lay : Layer) (level : Nat) : 0 < trialCap lay level := by
  unfold trialCap topNonceCap; split_ifs <;> positivity
theorem trialCap_le (lay : Layer) (level : Nat) : trialCap lay level ≤ 212992 := by
  unfold trialCap topNonceCap topZeroBits topZeroAlloc
  split_ifs with h
  · obtain ⟨-, hl⟩ := h
    interval_cases level <;> simp
  · omega
/-- The trial `j` of the position of `n` (nonce `j % 212992`). -/
def withNonce (n : TreeNode) (j : Nat) : TreeNode :=
  ⟨{ n.1 with nonce := ⟨j % 212992, Nat.mod_lt _ (by decide)⟩ }, n.2⟩
theorem withNonce_nonce (n : TreeNode) {j : Nat} (hj : j < 212992) : (withNonce n j).1.nonce.val = j := by
  simp [withNonce, Nat.mod_eq_of_lt hj]
@[simp] theorem withNonce_lay (n : TreeNode) (j : Nat) : (withNonce n j).1.lay = n.1.lay := rfl
@[simp] theorem withNonce_tree (n : TreeNode) (j : Nat) : (withNonce n j).1.tree = n.1.tree := rfl
@[simp] theorem withNonce_level (n : TreeNode) (j : Nat) : (withNonce n j).1.level = n.1.level := rfl
@[simp] theorem withNonce_idx (n : TreeNode) (j : Nat) : (withNonce n j).1.idx = n.1.idx := rfl
theorem withNonce_withNonce (n : TreeNode) (i j : Nat) : withNonce (withNonce n i) j = withNonce n j := rfl
theorem withNonce_self (n : TreeNode) : withNonce n n.1.nonce.val = n := by
  obtain ⟨⟨lay, tree, level, idx, nonce⟩, hv⟩ := n
  simp [withNonce, Nat.mod_eq_of_lt nonce.isLt]
/-- Trial `j` of the position of `n` fails the zero test of height `level + 1`. -/
def trialFails (labels : Labels) (n : TreeNode) (j : Nat) : Prop :=
  topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj (labels (.node (withNonce n j)))) = false
instance (labels : Labels) (n : TreeNode) (j : Nat) : Decidable (trialFails labels n j) := by
  unfold trialFails; infer_instance
/-- Node `n` is an active trial: inside the cap, and every earlier trial of its position failed. -/
def Active (labels : Labels) (n : TreeNode) : Prop :=
  n.1.nonce.val < trialCap n.1.lay n.1.level.val ∧ ∀ j < n.1.nonce.val, trialFails labels n j
instance (labels : Labels) (n : TreeNode) : Decidable (Active labels n) := by unfold Active; infer_instance
/-- The selected nonce of the position of `n`: the first passing trial, the last trial when none passes. -/
def selNonce (labels : Labels) (n : TreeNode) : Nat :=
  ((List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFails labels n j)).getD
    (trialCap n.1.lay n.1.level.val - 1)
/-- The selected trial of the position of `n`. -/
def selNode (labels : Labels) (n : TreeNode) : TreeNode := withNonce n (selNonce labels n)
/-- The 192-byte phantom cell of an inactive node: unique per node, no position (`posOf = none`). -/
def phantomCode (n : TreeNode) : Nat :=
  n.1.lay.val + 4 * (n.1.level.val + 12 * (n.1.idx.val + 2048 * (n.1.nonce.val + 212992 * n.1.tree.val)))
def phantom (n : TreeNode) : HashInput :=
  List.replicate 16 255 ++ bytesLE 16 (BitVec.ofNat 128 (phantomCode n)) ++ List.replicate 160 0
def treeLabel (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  if level = 0 then
    (match leafAt lay tree c with
     | some L => (Node.leaf L).toPos.proj (labels (.leaf L))
     | none => 0)
  else
    match treeNodeAt lay tree (level - 1) c with
    | some n => (Node.node n).toPos.proj (labels (.node (selNode labels n)))
    | none => 0
def ftsNodeAt (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Option WctNodePos :=
  if h : level < 6 ∧ c < 2 ^ (7 - level - 1) then
    some ⟨⟨index, coord, ⟨level, h.1⟩, ⟨c, lt_of_lt_of_le h.2 (by
      calc 2 ^ (7 - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 64 := by norm_num)⟩⟩, h.2⟩
  else none
/-- FTS tree value from labels. The top values (level 6, nested FTS r1-1) are the high half of their label. -/
def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 128 then (labels (.wctLeaf ⟨index, coord, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match ftsNodeAt index coord (level - 1) c with
    | some n => if level = 6 then (labels (.wctNode n)).extractLsb' 128 128 else (labels (.wctNode n)).extractLsb' 0 128
    | none => 0
/-- Pads of coordinate `coord` (nested FTS r1-1): the previous coordinate's top pair, `(0, 0)` for coordinate 0. -/
def ftsPrevLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) : Digest × Digest :=
  if h : coord.val = 0 then (0, 0) else
    (ftsLabel labels index ⟨coord.val - 1, by omega⟩ 6 0, ftsLabel labels index ⟨coord.val - 1, by omega⟩ 6 1)
def cell (secrets : Secrets) : Node → Labels → HashInput
  | .chain p, labels => inputW (seedsOf secrets) p (chainLabels labels)
  | .leaf L, labels => pad64 (Extract.leafInput L.1.lay L.1.tree.val L.1.leaf.val
      ((List.range (chainCount L.1.lay)).map (endLabel secrets labels L.1)))
  | .node n, labels => if Active labels n then pad64 (WCT9.merkleNodeInputN n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val) n.1.nonce.val
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val))
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1))) else phantom n
  | .wctChain p, labels => WCT9.ftsChainInputW p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
      (wctValueL secrets labels p.1 p.2.val)
  | .wctLeaf L, labels => pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
      (ftsPrevLabel labels L.index L.coord).1
      (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t)))
  | .wctNode n, labels => pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2 ^ (7 - n.1.level.val - 1) + n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val))
      (if n.1.level.val = 5 then (ftsPrevLabel labels n.1.index n.1.coord).2 else 0)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)))
  | .forest index, labels => pad64 (Extract.forestInput index.val
      ((List.range 9).map fun coord => (ftsLabel labels index (fin9 coord) 6 0, ftsLabel labels index (fin9 coord) 6 1)))
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
/-- The position representative of a node (top-nonce layer: the trial index set to 0). -/
def Node.base : Node → Node
  | .node n => .node (withNonce n 0)
  | x => x
theorem toPos_base (node : Node) : node.base.toPos = node.toPos := by
  cases node <;> rfl
/-- `toPos` is injective up to the trial index (`Node.base`). -/
theorem toPos_injective_base {left right : Node} (h : left.toPos = right.toPos) : left.base = right.base := by
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
      obtain ⟨⟨lay, tree, level, idx, k⟩, hn⟩ := n
      obtain ⟨⟨lay', tree', level', idx', k'⟩, hm⟩ := m
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
      exact ⟨.node ⟨⟨lay, ⟨tree, lt_of_lt_of_le h1 (treeBits_lt lay)⟩, ⟨level, hl⟩, ⟨nd, hn⟩, 0⟩, h2, h3, h1, h4⟩, rfl⟩
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
theorem merkleNodeInput_length (lay tree heap : Nat) (left right : Digest) :
    (WCT9.merkleNodeInput lay tree heap left right).length = 64 := by
  simp only [WCT9.merkleNodeInput, zero16, List.length_append, List.length_replicate, bytesLE_length]
theorem pad64_merkleNodeInput (lay tree heap : Nat) (left right : Digest) :
    pad64 (WCT9.merkleNodeInput lay tree heap left right) = WCT9.merkleNodeInput lay tree heap left right := by
  unfold pad64; rw [merkleNodeInput_length]; simp
/-- Top-nonce layer: the cell of `node` is a phantom (an inactive tree node). -/
def PhantomAt (node : Node) (labels : Labels) : Prop := ∃ n, node = .node n ∧ ¬ Active labels n
theorem phantomCode_lt (n : TreeNode) : phantomCode n < 2 ^ 128 := by
  unfold phantomCode
  have := n.1.lay.isLt; have := n.1.level.isLt; have := n.1.idx.isLt; have := n.1.nonce.isLt; have := n.1.tree.isLt
  have h1 : n.1.lay.val + 4 * (n.1.level.val + 12 * (n.1.idx.val + 2048 * (n.1.nonce.val + 212992 * n.1.tree.val)))
      < 4 * 12 * 2048 * 212992 * 2 ^ 31 := by nlinarith
  calc _ < 4 * 12 * 2048 * 212992 * 2 ^ 31 := h1
    _ ≤ 2 ^ 128 := by norm_num
theorem phantomCode_injective : Function.Injective phantomCode := by
  intro a b h
  obtain ⟨⟨lay, tree, level, idx, k⟩, ha⟩ := a
  obtain ⟨⟨lay', tree', level', idx', k'⟩, hb⟩ := b
  unfold phantomCode at h
  simp only at h
  have := lay.isLt; have := lay'.isLt; have := level.isLt; have := level'.isLt; have := idx.isLt
  have := idx'.isLt; have := k.isLt; have := k'.isLt
  have e1 : lay.val = lay'.val := by omega
  have e2 : level.val = level'.val := by omega
  have e3 : idx.val = idx'.val := by omega
  have e4 : k.val = k'.val := by omega
  have e5 : tree.val = tree'.val := by omega
  have f1 := Fin.ext e1; have f2 := Fin.ext e2; have f3 := Fin.ext e3; have f4 := Fin.ext e4; have f5 := Fin.ext e5
  subst f1 f2 f3 f4 f5
  rfl
theorem phantom_length (n : TreeNode) : (phantom n).length = 192 := by
  simp [phantom, bytesLE_length]
theorem phantom_injective : Function.Injective phantom := by
  intro a b h
  unfold phantom at h
  have h1 := List.append_cancel_left (List.append_cancel_right h)
  have h2 := congrArg BitVec.toNat (bytesLE_injective h1)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (phantomCode_lt a),
    Nat.mod_eq_of_lt (phantomCode_lt b)] at h2
  exact phantomCode_injective h2
theorem Pos.len_ne_192 (p : Extract.Pos) : p.len ≠ 192 := by
  cases p <;> simp only [Extract.Pos.len] <;> (try split_ifs) <;> omega
theorem posOf_phantom (n : TreeNode) : Extract.posOf (phantom n) = none :=
  Extract.posOf_eq_none fun p _ hl _ => Pos.len_ne_192 p (by rw [← hl, phantom_length])
theorem cell_node_active {secrets : Secrets} {n : TreeNode} {labels : Labels} (h : Active labels n) :
    cell secrets (.node n) labels = pad64 (WCT9.merkleNodeInputN n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val) n.1.nonce.val
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val))
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1))) := by
  simp only [cell, if_pos h]
theorem cell_node_inactive {secrets : Secrets} {n : TreeNode} {labels : Labels} (h : ¬ Active labels n) :
    cell secrets (.node n) labels = phantom n := by
  simp only [cell, if_neg h]
theorem cell_of_phantomAt {secrets : Secrets} {node : Node} {labels : Labels} (h : PhantomAt node labels) :
    ∃ n, node = .node n ∧ cell secrets node labels = phantom n := by
  obtain ⟨n, rfl, hn⟩ := h
  exact ⟨n, rfl, cell_node_inactive hn⟩
theorem not_phantomAt_node {n : TreeNode} {labels : Labels} (h : Active labels n) : ¬ PhantomAt (.node n) labels := by
  rintro ⟨m, hm, hn⟩
  cases hm
  exact hn h
/-- Every non-phantom cell has its position's honest length (length-aware decoding, C3). -/
theorem cell_length (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    (cell secrets node labels).length = node.toPos.len := by
  cases node with
  | chain p =>
      change (rowW p _).length = _
      rw [rowW_length]; rfl
  | leaf L =>
      simp only [cell, Extract.leafInput, Node.toPos, Extract.Pos.len]
      rw [Cost.pad64_length, SigGolfCandidate.T3.leafInput_length]
      simp only [List.length_map, List.length_range]
      by_cases h0 : L.1.lay = 0
      · rw [if_pos h0, if_pos h0, h0]; decide
      · rw [if_neg h0, if_neg h0, chainCount_lower h0]
  | node n =>
      have ha : Active labels n := by
        by_contra ha; exact hp ⟨n, rfl, ha⟩
      rw [cell_node_active ha]
      simp only [Node.toPos, Extract.Pos.len]
      rw [WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]
  | wctChain p =>
      simp only [cell, WCT9.ftsChainInputW_length, Node.toPos, Extract.Pos.len]
  | wctLeaf L =>
      simp only [cell, Extract.wctLeafInputP, Node.toPos, Extract.Pos.len]
      rw [Cost.pad64_length, Extract.listInput_length']
      simp only [List.length_cons, List.length_drop, List.length_ofFn]
  | wctNode n =>
      simp only [cell, Node.toPos, Extract.Pos.len]
      rw [pad64_nodeInputP, nodeInputP, block4]
      simp only [List.length_append, bytesLE_length]
  | forest index =>
      simp only [cell, Extract.forestInput, Node.toPos, Extract.Pos.len]
      rw [Cost.pad64_length, WCT9.forestInput_length _ _ (by simp)]

theorem hdrBlock_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.hdrBlock (cell secrets node labels) = bytesLE 16 node.toPos.hdr := by
  cases node with
  | chain p =>
      change Extract.hdrBlock (WCT9.chainInputW p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val _) = _
      exact WCT9.chainInputW_header _ _ _ _ _ _
  | leaf L =>
      simp only [cell]
      rw [Extract.hdrBlock_leafInput]
      rfl
  | node n =>
      have ha : Active labels n := by
        by_contra ha; exact hp ⟨n, rfl, ha⟩
      rw [cell_node_active ha, Extract.hdrBlock_merkleNodeInputN]
      rfl
  | wctChain p =>
      simp only [cell]
      rw [Extract.hdrBlock_ftsChainInputW]
      rfl
  | wctLeaf L =>
      simp only [cell]
      rw [Extract.hdrBlock_wctLeafInputP]
      rfl
  | wctNode n =>
      simp only [cell]
      rw [Extract.hdrBlock_nodeInputP]
      rfl
  | forest index =>
      simp only [cell]
      rw [Extract.hdrBlock_forestInput]
      rfl
/-- Two active trials of one position have different nonce slots. -/
theorem merkleNodeInputN_nonce_inj {lay tree heap k k' : Nat} {l r l' r' : Digest} (hk : k < 2 ^ 64)
    (hk' : k' < 2 ^ 64)
    (h : pad64 (WCT9.merkleNodeInputN lay tree heap k l r) = pad64 (WCT9.merkleNodeInputN lay tree heap k' l' r')) :
    k = k' := by
  rw [WCT9.pad64_merkleNodeInputN, WCT9.pad64_merkleNodeInputN] at h
  unfold WCT9.merkleNodeInputN at h
  have h1 := List.append_inj_left' h (by simp [bytesLE_length])
  have h2 := List.append_inj_right' h1 (by simp [bytesLE_length])
  exact WCT9.nonceDigest_inj hk hk' (bytesLE_injective h2)
/-- Separation of the trial-node graph (phantoms included). -/
theorem cell_separated (secrets : Secrets) : Separated (cell secrets) := by
  intro left right hne before after heq
  by_cases hl : PhantomAt left before
  · obtain ⟨n, rfl, hn⟩ := cell_of_phantomAt (secrets := secrets) hl
    by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      rw [hn, hm] at heq
      exact hne (congrArg Node.node (phantom_injective heq))
    · have h1 := cell_length secrets right after hr
      rw [← heq, hn, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
  · by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      have h1 := cell_length secrets left before hl
      rw [heq, hm, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
    · have h1 := hdrBlock_cell secrets left before hl
      have h2 := hdrBlock_cell secrets right after hr
      have hlen : left.toPos.len = right.toPos.len := by
        rw [← cell_length secrets left before hl, ← cell_length secrets right after hr, heq]
      rw [heq] at h1
      have hpos := Extract.Pos.hdr_injective (toPos_bounded left) (toPos_bounded right) hlen
        (bytesLE_injective (h1.symm.trans h2))
      have hb := toPos_injective_base hpos
      cases left with
      | node n =>
          cases right with
          | node m =>
              have ha : Active before n := by by_contra ha; exact hl ⟨n, rfl, ha⟩
              have hb' : Active after m := by by_contra hb'; exact hr ⟨m, rfl, hb'⟩
              rw [cell_node_active ha, cell_node_active hb'] at heq
              have hk := merkleNodeInputN_nonce_inj (lt_trans n.1.nonce.isLt (by norm_num))
                (lt_trans m.1.nonce.isLt (by norm_num)) (by
                  have he : (Node.node n).toPos = (Node.node m).toPos := hpos
                  simp only [Node.toPos, Extract.Pos.node.injEq] at he
                  obtain ⟨e1, e2, e3, e4⟩ := he
                  rw [e1, e2, e3, e4] at heq
                  exact heq)
              apply hne
              have hnm : n = m := by
                have hw : withNonce n 0 = withNonce m 0 := Node.node.inj hb
                rw [← withNonce_self n, ← withNonce_self m, ← withNonce_withNonce n 0,
                  ← withNonce_withNonce m 0, hw, hk]
              rw [hnm]
          | _ => simp [Node.base] at hb
      | _ =>
          cases right <;> first
            | exact hne hb
            | (simp [Node.base] at hb)
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
/-- Depth bound of the values of tree level `level` (levels are spaced by `2^18` trial depths, all layers). -/
def levelDepth (_lay : Layer) (level : Nat) : Nat := 8 + level * 2 ^ 18
theorem depth_node (n : TreeNode) :
    (Node.node n).depth = levelDepth n.1.lay n.1.level.val + n.1.nonce.val := rfl
theorem depth_withNonce_lt (n : TreeNode) {j : Nat} (hj : j < trialCap n.1.lay n.1.level.val) {level : Nat}
    (hl : n.1.level.val + 1 ≤ level) : (Node.node (withNonce n j)).depth < levelDepth n.1.lay level := by
  have hc := trialCap_le n.1.lay n.1.level.val
  rw [depth_node]
  simp only [withNonce_lay, withNonce_level]
  rw [withNonce_nonce n (by omega)]
  unfold levelDepth
  have : (n.1.level.val + 1) * 2 ^ 18 ≤ level * 2 ^ 18 := Nat.mul_le_mul_right _ hl
  have : n.1.level.val * 2 ^ 18 + 2 ^ 18 ≤ level * 2 ^ 18 := by rw [Nat.add_mul, one_mul] at this; exact this
  have h2 : (2 : Nat) ^ 18 = 262144 := by norm_num
  omega
theorem find?_congr' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.find?_cons, h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
theorem trialFails_congr {left right : Labels} {n : TreeNode} {j : Nat}
    (h : left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    trialFails left n j ↔ trialFails right n j := by
  unfold trialFails; rw [h]
theorem selNonce_congr {left right : Labels} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    selNonce left n = selNonce right n := by
  unfold selNonce
  congr 1
  apply find?_congr'
  intro j hj
  rw [List.mem_range] at hj
  simp only [decide_eq_decide.mpr (trialFails_congr (h j hj))]
theorem selNonce_lt (labels : Labels) (n : TreeNode) : selNonce labels n < trialCap n.1.lay n.1.level.val := by
  have hc := trialCap_pos n.1.lay n.1.level.val
  unfold selNonce
  cases hf : (List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFails labels n j) with
  | none => simp only [Option.getD_none]; omega
  | some j =>
      simp only [Option.getD_some]
      exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
theorem selNode_congr {left right : Labels} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    selNode left n = selNode right n := by
  unfold selNode; rw [selNonce_congr h]
theorem selNode_label_congr {left right : Labels} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    left (.node (selNode left n)) = right (.node (selNode right n)) := by
  rw [selNode_congr h]
  exact h _ (selNonce_lt right n)
/-- A single-trial position (lower trees, the root, any node off the top tree's nonce levels) selects nonce 0. -/
theorem selNonce_of_cap_one {labels : Labels} {n : TreeNode} (h : trialCap n.1.lay n.1.level.val = 1) :
    selNonce labels n = 0 := by
  have := selNonce_lt labels n; omega
theorem selNode_of_cap_one {labels : Labels} {n : TreeNode} (h : trialCap n.1.lay n.1.level.val = 1)
    (h0 : n.1.nonce.val = 0) : selNode labels n = n := by
  unfold selNode
  rw [selNonce_of_cap_one h, ← h0, withNonce_self]
theorem trialCap_lower {lay : Layer} (h : lay ≠ 0) (level : Nat) : trialCap lay level = 1 := by
  unfold trialCap; rw [if_neg (fun h' => h h'.1)]
theorem trialCap_root (lay : Layer) : trialCap lay 11 = 1 := by
  unfold trialCap; rw [if_neg (fun h' => by omega)]
theorem treeNodeAt_nonce {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {n : TreeNode}
    (h : treeNodeAt lay tree level c = some n) : n.1.nonce.val = 0 := by
  unfold treeNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem treeNodeAt_lay {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {n : TreeNode}
    (h : treeNodeAt lay tree level c = some n) : n.1.lay = lay := by
  unfold treeNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem treeLabel_congr (left right : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ other : Node, other.depth < levelDepth lay level → left other = right other) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L =>
        simp only
        rw [h _ (by simp only [Node.depth, levelDepth]; omega)]
  · cases hn : treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        have hl := treeNodeAt_level hn
        have hlay := treeNodeAt_lay hn
        rw [selNode_label_congr (fun j hj => h _ (by
          have := depth_withNonce_lt n hj (level := level) (by omega)
          rw [hlay] at this; exact this))]
theorem ftsNodeAt_coord {index : Fin (2^31)} {coord : Fin 9} {level c : Nat} {n : WctNodePos}
    (h : ftsNodeAt index coord level c = some n) : n.1.coord = coord := by
  unfold ftsNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (h : ∀ other : Node, other.depth < 5 + 7 * coord.val + level → left other = right other) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  unfold ftsLabel
  split_ifs with hzero hc
  · have hd : (Node.wctLeaf ⟨index, coord, ⟨c, hc⟩⟩).depth < 5 + 7 * coord.val + level := by
      show 4 + 7 * coord.val < _; omega
    rw [h _ hd]
  · rfl
  all_goals
    cases hn : ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n =>
        have hd : (Node.wctNode n).depth < 5 + 7 * coord.val + level := by
          show 5 + 7 * n.1.coord.val + n.1.level.val < _
          rw [ftsNodeAt_level hn, ftsNodeAt_coord hn]; omega
        simp only [h _ hd]
theorem ftsPrevLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (h : ∀ other : Node, other.depth < 4 + 7 * coord.val → left other = right other) :
    ftsPrevLabel left index coord = ftsPrevLabel right index coord := by
  unfold ftsPrevLabel
  split_ifs with hz
  · rfl
  · have hc : 0 < coord.val := Nat.pos_of_ne_zero hz
    rw [ftsLabel_congr left right index _ 6 0 (fun other ho => h other (by simp only at ho; omega)),
      ftsLabel_congr left right index _ 6 1 (fun other ho => h other (by simp only at ho; omega))]
/-- An earlier trial is shallower. -/
theorem depth_trial_lt (n : TreeNode) {j : Nat} (hj : j < n.1.nonce.val) :
    (Node.node (withNonce n j)).depth < (Node.node n).depth := by
  have hk := n.1.nonce.isLt
  rw [depth_node, depth_node]
  simp only [withNonce_lay, withNonce_level]
  rw [withNonce_nonce n (by omega)]
  omega
theorem activeCongr (left right : Labels) (n : TreeNode)
    (h : ∀ j < n.1.nonce.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    Active left n ↔ Active right n := by
  unfold Active
  exact and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj => trialFails_congr (h j hj)
theorem cell_congr (secrets : Secrets) (node : Node) (left right : Labels)
    (h : ∀ other : Node, other.depth < node.depth → left other = right other) :
    cell secrets node left = cell secrets node right := by
  cases node with
  | chain p =>
      change inputW (seedsOf secrets) p (chainLabels left) =
        inputW (seedsOf secrets) p (chainLabels right)
      unfold inputW priorW
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
        unfold endLabel
        rw [h _ (by simp only [Node.depth, endPt]; exact Nat.mod_lt _ (by decide))]
      simp only [cell, hends]
  | node n =>
      have hl := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by rw [depth_node]; omega))
      have hr := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by rw [depth_node]; omega))
      have ha : Active left n ↔ Active right n := activeCongr left right n (fun j hj => h _ (depth_trial_lt n hj))
      simp only [cell, hl, hr, ha]
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
        rw [h _ (by show 3 < 4 + 7 * L.coord.val; omega)]
      have hpad := ftsPrevLabel_congr left right L.index L.coord
        (fun other ho => h other (by show other.depth < 4 + 7 * L.coord.val; omega))
      simp only [cell, hends, hpad]
  | wctNode n =>
      have hl := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hr := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hpad := ftsPrevLabel_congr left right n.1.index n.1.coord
        (fun other ho => h other (by show other.depth < 5 + 7 * n.1.coord.val + n.1.level.val; omega))
      simp only [cell, hl, hr, hpad]
  | forest index =>
      have hroots : ((List.range 9).map fun coord =>
            (ftsLabel left index (fin9 coord) 6 0, ftsLabel left index (fin9 coord) 6 1)) =
          ((List.range 9).map fun coord =>
            (ftsLabel right index (fin9 coord) 6 0, ftsLabel right index (fin9 coord) 6 1)) := by
        apply List.map_congr_left
        intro coord _
        have hc := (fin9 coord).isLt
        rw [ftsLabel_congr left right index (fin9 coord) 6 0
            (fun other ho => h other (show other.depth < 70 by omega)),
          ftsLabel_congr left right index (fin9 coord) 6 1
            (fun other ho => h other (show other.depth < 70 by omega))]
      simp only [cell, hroots]
theorem posOf_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.posOf (cell secrets node labels) = some node.toPos :=
  Extract.posOf_eq (toPos_bounded node) (cell_length secrets node labels hp) (hdrBlock_cell secrets node labels hp)
theorem posOf_cell_phantom (secrets : Secrets) (node : Node) (labels : Labels) (hp : PhantomAt node labels) :
    Extract.posOf (cell secrets node labels) = none := by
  obtain ⟨n, -, hc⟩ := cell_of_phantomAt (secrets := secrets) hp
  rw [hc, posOf_phantom]
/-- A cell decoding to a position belongs to a non-phantom node of that position. -/
theorem cell_eq_of_posOf {input : HashInput} {node node' : Node} (secrets : Secrets) (labels : Labels)
    (hpos : Extract.posOf input = some node.toPos) (h : input = cell secrets node' labels) :
    node'.toPos = node.toPos ∧ ¬ PhantomAt node' labels := by
  subst h
  by_cases hp : PhantomAt node' labels
  · rw [posOf_cell_phantom secrets node' labels hp] at hpos; cases hpos
  · rw [posOf_cell secrets node' labels hp] at hpos
    exact ⟨Option.some.inj hpos, hp⟩
theorem height_pos (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide
def rootNode : TreeNode :=
  ⟨⟨0, 0, ⟨height 0 - 1, by decide⟩, ⟨0, by decide⟩, 0⟩, by decide⟩
def ftsTopNode (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) : WctNodePos :=
  ⟨⟨index, coord, ⟨5, by decide⟩, ⟨b.val, by have := b.isLt; omega⟩⟩, show b.val < 2 ^ (7 - 5 - 1) by
    have := b.isLt; omega⟩
theorem height_ge_two (lay : Layer) : 2 ≤ height lay := by fin_cases lay <;> decide
def topNode (lay : Layer) (tree : Fin (2^31)) (ht : tree.val < 2 ^ treeBits lay) (b : Fin 2) : TreeNode :=
  ⟨⟨lay, tree, ⟨height lay - 2, by have := SigGolfCandidate.T3M.Extract.height_le lay; omega⟩,
    ⟨b.val, by have := b.isLt; omega⟩, 0⟩,
    ⟨show height lay - 2 < height lay by have := height_ge_two lay; omega, by
      have := height_ge_two lay
      show b.val < 2 ^ (height lay - (height lay - 2) - 1)
      rw [show height lay - (height lay - 2) - 1 = 1 by omega]
      have := b.isLt; omega, ht, Or.inr (by have := height_ge_two lay; show height lay - 2 + 1 < height lay; omega)⟩⟩
theorem treeLabel_top (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (ht : tree.val < 2 ^ treeBits lay)
    (b : Fin 2) :
    treeLabel labels lay tree (height lay - 1) b.val =
      (Node.node (topNode lay tree ht b)).toPos.proj (labels (.node (selNode labels (topNode lay tree ht b)))) := by
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
theorem selNode_rootNode (labels : Labels) : selNode labels rootNode = rootNode :=
  selNode_of_cap_one (trialCap_root 0) rfl
theorem treeLabel_root (labels : Labels) :
    treeLabel labels 0 0 (height 0) 0 = (labels (.node rootNode)).extractLsb' 0 128 := by
  unfold treeLabel
  rw [if_neg (by decide)]
  unfold treeNodeAt
  rw [dif_pos (by decide)]
  change (Node.node rootNode).toPos.proj (labels (.node (selNode labels rootNode))) = _
  rw [selNode_rootNode]
  rfl
theorem ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    ftsLabel labels index coord 6 b.val = (labels (.wctNode (ftsTopNode index coord b))).extractLsb' 128 128 := by
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
      change (rowW p _).length ≤ 4096
      rw [rowW_length]; omega
  | leaf L =>
      simp only [cell, Extract.leafInput]
      rw [Cost.pad64_length, SigGolfCandidate.T3.leafInput_length]
      have hc : chainCount L.1.lay ≤ 58 := chainCount_bound L.1.lay
      simp only [List.length_map, List.length_range]
      split_ifs <;> omega
  | node n =>
      by_cases ha : Active labels n
      · rw [cell_node_active ha, WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]; omega
      · rw [cell_node_inactive ha, phantom_length]; omega
  | wctChain p =>
      simp only [cell, WCT9.ftsChainInputW_length]
      omega
  | wctLeaf L =>
      simp only [cell, Extract.wctLeafInputP]
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
/-- Half-cell of secret `a`: for an address `(lay, tree, f, j)` with `j < famSize lay f` it is the packed half
`famOrd lay f j` of `lowerSeedPair lay tree` (coefficient `j` of family `f`); other addresses get distinct unused
cells. -/
def seedCoordinateP (a : Address) : ChainGraph.HalfCoordinate :=
  if a.chain.val < WCT9.famSize a.layer a.leaf.val then
    (.inl (WCT9.lowerSeedHeader a.layer a.tree.val (famOrd a.layer a.leaf.val a.chain.val / 2)),
      fullHalf (famOrd a.layer a.leaf.val a.chain.val))
  else (.inl (header 0 a.layer.val a.tree.val (a.chain.val / 2) (a.leaf.val + 1)), fullHalf a.chain.val)
def secretCoordinate : SecretIndex → ChainGraph.HalfCoordinate := Sum.elim seedCoordinateP wctCoefCoordinate
theorem fullHalf_val (n : Nat) : (fullHalf n).val = n % 2 := rfl
theorem famOrd_pair_lt' (a : Address) : famOrd a.layer a.leaf.val a.chain.val / 2 < 2 ^ 32 := by
  have h1 := a.leaf.isLt; have h2 := a.chain.isLt
  have h3 := WCT9.famBase_le a.layer
  have : WCT9.famBase a.layer * a.leaf.val ≤ 39 * 4096 := Nat.mul_le_mul h3 (by omega)
  unfold famOrd
  omega
theorem famOrd_inj {lay : Layer} {f f' j j' : Nat} (hj : j < WCT9.famBase lay) (hj' : j' < WCT9.famBase lay)
    (h : famOrd lay f j = famOrd lay f' j') : f = f' ∧ j = j' := by
  unfold famOrd at h
  rcases Nat.lt_or_ge f f' with hlt | hge
  · exfalso
    have : WCT9.famBase lay * f + WCT9.famBase lay ≤ WCT9.famBase lay * f' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rcases Nat.lt_or_ge f' f with hlt' | hge'
    · exfalso
      have : WCT9.famBase lay * f' + WCT9.famBase lay ≤ WCT9.famBase lay * f := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt'
      omega
    · have hff : f = f' := by omega
      subst hff
      exact ⟨rfl, by omega⟩
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
  have pl := famOrd_pair_lt' left; have pr := famOrd_pair_lt' right
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  unfold seedCoordinateP at hp hh
  by_cases hc : left.chain.val < WCT9.famSize left.layer left.leaf.val <;>
    by_cases hc' : right.chain.val < WCT9.famSize right.layer right.leaf.val
  · rw [if_pos hc, if_pos hc'] at hp hh
    simp only [fullHalf_val, Sum.inl.injEq] at hp hh
    unfold WCT9.lowerSeedHeader at hp
    obtain ⟨-, e1, e2, e3, -⟩ := header_injective (by decide) (by omega) (by omega) pl (by omega)
      (by decide) (by omega) (by omega) pr (by omega) hp
    have elay : left.layer = right.layer := Fin.ext e1
    rw [elay] at e3 hh hc
    have eo : famOrd right.layer left.leaf.val left.chain.val =
        famOrd right.layer right.leaf.val right.chain.val := by omega
    obtain ⟨e4, e5⟩ := famOrd_inj (lt_of_lt_of_le hc (WCT9.famSize_le_base _ _))
      (lt_of_lt_of_le hc' (WCT9.famSize_le_base _ _)) eo
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
/-- The nodes whose used half is the HIGH half of their output (`Pos.high`): on the paired tree's legacy (unpaired)
FTS positions the top FTS nodes (`wctNode` level 5, nested FTS r1-1; the paired forest's own halves are
`CanonGraph.Paired.highNode`), the left children of the lower trees (C2) and the last step of lower chain 0 (C3).
The name is historical. -/
def Node.isTop (N : Node) : Bool := N.toPos.high
theorem proj_toPos (N : Node) (y : HashOutput) :
    N.toPos.proj y = if N.isTop then y.extractLsb' 128 128 else y.extractLsb' 0 128 := by
  rw [Extract.Pos.proj_eq]; rfl
theorem high_chain (q : Point) : (Node.chain q).toPos.high = WCT9.chainHigh q.1.layer q.1.chain.val q.2.val := rfl
/-- C3: a point of an F chain (`isG = false`) below the last step uses the low half. -/
theorem proj_chain_of_lt {q : Point} (hG : WCT9.isG q.1.layer q.1.chain.val = false) (h : q.2.val < 6)
    (y : HashOutput) : (Node.chain q).toPos.proj y = y.extractLsb' 0 128 := by
  rw [Extract.Pos.proj_of_low (by rw [high_chain]; exact WCT9.chainHigh_eq_false_F hG (Or.inr (by omega)))]
theorem isTop_wctNode (n : WctNodePos) : (Node.wctNode n).isTop = decide (n.1.level.val = 5) := rfl
theorem isTop_wctLeaf (L : WctLeafPos) : (Node.wctLeaf L).isTop = false := rfl
theorem proj_toPos_of_not_top {N : Node} (h : N.isTop = false) (y : HashOutput) :
    N.toPos.proj y = y.extractLsb' 0 128 := by
  rw [proj_toPos, h]; rfl
/-- The two halves of an output, swapped. -/
noncomputable def swapOut : HashOutput ≃ HashOutput :=
  (ChainGraph.outputEquiv.trans (Equiv.prodComm _ _)).trans ChainGraph.outputEquiv.symm
theorem proj_top (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) (y : HashOutput) :
    (Node.wctNode (ftsTopNode index coord b)).toPos.proj y = y.extractLsb' 128 128 := by
  rw [proj_toPos]; rfl
theorem swapOut_low (y : HashOutput) : (swapOut y).extractLsb' 0 128 = y.extractLsb' 128 128 :=
  ChainGraph.joinOutput_low _ _
theorem swapOut_high (y : HashOutput) : (swapOut y).extractLsb' 128 128 = y.extractLsb' 0 128 :=
  ChainGraph.joinOutput_high _ _
/-- How node `N` stores its value: an output whose low half is the value, presented with the halves swapped for the
top FTS nodes, so that the value always sits in the half that `N.toPos.proj` reads. -/
noncomputable def presentEquiv (N : Node) : HashOutput ≃ HashOutput := if N.isTop then swapOut else Equiv.refl _
theorem proj_presentEquiv (N : Node) (y : HashOutput) : N.toPos.proj (presentEquiv N y) = y.extractLsb' 0 128 := by
  rw [proj_toPos]
  unfold presentEquiv
  cases N.isTop
  · rfl
  · exact swapOut_high y
/-- Witness stack: an FTS chain node reads the half `ftsChainHigh t step` (HIGH for G chains 1, 3 on steps < 3). -/
theorem proj_wctChain (p : WctPoint) (y : HashOutput) :
    (Node.wctChain p).toPos.proj y = projHalf (WCT9.ftsChainHigh p.1.2.2.2.val p.2.val) y := by
  simp only [Node.toPos, Extract.Pos.proj, Extract.Pos.high]
  cases WCT9.ftsChainHigh p.1.2.2.2.val p.2.val <;> rfl
/-- The used half of a presented FTS chain label is its stored low half. -/
theorem projHalf_presentEquiv_wctChain (p : WctPoint) (low high : Digest) :
    projHalf (WCT9.ftsChainHigh p.1.2.2.2.val p.2.val)
      (presentEquiv (Node.wctChain p) (ChainGraph.joinOutput low high)) = low := by
  rw [← proj_wctChain, proj_presentEquiv, ChainGraph.joinOutput_low]
noncomputable def labelPairEquiv : Labels ≃ LowLabels × LowLabels :=
  ((Equiv.piCongrRight fun N => (presentEquiv N).symm).trans
    (Equiv.arrowCongr (Equiv.refl Node) ChainGraph.outputEquiv)).trans
    (Equiv.arrowProdEquivProdArrow Node (fun _ => Digest) (fun _ => Digest))
/-- Labels from used halves `low` and other halves `high` (nested FTS r1-1: `low node` is the half that the node's
parents read, the high half for the top FTS nodes). -/
noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => presentEquiv node (ChainGraph.joinOutput (low node) (high node))
theorem labelPairEquiv_symm (low high : LowLabels) : labelPairEquiv.symm (low, high) = joinLabels low high := rfl
theorem joinLabels_val (low high : LowLabels) (node : Node) :
    node.toPos.proj (joinLabels low high node) = low node :=
  (proj_presentEquiv node _).trans (ChainGraph.joinOutput_low _ _)
theorem joinLabels_low {low high : LowLabels} {node : Node} (h : node.isTop = false) :
    (joinLabels low high node).extractLsb' 0 128 = low node := by
  rw [← proj_toPos_of_not_top h]; exact joinLabels_val low high node
theorem joinLabels_not_top {low high : LowLabels} {node : Node} (h : node.isTop = false) :
    joinLabels low high node = ChainGraph.joinOutput (low node) (high node) := by
  unfold joinLabels presentEquiv; rw [h]; rfl
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
    AgreesW answers (seedsOf (secretsOf answers)) (chainLabels labels) :=
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
/-- Coefficient `j` of family `f` as the signer reads it (`famCoefN lay tree leaf j = famCoefF lay tree (famOf leaf) j`). -/
def famCoefF (answers : Answers) (lay : Layer) (tree f j : Nat) : Digest :=
  WCT9.seedHalf (evalWithAnswerFn answers (WCT9.lowerSeedPair lay tree (famOrd lay f j / 2))) (famOrd lay f j)
theorem famCoefN_eq (answers : Answers) (lay : Layer) (tree leaf j : Nat) :
    WCT9.famCoefN answers lay tree leaf j = famCoefF answers lay tree (WCT9.famOf lay leaf) j := rfl
/-- A coefficient secret is the packed half the signer reads (stage B lower, T8D top). -/
theorem secretsOf_fam (answers : Answers) (a : Address) (hc : a.chain.val < WCT9.famSize a.layer a.leaf.val) :
    secretsOf answers (.inl a) = famCoefF answers a.layer a.tree.val a.leaf.val a.chain.val := by
  change halfAnswer answers (seedCoordinateP a) = _
  unfold seedCoordinateP famCoefF WCT9.seedHalf WCT9.lowerSeedHeader WCT9.lowerSeedPair
  rw [if_pos hc, halfAnswer_pair, fullHalf_val]
theorem leafFamily_secretsOf (answers : Answers) (lay : Layer) (tree : Fin (2 ^ 31)) (leaf : Fin 4096) :
    leafFamily (secretsOf answers) lay tree leaf = WCT9.famCoef answers lay tree.val leaf.val :=
  funext fun j => secretsOf_fam answers
    ⟨lay, tree, famSlot lay leaf, ⟨j.val, lt_trans j.isLt (WCT9.famSize_lt_58 lay _)⟩⟩ j.isLt
theorem seedsOf_secretsOf (answers : Answers) (a : Address) :
    seedsOf (secretsOf answers) a = WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val := by
  unfold seedsOf
  rw [leafFamily_secretsOf answers, WCT9.wotsSeed_fam]
end ClaudeWCT.W9.T3.Security.CanonGraph

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def first (coord : Nat) : Prop := coord<8 ∧ coord%2=0
instance (coord : Nat) : Decidable (first coord) := by unfold first;infer_instance
/-- Inverse of the fixed physical placement used by B and C trees. -/
def rawLeaf (coord physical : Nat) : Nat :=
  if first coord then physical else 2*(physical%64)+physical/64

def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (level physical : Nat) : Digest :=
  if level=0 then
    if h:rawLeaf coord.val physical<128 then
      Extract.Paired.proj (.wctLeaf index.val coord.val (rawLeaf coord.val physical))
        (labels (.wctLeaf ⟨index,coord,⟨rawLeaf coord.val physical,h⟩⟩))
    else 0
  else
    match ftsNodeAt index coord (level-1) physical with
    | some n=>Extract.Paired.proj (.wctNode index.val coord.val (level-1) physical) (labels (.wctNode n))
    | none=>0

/-- A and C bind the preceding pair; B binds the selected A branch. -/
def pads (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) : Digest×Digest :=
  if h:coord.val=0 then (0,0) else
    let previous : Fin 9:=⟨coord.val-1,by have:=coord.isLt;omega⟩
    if coord.val%2=1 then
      (ftsLabel labels index previous 5 (2*branch),ftsLabel labels index previous 5 (2*branch+1))
    else (ftsLabel labels index previous 6 0,ftsLabel labels index previous 6 1)

def cell (secrets : Secrets) : Node→Labels→HashInput
  | .wctLeaf L,labels=>pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
      (pads labels L.index L.coord (L.child.val%2)).1
      (List.ofFn fun t:Fin 6=>wctEndLabel labels (L.index,L.coord,L.child,t)))
  | .wctNode n,labels=>pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2^(7-n.1.level.val-1)+n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val))
      (if n.1.level.val=4 then (pads labels n.1.index n.1.coord (n.1.idx.val/2)).2 else 0)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)))
  | node,labels=>CanonGraph.cell secrets node labels

theorem hdrBlock_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.hdrBlock (cell secrets node labels)=bytesLE 16 node.toPos.hdr := by
  cases node with
  | wctLeaf L=>
    simp only [cell]
    rw [Extract.hdrBlock_wctLeafInputP]
    rfl
  | wctNode n=>
    simp only [cell]
    rw [Extract.hdrBlock_nodeInputP]
    rfl
  | chain v=>exact CanonGraph.hdrBlock_cell secrets (.chain v) labels hp
  | leaf v=>exact CanonGraph.hdrBlock_cell secrets (.leaf v) labels hp
  | node v=>exact CanonGraph.hdrBlock_cell secrets (.node v) labels hp
  | wctChain v=>exact CanonGraph.hdrBlock_cell secrets (.wctChain v) labels hp
  | forest v=>exact CanonGraph.hdrBlock_cell secrets (.forest v) labels hp

theorem cell_length (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    (cell secrets node labels).length=node.toPos.len := by
  cases node with
  | wctLeaf L=>
    simp only [cell,Extract.wctLeafInputP,Node.toPos,Extract.Pos.len]
    rw [Cost.pad64_length,Extract.listInput_length']
    simp only [List.length_cons,List.length_drop,List.length_ofFn]
  | wctNode n=>
    simp only [cell,Node.toPos,Extract.Pos.len]
    rw [pad64_nodeInputP,nodeInputP,block4]
    simp only [List.length_append,bytesLE_length]
  | chain v=>exact CanonGraph.cell_length secrets (.chain v) labels hp
  | leaf v=>exact CanonGraph.cell_length secrets (.leaf v) labels hp
  | node v=>exact CanonGraph.cell_length secrets (.node v) labels hp
  | wctChain v=>exact CanonGraph.cell_length secrets (.wctChain v) labels hp
  | forest v=>exact CanonGraph.cell_length secrets (.forest v) labels hp

/-- The Paired cell differs from the base cell only on FTS leaves and nodes (never phantoms). -/
theorem cell_node (secrets : Secrets) (n : TreeNode) (labels : Labels) :
    cell secrets (.node n) labels = CanonGraph.cell secrets (.node n) labels := rfl
theorem cell_separated (secrets : Secrets) : Separated (cell secrets) := by
  intro left right hne before after heq
  -- A tree node with the same cell: both are tree nodes (phantoms only collide with phantoms; a non-phantom
  -- tree-node cell decodes to a tree position). Reduce to the base separation there.
  by_cases hl : PhantomAt left before
  · obtain ⟨n, rfl, hn⟩ := cell_of_phantomAt (secrets := secrets) hl
    by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      exact CanonGraph.cell_separated secrets _ _ hne before after heq
    · have h1 := cell_length secrets right after hr
      rw [← heq, cell_node, hn, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
  · by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      have h1 := cell_length secrets left before hl
      rw [heq, cell_node, hm, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
    · have h1 := hdrBlock_cell secrets left before hl
      have h2 := hdrBlock_cell secrets right after hr
      have hlen : left.toPos.len = right.toPos.len := by
        rw [← cell_length secrets left before hl, ← cell_length secrets right after hr, heq]
      rw [heq] at h1
      have hpos := Extract.Pos.hdr_injective (toPos_bounded left) (toPos_bounded right) hlen
        (bytesLE_injective (h1.symm.trans h2))
      have hb := toPos_injective_base hpos
      cases left with
      | node n =>
          cases right with
          | node m => exact CanonGraph.cell_separated secrets _ _ hne before after heq
          | _ => simp [Node.base] at hb
      | _ =>
          cases right <;> first
            | exact hne hb
            | (simp [Node.base] at hb)

theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (h : ∀other:Node,other.depth<5+7*coord.val+level→left other=right other) :
    ftsLabel left index coord level c=ftsLabel right index coord level c := by
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [h _ (by simp only [Node.depth];omega)]
  · rfl
  all_goals
    cases hn:ftsNodeAt index coord (level-1) c with
    | none=>rfl
    | some n=>
      have hd:(Node.wctNode n).depth<5+7*coord.val+level := by
        show 5+7*n.1.coord.val+n.1.level.val<_
        rw [ftsNodeAt_level hn,ftsNodeAt_coord hn]
        omega
      simp only [h _ hd]

theorem pads_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat)
    (h : ∀other:Node,other.depth<4+7*coord.val→left other=right other) :
    pads left index coord branch=pads right index coord branch := by
  unfold pads
  split_ifs with hz hodd
  · rfl
  all_goals
    dsimp only
    apply Prod.ext
    all_goals dsimp only;apply ftsLabel_congr;intro other ho;apply h;dsimp at ho;omega

theorem cell_congr (secrets : Secrets) (node : Node) (left right : Labels)
    (h : ∀other:Node,other.depth<node.depth→left other=right other) :
    cell secrets node left=cell secrets node right := by
  cases node with
  | wctLeaf L=>
    have hends : (List.ofFn fun t:Fin 6=>wctEndLabel left (L.index,L.coord,L.child,t))=
        (List.ofFn fun t:Fin 6=>wctEndLabel right (L.index,L.coord,L.child,t)) := by
      congr 1
      funext t
      unfold wctEndLabel
      rw [h _ (by show 3<4+7*L.coord.val;omega)]
    have hpad:=pads_congr left right L.index L.coord (L.child.val%2)
      (fun other ho=>h other ho)
    simp only [cell,hends,hpad]
  | wctNode n=>
    have hl:=ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)
      (fun other ho=>h other ho)
    have hr:=ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)
      (fun other ho=>h other ho)
    have hpad:=pads_congr left right n.1.index n.1.coord (n.1.idx.val/2)
      (fun other ho=>h other (by show other.depth<5+7*n.1.coord.val+n.1.level.val;omega))
    simp only [cell,hl,hr,hpad]
  | _=>exact CanonGraph.cell_congr secrets _ left right h

/-- Every paired cell has its position's honest length (length-aware decoding, C3). -/
theorem posOf_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.posOf (cell secrets node labels)=some node.toPos :=
  Extract.posOf_eq (toPos_bounded node) (cell_length secrets node labels hp) (hdrBlock_cell secrets node labels hp)

theorem cell_eq_of_posOf {input : HashInput} {node node' : Node} (secrets : Secrets) (labels : Labels)
    (hpos : Extract.posOf input=some node.toPos) (h : input=cell secrets node' labels) :
    node'.toPos = node.toPos ∧ ¬ PhantomAt node' labels := by
  subst h
  by_cases hp : PhantomAt node' labels
  · obtain ⟨n, rfl, hc⟩ := cell_of_phantomAt (secrets := secrets) hp
    rw [cell_node, hc, posOf_phantom] at hpos; cases hpos
  · rw [posOf_cell secrets node' labels hp] at hpos
    exact ⟨Option.some.inj hpos, hp⟩

noncomputable def canonInputs : Finset HashInput := SeccLaw.publicUniverse
attribute [irreducible] canonInputs

theorem cell_length_le (secrets : Secrets) (node : Node) (labels : Labels) :
    (cell secrets node labels).length≤4096 := by
  cases node with
  | wctLeaf L=>
    simp only [cell,Extract.wctLeafInputP]
    rw [Cost.pad64_length,Extract.listInput_length']
    simp only [List.length_cons,List.length_drop,List.length_ofFn]
    omega
  | wctNode n=>
    simp only [cell]
    rw [pad64_nodeInputP,nodeInputP,block4]
    simp only [List.length_append,bytesLE_length]
    omega
  | chain v=>exact CanonGraph.cell_length_le secrets (.chain v) labels
  | leaf v=>exact CanonGraph.cell_length_le secrets (.leaf v) labels
  | node v=>exact CanonGraph.cell_length_le secrets (.node v) labels
  | wctChain v=>exact CanonGraph.cell_length_le secrets (.wctChain v) labels
  | forest v=>exact CanonGraph.cell_length_le secrets (.forest v) labels

theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels∈canonInputs := by
  rw [canonInputs]
  exact SeccLaw.mem_publicUniverse _ (cell_length_le secrets node labels)
theorem canonInputs_subset_publicUniverse : canonInputs⊆SeccLaw.publicUniverse := by
  rw [canonInputs]
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
#print axioms cell_congr
#print axioms graph_eq_uniform_programmed
#print axioms uniform_bind_programmed
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def Used : Node → Prop
  | .forest _ => False
  | .wctNode n => first n.1.coord.val → n.1.level.val < 5
  | _ => True
instance (n : Node) : Decidable (Used n) := by unfold Used; cases n <;> infer_instance

theorem used_iff_bounded (n : Node) : Used n ↔ Extract.Paired.Bounded n.toPos := by
  cases n with
  | forest i => rfl
  | wctNode n =>
      simp only [Used, Node.toPos, Extract.Paired.Bounded, Extract.Paired.first,
        decide_eq_true_eq]
      exact ⟨fun h => ⟨toPos_bounded (.wctNode n), h⟩, fun h => h.2⟩
  | chain p =>
      change True ↔ (Node.chain p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | leaf p =>
      change True ↔ (Node.leaf p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | node p =>
      change True ↔ (Node.node p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | wctChain p =>
      change True ↔ (Node.wctChain p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | wctLeaf p =>
      change True ↔ (Node.wctLeaf p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩

theorem treeLabel_congr (left right : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ other : Node, Used other → other.depth < levelDepth lay level → left other = right other) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L => simp only; rw [h (.leaf L) trivial (by simp only [Node.depth, levelDepth]; omega)]
  · cases hn : treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        have hl := treeNodeAt_level hn
        have hlay := treeNodeAt_lay hn
        rw [selNode_label_congr (fun j hj => h _ trivial (by
          have := depth_withNonce_lt n hj (level := level) (by omega)
          rw [hlay] at this; exact this))]

theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : first coord.val → level ≤ 5)
    (h : ∀ other : Node, Used other → other.depth < 5 + 7 * coord.val + level → left other = right other) :
    Paired.ftsLabel left index coord level c = Paired.ftsLabel right index coord level c := by
  unfold Paired.ftsLabel
  split_ifs with hzero hc
  · rw [h (.wctLeaf ⟨index,coord,⟨rawLeaf coord.val c,hc⟩⟩) trivial (by simp only [Node.depth]; omega)]
  · rfl
  all_goals
    cases hn : ftsNodeAt index coord (level-1) c with
    | none => rfl
    | some n =>
      have hu : Used (.wctNode n) := by
        change first n.1.coord.val → n.1.level.val < 5
        rw [ftsNodeAt_level hn, ftsNodeAt_coord hn]
        intro hf
        have := hl hf
        omega
      have hd : (Node.wctNode n).depth < 5+7*coord.val+level := by
        simp only [Node.depth]
        rw [ftsNodeAt_level hn,ftsNodeAt_coord hn]
        omega
      simp only [h _ hu hd]

theorem pads_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat)
    (h : ∀other : Node, Used other → other.depth<4+7*coord.val → left other=right other) :
    Paired.pads left index coord branch = Paired.pads right index coord branch := by
  unfold Paired.pads
  split_ifs with hz hodd
  · rfl
  · dsimp only
    apply Prod.ext
    all_goals
      dsimp only
      apply ftsLabel_congr
      · intro _; omega
      · intro other hu ho; apply h other hu; dsimp at ho; omega
  · dsimp only
    apply Prod.ext
    all_goals
      dsimp only
      apply ftsLabel_congr
      · intro hf
        unfold first at hf
        dsimp only at hf
        omega
      · intro other hu ho; apply h other hu; dsimp at ho; omega

theorem cell_congr_nonforest (secrets : Secrets) (node : Node)
    (hnf : ∀i, node≠.forest i) (left right : Labels)
    (h : ∀ other : Node, Used other → other.depth < node.depth → left other = right other) :
    Paired.cell secrets node left = Paired.cell secrets node right := by
  cases node with
  | chain p =>
      change inputW (seedsOf secrets) p (chainLabels left) =
        inputW (seedsOf secrets) p (chainLabels right)
      unfold inputW priorW
      split_ifs with hz
      · rfl
      · have hd := h (.chain (ChainGraph.predecessor p)) trivial (by
          simp only [Node.depth, ChainGraph.predecessor]; omega)
        simp only [chainLabels, hd]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets left L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets right L.1) := by
        apply List.map_congr_left
        intro i _
        -- C3 (#866): a leaf reads the used half of its chains' last-step labels (`endLabel` via `endPt`).
        unfold endLabel
        rw [h (.chain _) trivial (by simp only [Node.depth, endPt]; exact Nat.mod_lt _ (by decide))]
      simp only [Paired.cell, CanonGraph.cell, hends]
  | node n =>
      have hl := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val)
        (fun other ho hd => h other ho (by rw [depth_node]; omega))
      have hr := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val+1)
        (fun other ho hd => h other ho (by rw [depth_node]; omega))
      have ha : Active left n ↔ Active right n :=
        activeCongr left right n (fun j hj => h _ trivial (depth_trial_lt n hj))
      simp only [Paired.cell, CanonGraph.cell, hl, hr, ha]
  | wctChain p =>
      have hv : wctValueL secrets left p.1 p.2.val = wctValueL secrets right p.1 p.2.val := by
        unfold wctValueL
        split_ifs with hz
        · rfl
        · rw [h (.wctChain (p.1,⟨(p.2.val-1)%4,Nat.mod_lt _ (by decide)⟩)) trivial (by simp only [Node.depth]; have := p.2.isLt; omega)]
      simp only [Paired.cell, CanonGraph.cell, hv]
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel left (L.index,L.coord,L.child,t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel right (L.index,L.coord,L.child,t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [h (.wctChain ((L.index,L.coord,L.child,t),3)) trivial (by show 3<4+7*L.coord.val; omega)]
      have hpad := pads_congr left right L.index L.coord (L.child.val%2)
        (fun other ho hd => h other ho hd)
      simp only [Paired.cell,hends,hpad]
  | wctNode n =>
      have hh : first n.1.coord.val → n.1.level.val ≤ 5 := fun _ => Nat.le_of_lt_succ n.1.level.isLt
      have hl := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val) hh
        (fun other ho hd => h other ho hd)
      have hr := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1) hh
        (fun other ho hd => h other ho hd)
      have hpad := pads_congr left right n.1.index n.1.coord (n.1.idx.val/2)
        (fun other ho hd => h other ho (by change other.depth<5+7*n.1.coord.val+n.1.level.val; omega))
      simp only [Paired.cell,hl,hr,hpad]
  | forest i => exact (hnf i rfl).elim

theorem cell_congr (secrets : Secrets) (node : Node) (hu : Used node) (left right : Labels)
    (h : ∀ other : Node, Used other → other.depth < node.depth → left other = right other) :
    Paired.cell secrets node left = Paired.cell secrets node right := by
  apply cell_congr_nonforest secrets node _ left right h
  intro i hi
  subst node
  exact hu

end ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def order : List Node := CanonGraph.order.filter (fun n => decide (Used n))
theorem mem_order (n : Node) : n ∈ order ↔ Used n := by
  simp only [order, List.mem_filter, CanonGraph.mem_order, true_and, decide_eq_true_eq]
theorem order_nodup : order.Nodup := CanonGraph.order_nodup.filter _
theorem order_sorted : order.Pairwise (fun left right => left.depth ≤ right.depth) :=
  CanonGraph.order_sorted.filter _

noncomputable def programmed (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => Paired.cellIn U hU secrets node labels) labels residual order

theorem programmed_at (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) (node : Node) (hu : Used node) :
    programmed U hU secrets labels residual (Paired.cellIn U hU secrets node labels) = labels node :=
  patch_at _ (Paired.cellIn_injective U hU secrets labels) labels residual order node ((mem_order node).2 hu)

theorem programmed_other (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, Used node → query.val ≠ Paired.cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node hn heq
  exact hquery node ((mem_order node).1 hn) (congrArg Subtype.val heq)

theorem replay_snd (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
    (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (hused : ∀node∈nodes, Used node)
    (before : Labels) (hagrees : ∀node, Used node → node∉nodes → before node=labels node) :
    (replay (Paired.cellIn U hU secrets) advance labels residual nodes before).2 =
      patch (fun node => Paired.cellIn U hU secrets node labels) labels residual nodes := by
  induction nodes generalizing before with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨hdepth,hsorted⟩ := List.pairwise_cons.mp hsorted
    have hinput : Paired.cellIn U hU secrets first before = Paired.cellIn U hU secrets first labels := by
      apply Subtype.ext
      apply cell_congr secrets first (hused first (by simp))
      intro other hu ho
      apply hagrees other hu
      intro hmem
      rcases List.mem_cons.mp hmem with heq|hmem
      · rw [heq] at ho; omega
      · have := hdepth _ hmem; omega
    have hafter : ∀node, Used node → node∉rest → advance first (labels first) before node=labels node := by
      intro node hu hn
      unfold advance
      by_cases heq : node=first
      · subst node; rw [Function.update_self]
      · rw [Function.update_of_ne heq]
        exact hagrees node hu (fun hm => (List.mem_cons.mp hm).elim heq hn)
    simp only [replay, patch]
    rw [ih hsorted (fun node hn => hused node (List.mem_cons_of_mem _ hn)) _ hafter, hinput]

section Laws
variable (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (U → HashOutput) := SampleableType.ofFintype _

theorem plant_bind_programmed {Result : Type} (secrets : Secrets)
    (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let result ← plant (Paired.cellIn U hU secrets) advance order (fun _ => 0); next result.2] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] := by
  rw [evalSPMF_bind, evalDist_plant_eq_replay _ _ _ order_nodup]
  simp only [evalSPMF_bind, bind_assoc, evalSPMF_pure, pure_bind]
  apply bind_congr
  intro labels
  apply bind_congr
  intro residual
  rw [replay_snd U hU secrets labels residual order order_sorted
    (fun node hn => (mem_order node).1 hn) _
    (fun node hu hn => (hn ((mem_order node).2 hu)).elim)]
  rfl

theorem uniform_bind_programmed {Result : Type} (secrets : Secrets)
    (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
      law >>= fun result => 𝒮[next result.2])
    (Paired.read_eq_plant U hU secrets order order_nodup (fun _ => 0))
  have h' : 𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do let result ← plant (Paired.cellIn U hU secrets) advance order (fun _ => 0); next result.2] := by
    simpa only [evalSPMF_bind,evalSPMF_pure,bind_assoc,pure_bind] using h
  exact h'.trans (plant_bind_programmed U hU secrets next)
end Laws

def Agrees (answers : Correctness.Answers) (labels : Labels) : Prop :=
  ∀node, Used node → answers (.inl (.inr (Paired.cell (secretsOf answers) node labels)))=labels node

theorem agrees_of_programmed (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
    (answers : Correctness.Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀x : U, answers (.inl (.inr x.val))=programmed U hU (secretsOf answers) labels residual x) :
    Agrees answers labels := by
  intro node hu
  have h := hpub (Paired.cellIn U hU (secretsOf answers) node labels)
  rw [programmed_at _ _ _ _ _ _ hu] at h
  exact h
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SphincsSecurity.Concrete
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- C1: the nodes whose label is presented through the high output half: the top folds of
`highPosition`, the singleton's left top node (stage 2, `singletonHigh`), the even nodes of levels `0..2` and the
leaves of even physical children; on the lower trees the #866 rule (C2: left children, C3: the last step of lower chain
0; `Extract.Pos.high`). -/
def highNode : Node → Bool
  | .wctNode n => decide (Extract.Paired.highNodeAt n.1.coord.val n.1.level.val n.1.idx.val)
  | .wctLeaf L => decide (Extract.Paired.highLeafAt L.coord.val L.child.val)
  | .chain p => (Node.chain p).toPos.high
  | .leaf L => (Node.leaf L).toPos.high
  | .node n => (Node.node n).toPos.high
  | .wctChain p => (Node.wctChain p).toPos.high
  | .forest _ => false

theorem proj_toPos (N : Node) (y : HashOutput) :
    Extract.Paired.proj N.toPos y = if highNode N then y.extractLsb' 128 128 else y.extractLsb' 0 128 := by
  cases N with
  | wctNode n =>
      simp only [Node.toPos,highNode,Extract.Paired.proj,decide_eq_true_eq,ite_apply]
  | wctLeaf L =>
      simp only [Node.toPos,highNode,Extract.Paired.proj,decide_eq_true_eq,ite_apply]
  | chain p => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | leaf L => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | node n => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | wctChain p => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | forest i => rfl

/-- C2/C3: on the lower trees the paired projection is the legacy (#866) `Pos.proj`. -/
theorem pairedProj_chain (p : ChainGraph.Point) : Extract.Paired.proj (Node.chain p).toPos = (Node.chain p).toPos.proj :=
  Extract.Paired.proj_chain _ _ _ _ _
theorem pairedProj_leaf (L : SrcLeaf) : Extract.Paired.proj (Node.leaf L).toPos = (Node.leaf L).toPos.proj :=
  Extract.Paired.proj_leaf _ _ _
theorem pairedProj_node (n : TreeNode) : Extract.Paired.proj (Node.node n).toPos = (Node.node n).toPos.proj :=
  Extract.Paired.proj_node _ _ _ _

noncomputable def presentEquiv (N : Node) : HashOutput ≃ HashOutput :=
  if highNode N then CanonGraph.swapOut else Equiv.refl _

theorem proj_presentEquiv (N : Node) (y : HashOutput) :
    Extract.Paired.proj N.toPos (presentEquiv N y)=y.extractLsb' 0 128 := by
  rw [proj_toPos]
  unfold presentEquiv
  cases highNode N
  · rfl
  · exact CanonGraph.swapOut_high y

noncomputable def labelPairEquiv : Labels ≃ LowLabels × LowLabels :=
  ((Equiv.piCongrRight fun N => (presentEquiv N).symm).trans
    (Equiv.arrowCongr (Equiv.refl Node) ChainGraph.outputEquiv)).trans
    (Equiv.arrowProdEquivProdArrow Node (fun _ => Digest) (fun _ => Digest))

noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => presentEquiv node (ChainGraph.joinOutput (low node) (high node))

theorem labelPairEquiv_symm (low high : LowLabels) : labelPairEquiv.symm (low,high)=joinLabels low high := rfl

theorem joinLabels_val (low high : LowLabels) (node : Node) :
    Extract.Paired.proj node.toPos (joinLabels low high node)=low node :=
  (proj_presentEquiv node _).trans (ChainGraph.joinOutput_low _ _)

/-- C2/C3: the used half (`Pos.proj`) of a lower-tree label is its low label (the paired form of the legacy
`CanonGraph.joinLabels_val`, used where `CanonGraph.treeLabel`/`endLabel` read a label through `Pos.proj`). -/
theorem joinLabels_node (low high : LowLabels) (n : TreeNode) :
    (Node.node n).toPos.proj (joinLabels low high (.node n))=low (.node n) := by
  rw [←pairedProj_node]; exact joinLabels_val low high (.node n)
theorem joinLabels_leaf (low high : LowLabels) (L : SrcLeaf) :
    (Node.leaf L).toPos.proj (joinLabels low high (.leaf L))=low (.leaf L) := by
  rw [←pairedProj_leaf]; exact joinLabels_val low high (.leaf L)
theorem joinLabels_chain (low high : LowLabels) (p : ChainGraph.Point) :
    (Node.chain p).toPos.proj (joinLabels low high (.chain p))=low (.chain p) := by
  rw [←pairedProj_chain]; exact joinLabels_val low high (.chain p)

theorem joinLabels_not_high {low high : LowLabels} {node : Node} (h : highNode node=false) :
    joinLabels low high node=ChainGraph.joinOutput (low node) (high node) := by
  unfold joinLabels presentEquiv
  rw [h]
  rfl

theorem joinLabels_low {low high : LowLabels} {node : Node} (h : highNode node=false) :
    (joinLabels low high node).extractLsb' 0 128=low node := by
  rw [joinLabels_not_high h]
  exact ChainGraph.joinOutput_low _ _

section Laws
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _

theorem labels_bind {Result : Type} (next : Labels → ProbComp Result) :
    𝒮[do let labels ← ($ᵗ Labels : ProbComp _); next labels] =
      𝒮[do
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        next (joinLabels low high)] := by
  have hpair : 𝒮[labelPairEquiv <$> ($ᵗ Labels : ProbComp _)] =
      𝒮[do let low ← ($ᵗ LowLabels : ProbComp _); let high ← ($ᵗ LowLabels : ProbComp _); pure (low,high)] :=
    (evalSPMF_map_bijective_uniform_cross (α := Labels) (β := LowLabels × LowLabels)
      labelPairEquiv labelPairEquiv.bijective).trans (FullGame.uniform_product (A := LowLabels) (B := LowLabels)).symm
  have h := congrArg (fun law : SPMF (LowLabels × LowLabels) =>
    law >>= fun result => 𝒮[next (labelPairEquiv.symm result)]) hpair
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply,labelPairEquiv_symm] using h
end Laws
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired
