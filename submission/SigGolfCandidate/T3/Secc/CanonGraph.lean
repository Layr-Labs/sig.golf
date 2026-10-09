import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.WotsEvents

namespace SigGolfCandidate.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
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
structure TreeNodeRaw where
  lay : Layer
  tree : Fin (2^31)
  level : Fin 12
  idx : Fin 2048
  deriving DecidableEq, Fintype
def TreeNodeRaw.Valid (n : TreeNodeRaw) : Prop :=
  n.level.val < height n.lay ∧ n.idx.val < 2 ^ (height n.lay - n.level.val - 1)
instance instDecidablePredTreeNodeRawValid : DecidablePred TreeNodeRaw.Valid := fun n => by unfold TreeNodeRaw.Valid; infer_instance
abbrev TreeNode := {n : TreeNodeRaw // n.Valid}
structure FtsLeafPos where
  index : Fin (2^31)
  coord : Fin 7
  leaf : Fin 2048
  deriving DecidableEq, Fintype
structure FtsNodeRaw where
  index : Fin (2^31)
  coord : Fin 7
  level : Fin 11
  idx : Fin 1024
  deriving DecidableEq, Fintype
def FtsNodeRaw.Valid (n : FtsNodeRaw) : Prop := n.idx.val < 2 ^ (11 - n.level.val - 1)
instance instDecidablePredFtsNodeRawValid : DecidablePred FtsNodeRaw.Valid := fun n => by unfold FtsNodeRaw.Valid; infer_instance
abbrev FtsNodePos := {n : FtsNodeRaw // n.Valid}
inductive Node where
  | chain (point : Point)
  | leaf (pos : LeafPos)
  | node (pos : TreeNode)
  | ftsLeaf (pos : FtsLeafPos)
  | ftsNode (pos : FtsNodePos)
  | forest (index : Fin (2^31))
  deriving DecidableEq, Fintype
attribute [local irreducible] ChainGraph.instFintypeAddress
def Node.depth : Node → Nat
  | .chain p => p.2.val
  | .leaf _ => 7
  | .node n => 8 + n.1.level.val
  | .ftsLeaf _ => 0
  | .ftsNode n => 1 + n.1.level.val
  | .forest _ => 12
abbrev SecretIndex := Address ⊕ FtsLeafPos
abbrev Secrets := SecretIndex → Digest
abbrev Labels := Node → HashOutput
def seedsOf (secrets : Secrets) : Seeds := fun address => secrets (.inl address)
def ftsOf (secrets : Secrets) : FtsLeafPos → Digest := fun leaf => secrets (.inr leaf)
def chainLabels (labels : Labels) : ChainGraph.Labels := fun point => labels (.chain point)
def fin58 (i : Nat) : Fin 58 := ⟨i % 58, Nat.mod_lt _ (by decide)⟩
def fin7 (i : Nat) : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
def endLabel (secrets : Secrets) (labels : Labels) (L : LeafPos) (i : Nat) : Digest :=
  ChainGraph.value (seedsOf secrets) (chainLabels labels) ⟨L.lay, L.tree, L.leaf, fin58 i⟩ (maxDigit L.lay i)
def treeNodeAt (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option TreeNode :=
  if h : level < height lay ∧ c < 2 ^ (height lay - level - 1) then
    some ⟨⟨lay, tree, ⟨level, lt_of_lt_of_le h.1 (Extract.height_le lay)⟩,
      ⟨c, lt_of_lt_of_le h.2 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := Extract.height_le lay; omega)
          _ = 2048 := by norm_num)⟩⟩, h⟩
  else none
def treeLabel (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 4096 then (labels (.leaf ⟨lay, tree, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match treeNodeAt lay tree (level - 1) c with
    | some n => (labels (.node n)).extractLsb' 0 128
    | none => 0
def ftsNodeAt (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Option FtsNodePos :=
  if h : level < 11 ∧ c < 2 ^ (11 - level - 1) then
    some ⟨⟨index, coord, ⟨level, h.1⟩, ⟨c, lt_of_lt_of_le h.2 (by
      calc 2 ^ (11 - level - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 1024 := by norm_num)⟩⟩, h.2⟩
  else none
def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 2048 then (labels (.ftsLeaf ⟨index, coord, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match ftsNodeAt index coord (level - 1) c with
    | some n => (labels (.ftsNode n)).extractLsb' 0 128
    | none => 0
def cell (secrets : Secrets) : Node → Labels → HashInput
  | .chain p, labels => ChainGraph.input (seedsOf secrets) p (chainLabels labels)
  | .leaf L, labels => pad64 (Extract.leafInput L.lay L.tree.val L.leaf.val
      ((List.range (chainCount L.lay)).map (endLabel secrets labels L)))
  | .node n, labels => pad64 (nodeInputP 3 n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)) 0
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)))
  | .ftsLeaf f, _ => pad64 (ftsLeafInputP f.index.val f.coord.val f.leaf.val 0 (ftsOf secrets f) 0)
  | .ftsNode n, labels => pad64 (nodeInputP 10 n.1.coord.val n.1.index.val
      (2 ^ (11 - n.1.level.val - 1) + n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)) 0
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)))
  | .forest index, labels => pad64 (Extract.forestInput index.val
      ((List.range 7).map fun coord => ftsLabel labels index (fin7 coord) 11 0))
def treeBits (lay : Layer) : Nat := ![0, 12, 19, 25] lay
def LeafPos.Source (L : LeafPos) : Prop := L.tree.val < 2 ^ treeBits L.lay ∧ L.leaf.val < 2 ^ height L.lay
instance instDecidablePredLeafPosSource : DecidablePred LeafPos.Source := fun L => by unfold LeafPos.Source; infer_instance
def Node.toPos : Node → Extract.Pos
  | .chain p => .chain p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val
  | .leaf L => .leaf L.lay L.tree.val L.leaf.val
  | .node n => .node n.1.lay n.1.tree.val n.1.level.val n.1.idx.val
  | .ftsLeaf f => .ftsLeaf f.index.val f.coord.val f.leaf.val
  | .ftsNode n => .ftsNode n.1.index.val n.1.coord.val n.1.level.val n.1.idx.val
  | .forest index => .forest index.val
theorem height_pos (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide
def rootNode (lay : Layer) (tree : Fin (2^31)) : TreeNode :=
  ⟨⟨lay, tree, ⟨height lay - 1, by have := Extract.height_le lay; omega⟩, ⟨0, by decide⟩⟩,
    ⟨Nat.sub_lt (height_pos lay) Nat.one_pos, pow_pos (by decide : 0 < 2) _⟩⟩
def ftsRootNode (index : Fin (2^31)) (coord : Fin 7) : FtsNodePos :=
  ⟨⟨index, coord, ⟨10, by decide⟩, ⟨0, by decide⟩⟩, show 0 < 2 ^ (11 - 10 - 1) by decide⟩
theorem treeLabel_root (labels : Labels) (lay : Layer) (tree : Fin (2^31)) :
    treeLabel labels lay tree (height lay) 0 = (labels (.node (rootNode lay tree))).extractLsb' 0 128 := by
  have hpos := height_pos lay
  unfold treeLabel
  rw [if_neg (by omega)]
  have hv : height lay - 1 < height lay ∧ 0 < 2 ^ (height lay - (height lay - 1) - 1) :=
    ⟨by omega, pow_pos (by decide) _⟩
  unfold treeNodeAt
  rw [dif_pos hv]
  rfl
noncomputable def canonInputs : Finset HashInput :=
  (Finset.univ : Finset (Secrets × Labels × Node)).image fun x => cell x.1 x.2.2 x.2.1
attribute [irreducible] canonInputs
theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels ∈ canonInputs := by
  rw [canonInputs]
  exact Finset.mem_image.mpr ⟨(secrets, labels, node), Finset.mem_univ _, rfl⟩
noncomputable def cellIn (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (node : Node) (labels : Labels) : U :=
  ⟨cell secrets node labels, hU (cell_mem secrets node labels)⟩
noncomputable def order : List Node :=
  (Finset.univ : Finset Node).toList.mergeSort (fun left right => decide (left.depth ≤ right.depth))
attribute [irreducible] order
def advance (node : Node) (output : HashOutput) (labels : Labels) : Labels := Function.update labels node output
noncomputable def programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => cellIn U hU secrets node labels) labels residual order
def ftsCoordinate (f : FtsLeafPos) : ChainGraph.HalfCoordinate :=
  (.inl (header 8 f.coord.val f.index.val 0 (f.leaf.val / 2)), ⟨f.leaf.val % 2, Nat.mod_lt _ (by decide)⟩)
def secretCoordinate : SecretIndex → ChainGraph.HalfCoordinate := Sum.elim ChainGraph.seedCoordinate ftsCoordinate
theorem ftsCoordinate_injective : Function.Injective ftsCoordinate := by
  intro left right heq
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  change Sum.inl (header 8 left.coord.val left.index.val 0 (left.leaf.val / 2)) =
    (Sum.inl (header 8 right.coord.val right.index.val 0 (right.leaf.val / 2)) : Coordinate) at hp
  change left.leaf.val % 2 = right.leaf.val % 2 at hh
  have hl := left.coord.isLt
  have hr := right.coord.isLt
  have hlt := left.index.isLt
  have hrt := right.index.isLt
  have hli := left.leaf.isLt
  have hri := right.leaf.isLt
  have fields := header_injective (by decide : 8 < 256) (by omega) (by omega) (by omega) (by omega)
    (by decide : 8 < 256) (by omega) (by omega) (by omega) (by omega) (Sum.inl.inj hp)
  obtain ⟨index, coord, leaf⟩ := left
  obtain ⟨index', coord', leaf'⟩ := right
  simp only at fields hh
  have e1 : index = index' := Fin.ext fields.2.2.1
  have e2 : coord = coord' := Fin.ext fields.2.1
  have e3 : leaf = leaf' := Fin.ext (by have := fields.2.2.2.2; omega)
  rw [e1, e2, e3]
theorem secretCoordinate_injective : Function.Injective secretCoordinate := by
  intro left right heq
  cases left with
  | inl a =>
      cases right with
      | inl b => exact congrArg Sum.inl (ChainGraph.seedCoordinate_injective heq)
      | inr g =>
          exfalso
          have hp := congrArg Prod.fst heq
          change Sum.inl (header 0 a.layer.val a.tree.val (a.chain.val / 2) a.leaf.val) =
            (Sum.inl (header 8 g.coord.val g.index.val 0 (g.leaf.val / 2)) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (by decide) (Sum.inl.inj hp)
  | inr f =>
      cases right with
      | inl b =>
          exfalso
          have hp := congrArg Prod.fst heq
          change Sum.inl (header 8 f.coord.val f.index.val 0 (f.leaf.val / 2)) =
            (Sum.inl (header 0 b.layer.val b.tree.val (b.chain.val / 2) b.leaf.val) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (by decide) (Sum.inl.inj hp)
      | inr g => exact congrArg Sum.inr (ftsCoordinate_injective heq)
abbrev OtherHalf := {coordinate : ChainGraph.HalfCoordinate // coordinate ∉ Set.range secretCoordinate}
abbrev OtherHalves := OtherHalf → Digest
noncomputable def splitEquiv : ChainGraph.HalfTable ≃ Secrets × OtherHalves :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range secretCoordinate)).symm.trans
    ((Equiv.ofInjective secretCoordinate secretCoordinate_injective).symm.sumCongr (Equiv.refl OtherHalf)))
    (Equiv.refl Digest)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
noncomputable def privateEquiv : FullGame.FullTable ≃ Secrets × OtherHalves :=
  ChainGraph.halvesEquiv.trans splitEquiv
set_option warn.classDefReducibility false in
noncomputable def encodingKeyFintype : Fintype QuerySpace.EncodingKey := inferInstance
attribute [irreducible] encodingKeyFintype
noncomputable def encInputs : Finset HashInput :=
  (@Finset.univ _ encodingKeyFintype).image QuerySpace.encodingQuery
attribute [irreducible] encInputs
noncomputable def canonUniverse {α : Type} (program : M α) : Finset HashInput :=
  canonInputs ∪ encInputs ∪ ChainGraph.recordedInputs program
attribute [irreducible] canonUniverse
section PrivateLaws
noncomputable local instance instFintypeCoordinate_canonGraph : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_canonGraph : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeHashOutput_canonGraph_1 : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels_1 : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeOtherHalves : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdSecretsOtherHalves : SampleableType (Secrets × OtherHalves) := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
abbrev LowLabels := Node → Digest
noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => ChainGraph.joinOutput (low node) (high node)
theorem joinLabels_low (low high : LowLabels) (node : Node) :
    (joinLabels low high node).extractLsb' 0 128 = low node := ChainGraph.joinOutput_low _ _
noncomputable local instance instSampleableTypeLowLabels : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdLowLabels : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _
end PrivateLaws
noncomputable def eagerAnswers (privateTable : FullGame.FullTable) (U : Finset HashInput)
    (publicTable : U → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => finiteHashAnswer ∅ U publicTable input
  | .inr coordinate => privateTable coordinate
def ftsSecretOf (answers : Answers) (f : FtsLeafPos) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 f.coord.val f.index.val 0 (f.leaf.val / 2))
  if f.leaf.val % 2 = 0 then pair.1 else pair.2
def secretsOf (answers : Answers) : Secrets
  | .inl a => leafSeed answers a.layer a.tree.val a.leaf.val a.chain.val
  | .inr f => ftsSecretOf answers f
def Agrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ node, answers (.inl (.inr (cell (secretsOf answers) node labels))) = labels node
theorem agrees_chain {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    ChainGraph.Agrees answers (ChainGraph.sourceSeeds answers) (chainLabels labels) :=
  fun point => h (.chain point)
end SigGolfCandidate.T3.Security.CanonGraph
