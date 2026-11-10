import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import Batteries.Data.Fin.Coding
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.BitVec
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.DeriveFintype
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.ProgramLogic.Relational.ProgrammingOracle
import VCVio.ProgramLogic.Relational.Quantitative
import Mathlib.Tactic.IrreducibleDef
import VCVio.OracleComp.QueryTracking.WriterCost

-- ==== merged from SphincsSecurity_Compat ====
section

namespace OracleSpec.QueryCache
instance (priority := high) instLEExtension {ι : Type*} {spec : OracleSpec ι} :
    LE (QueryCache spec) :=
  @Preorder.toLE _ (@PartialOrder.toPreorder _ QueryCache.instPartialOrder)
end OracleSpec.QueryCache
end
-- ==== merged from SphincsSecurity_Scheme ====
section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 181
def numLayers : Nat := 5
def totalHeight : Nat := 34
def maxLayerHeight : Nat := 11
def ftsTreeHeight : Nat := 14
def ftsOpenings : Nat := 15
def ftsAuthCapacity : Nat := 118
def ftsSegments : Nat := 2 * ftsOpenings - 1
def signatureLimit : Nat := 2 ^ 32
def digestAttemptLimit : Nat := 2 ^ 20
def encodingAttemptLimit : Nat := 2 ^ 22
abbrev MasterSeed := BitVec 256
abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
abbrev Index := Fin (2 ^ totalHeight)
abbrev TreeIndex := Fin (2 ^ totalHeight)
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev FtsTree := Fin 1
abbrev IndexGroup := Fin ftsOpenings
abbrev SlotCode := Fin (ftsOpenings + 1)
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8
abbrev ChainPair := Fin (numChains / 2)
abbrev FtsPair := Fin (2 ^ (ftsTreeHeight - 1))
def evenChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val, by have := pair.isLt; unfold numChains at *; omega⟩
def oddChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val + 1, by have := pair.isLt; unfold numChains at *; omega⟩
def chainPairOf (chainIdx : ChainIndex) : ChainPair := ⟨chainIdx.val / 2, by have := chainIdx.isLt; unfold numChains at *; omega⟩
def evenFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
def oddFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val + 1, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
def ftsPairOf (leaf : FtsLeaf) : FtsPair := ⟨leaf.val / 2, by have := leaf.isLt; unfold ftsTreeHeight at *; omega⟩
def unpairChains {α : Type} (pairs : ChainPair → α × α) (chainIdx : ChainIndex) : α :=
  if chainIdx.val % 2 = 0 then (pairs (chainPairOf chainIdx)).1 else (pairs (chainPairOf chainIdx)).2
def unpairFtsLeaves {α : Type} (pairs : FtsPair → α × α) (leaf : FtsLeaf) : α :=
  if leaf.val % 2 = 0 then (pairs (ftsPairOf leaf)).1 else (pairs (ftsPairOf leaf)).2
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else if lay.val < 4 then 6 else 5
def topLayer : Layer := ⟨0, by decide⟩
def bottomLayer : Layer := ⟨numLayers - 1, by decide⟩
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits
def messageDigestBits : Nat := hashOutputBits
abbrev MessageDigest := BitVec messageDigestBits
def truncateMessageDigest (output : HashOutput) : MessageDigest :=
  output.extractLsb' 0 messageDigestBits
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq
structure Segment where
  folds : Fin 16
  merge : Bool
  parity : Bool
  nodes : Fin folds.val → Digest
  parity_normal : folds.val = 0 → parity = false
deriving DecidableEq
def Segment.normalized (folds : Fin 16) (merge parity : Bool) (nodes : Fin folds.val → Digest) : Segment :=
  ⟨folds, merge, parity && decide (folds.val ≠ 0), nodes, fun h => by simp [h]⟩
instance : Inhabited Segment := ⟨⟨0, false, false, fun index => index.elim0, fun _ => rfl⟩⟩
def Segment.node (segment : Segment) (i : Nat) : Digest :=
  if h : i < segment.folds.val then segment.nodes ⟨i, h⟩ else 0
structure FtsSignature where
  perm : Fin ftsOpenings → SlotCode
  secrets : Fin ftsOpenings → Digest
  segments : Fin ftsSegments → Segment
deriving DecidableEq
structure Signature where
  randomness : Randomness
  fts : FtsSignature
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)
structure TweakFields where
  tag : BitVec 8
  layer : BitVec 8
  tree : BitVec 40
  position : BitVec 32
  index : BitVec 32
deriving DecidableEq
def protocolDomainSep : UInt8 := 1
def fieldBytes (fields : TweakFields) : HashInput :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ bytesLE 1 fields.layer ++
    bytesLE 1 (fields.tree.extractLsb' 32 8) ++
    bytesLE 4 fields.position ++ bytesLE 4 (fields.tree.extractLsb' 0 32) ++ bytesLE 4 fields.index
def tweakFields (tag layer tree position index : Nat) : TweakFields :=
  ⟨BitVec.ofNat 8 tag, BitVec.ofNat 8 layer, BitVec.ofNat 40 tree,
    BitVec.ofNat 32 position, BitVec.ofNat 32 index⟩
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : Nat)
  | ftsNode (index : Index) (tree : FtsTree) (heapIdx : Nat)
  | message
deriving DecidableEq
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => tweakFields 1 lay tree (chainLength * chainIdx + step) leaf
  | .leaf lay tree leaf => tweakFields 2 lay tree 0 leaf
  | .node lay tree level nodeIdx => tweakFields 3 lay tree level nodeIdx
  | .encoding lay tree leaf => tweakFields 4 lay tree 0 leaf
  | .ftsLeaf index tree leaf => tweakFields 9 tree index 0 leaf
  | .ftsNode index tree heapIdx => tweakFields 10 tree index 0 heapIdx
  | .message => tweakFields 12 0 0 0 0
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : HashInput :=
  [1,7] ++ bytesLE 26 (seed.extractLsb' 0 208) ++ bytesLE 32 message ++ bytesLE 4 trial
inductive KeygenDomain where
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  | fts (index : Index) (tree : FtsTree) (pair : FtsPair)
  | mask (level : Fin maxLayerHeight) (nodeIdx : Fin (2 ^ maxLayerHeight))
deriving DecidableEq
def keygenDomainFields : KeygenDomain → TweakFields
  | .ots lay tree leaf pair => tweakFields 0 lay tree pair leaf
  | .fts index tree pair => tweakFields 8 tree index 0 pair
  | .mask level nodeIdx => tweakFields 13 0 0 level nodeIdx
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed
abbrev TopRegion := (level : Fin maxLayerHeight) → Fin (2 ^ (maxLayerHeight - level.val)) → Digest
structure TopCache where
  tag : HashOutput
  region : TopRegion
deriving DecidableEq
def TopCache.node (cache : TopCache) (level nodeIdx : Nat) : Digest :=
  if hlevel : level < maxLayerHeight then
    if hnode : nodeIdx < 2 ^ (maxLayerHeight - level) then cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnode⟩
    else 0
  else 0
def regionBytes (region : TopRegion) : HashInput :=
  (List.ofFn fun level : Fin maxLayerHeight => (List.ofFn (region level)).flatMap (bytesLE 16)).flatten
def macHashInput (parameter : PublicParameter) (seed : MasterSeed) (region : TopRegion) : HashInput :=
  fieldBytes ⟨14#8, 0#8, 0#40, 0#32, 0#32⟩ ++ bytesLE 16 parameter ++ bytesLE 32 seed ++ regionBytes region
namespace TargetSum
def sum (x : Encoding) : Nat := ∑ i, (x i).val
def Valid (x : Encoding) : Prop := sum x = targetSum
instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))
def digitsPerHalf : Nat := numChains / 2
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none
end TargetSum
abbrev HashSpec := HashInput →ₒ HashOutput
abbrev OracleWorld := unifSpec + HashSpec
namespace Concrete
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (totalHeight - heightAbove lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by
      unfold layerHeight maxLayerHeight; split <;> (try split) <;> omega))⟩
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (bytesLE 16 message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)
def porsTree : FtsTree := ⟨0, by decide⟩
def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def ftsHeapIndex (level nodeIdx : Nat) : Nat := 2 ^ (ftsTreeHeight - level) + nodeIdx
def ftsLeafHash (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : Nat)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (bytesLE 16 secret)
def foldPayload (right : Bool) (sibling current : Digest) : HashInput :=
  if right then nodePayload sibling current else nodePayload current sibling
def foldSegment (parameter : PublicParameter) (index : Index) (segment : Segment) :
    Nat → Nat → Digest → Nat → m (Digest × Nat)
  | 0, _, current, heap => pure (current, heap)
  | remaining + 1, position, current, heap => do
      let right := if position = 0 then segment.parity else decide (heap % 2 = 1)
      let parent ← tweakableHash parameter (.ftsNode index porsTree (heap / 2))
        (foldPayload right (segment.node position) current)
      foldSegment parameter index segment remaining (position + 1) parent (heap / 2)
inductive PendingHash where
  | leaf (value : Nat) (secret : Digest)
  | merge (heapIdx : Nat) (left : Digest)
structure RecoverState where
  node : Digest
  heap : Nat
  stack : List (Digest × Nat)
  folds : Nat
  segment : Nat
def RecoverState.initial : RecoverState := ⟨0, 0, [], 0, 0⟩
def recoverSegments (parameter : PublicParameter) (index : Index) (segments : Fin ftsSegments → Segment) :
    Nat → PendingHash → RecoverState → m (Option RecoverState)
  | 0, _, _ => pure none
  | fuel + 1, pending, state => do
      if hsegment : state.segment < ftsSegments then
        let segment := segments ⟨state.segment, hsegment⟩
        if ftsTreeHeight < segment.folds.val then
          return none
        else if segment.folds.val ≠ 0 ∧ segment.parity ≠ decide (state.heap % 2 = 1) then
          return none
        else
          let start ← match pending with
            | .leaf value secret => ftsLeafHash parameter index porsTree value secret
            | .merge heapIdx left =>
                tweakableHash parameter (.ftsNode index porsTree heapIdx) (nodePayload left state.node)
          let (node, heap) ← foldSegment parameter index segment segment.folds.val 0 start state.heap
          let state : RecoverState :=
            { state with node := node, heap := heap, folds := state.folds + segment.folds.val,
                         segment := state.segment + 1 }
          if segment.merge then
            match state.stack with
            | [] => return none
            | (left, sibling) :: rest =>
                if sibling = heap then
                  recoverSegments parameter index segments fuel (.merge (heap / 2) left)
                    { state with stack := rest, heap := heap / 2 }
                else
                  return none
          else
            return some state
      else
        return none
def recoverLeaves (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) : Nat → Nat → Nat → RecoverState → m (Option RecoverState)
  | 0, _, _, state => pure (some state)
  | remaining + 1, position, previous, state => do
      if hposition : position < ftsOpenings then
        let value := values (fts.perm ⟨position, hposition⟩)
        if 0 < position ∧ ¬ previous < value then
          return none
        else if position + 1 = ftsOpenings ∧ ¬ value < 2 ^ ftsTreeHeight then
          return none
        else
          let some state ← recoverSegments parameter index fts.segments ftsSegments
              (.leaf value (fts.secrets ⟨position, hposition⟩))
              { state with heap := 2 ^ ftsTreeHeight ||| value }
            | return none
          let state := if position + 1 < ftsOpenings then
              { state with stack := (state.node, state.heap ^^^ 1) :: state.stack } else state
          recoverLeaves parameter index values fts remaining (position + 1) value state
      else
        return none
def ftsRecover (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) : m (Option Digest) := do
  let some state ← recoverLeaves parameter index values fts ftsOpenings 0 0 RecoverState.initial
    | return none
  if state.folds ≤ ftsAuthCapacity ∧ state.heap = 1 ∧ state.stack = [] then
    return some state.node
  else
    return none
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 16 randomness ++ bytesLE 16 (0 : Digest) ++ bytesLE 32 message
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let output ← oracleHash
    (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest output
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin
def digestLeaves (digest : MessageDigest) : IndexGroup → FtsLeaf :=
  fun slot => (digest.extractLsb' (totalHeight + ftsTreeHeight * slot.val) ftsTreeHeight).toFin
def slotValue (leaves : IndexGroup → FtsLeaf) (code : SlotCode) : Nat :=
  if h : code.val < ftsOpenings then (leaves ⟨code.val, h⟩).val else 2 ^ ftsTreeHeight
def bitLength (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1
def octopusSize (sorted : List Nat) : Nat :=
  ftsTreeHeight + 2 + (List.zipWith (fun a b => bitLength (a ^^^ b)) sorted sorted.tail).sum -
    2 * sorted.length
def sortedSlots (leaves : IndexGroup → FtsLeaf) : List IndexGroup :=
  (List.finRange ftsOpenings).insertionSort fun r r' => (leaves r).val ≤ (leaves r').val
def sortedLeaves (leaves : IndexGroup → FtsLeaf) : List Nat :=
  (sortedSlots leaves).map fun r => (leaves r).val
def AdmissibleLeaves (leaves : IndexGroup → FtsLeaf) : Prop :=
  Function.Injective leaves ∧ octopusSize (sortedLeaves leaves) ≤ ftsAuthCapacity
instance (leaves : IndexGroup → FtsLeaf) : Decidable (AdmissibleLeaves leaves) :=
  inferInstanceAs (Decidable (Function.Injective leaves ∧ _))
def Admissible (digest : MessageDigest) : Prop := AdmissibleLeaves (digestLeaves digest)
instance (digest : MessageDigest) : Decidable (Admissible digest) :=
  inferInstanceAs (Decidable (AdmissibleLeaves (digestLeaves digest)))
structure ScheduleSegment where
  merge : Bool
  parity : Bool
  reads : List (Nat × Nat)
deriving DecidableEq, Inhabited
structure ScheduleState where
  done : List ScheduleSegment
  stack : List Nat
  heap : Nat
  parity : Bool
  reads : List (Nat × Nat)
def scheduleStep (state : ScheduleState) (height : Nat) : ScheduleState :=
  let fold : ScheduleState :=
    { state with reads := state.reads ++ [(height, (state.heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))],
                 heap := state.heap / 2 }
  match state.stack with
  | top :: rest =>
      if top = state.heap then
        { state with done := state.done ++ [⟨true, state.parity, state.reads⟩], stack := rest,
                     heap := state.heap / 2, parity := decide (state.heap / 2 % 2 = 1), reads := [] }
      else fold
  | [] => fold
def scheduleLeaves : List Nat → ScheduleState → ScheduleState
  | [], state => state
  | v :: rest, state =>
      let heap := 2 ^ ftsTreeHeight ||| v
      let top := match rest with
        | [] => ftsTreeHeight
        | w :: _ => bitLength (v ^^^ w) - 1
      let state := (List.range top).foldl scheduleStep
        { state with heap := heap, parity := decide (heap % 2 = 1), reads := [] }
      let state := { state with done := state.done ++ [⟨false, state.parity, state.reads⟩] }
      scheduleLeaves rest (match rest with
        | [] => state
        | _ :: _ => { state with stack := (state.heap ^^^ 1) :: state.stack })
def schedule (sorted : List Nat) : List ScheduleSegment :=
  (scheduleLeaves sorted ⟨[], [], 0, false, []⟩).done
def ScheduleSegment.folds (segment : ScheduleSegment) : Fin 16 :=
  ⟨segment.reads.length % 16, Nat.mod_lt _ (by decide)⟩
def ScheduleSegment.byte (segment : ScheduleSegment) : Nat :=
  segment.reads.length + 16 * (if segment.merge then 1 else 0) + 32 * (if segment.parity then 1 else 0)
def ScheduleSegment.toSegment (segment : ScheduleSegment) (nodes : Fin segment.folds.val → Digest) :
    Segment :=
  Segment.normalized segment.folds segment.merge segment.parity nodes
def honestFts (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest) :
    FtsSignature :=
  let slots := sortedSlots leaves
  let segments := schedule (sortedLeaves leaves)
  { perm := fun s => (slots.getD s.val ⟨0, by decide⟩).castSucc
    secrets := fun s => secret (leaves (slots.getD s.val ⟨0, by decide⟩))
    segments := fun j =>
      let segment := segments.getD j.val default
      segment.toSegment fun i =>
        let position := segment.reads.getD i.val (0, 0)
        node position.1 position.2 }
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        verifyLayers parameter index signature remaining root
      else
        pure none
def CountersInRange (signature : Signature) : Prop :=
  ∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit
instance (signature : Signature) : Decidable (CountersInRange signature) :=
  inferInstanceAs (Decidable (∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit))
def verifyCore (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let some ftsPublicKey ← ftsRecover publicKey.parameter index (slotValue (digestLeaves digest))
      signature.fts
    | return false
  let some root ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey | return false
  return decide (root = publicKey.root)
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool :=
  if CountersInRange signature then verifyCore publicKey message signature else pure false
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩
def buildLevel (hashNode : Nat → Digest → Digest → m Digest) (width : Nat) (below : Nat → Digest) :
    m (Nat → Digest) := do
  let row ← sequenceFin (n := width) fun nodeIdx =>
    hashNode nodeIdx.val (below (2 * nodeIdx.val)) (below (2 * nodeIdx.val + 1))
  return fun nodeIdx => if h : nodeIdx < width then row ⟨nodeIdx, h⟩ else 0
def buildLevels (hashNode : Nat → Nat → Digest → Digest → m Digest) (height : Nat)
    (leaves : Nat → Digest) : Nat → m (Nat → Nat → Digest)
  | 0 => pure fun _ nodeIdx => leaves nodeIdx
  | levels + 1 => do
      let table ← buildLevels hashNode height leaves levels
      let row ← buildLevel (hashNode (levels + 1)) (2 ^ (height - (levels + 1))) (table levels)
      return fun level nodeIdx => if level = levels + 1 then row nodeIdx else table level nodeIdx
def zeroEncoding : Encoding := fun _ => ⟨0, by decide⟩
def buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (secret : m Digest) (digit : Nat) : m (Digest × Digest) := do
  let start ← secret
  let value ← chainWalk parameter lay tree leaf chainIdx 0 digit start
  let endpoint ← chainWalk parameter lay tree leaf chainIdx digit (chainLength - 1 - digit) value
  return (value, endpoint)
def buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → m Digest) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let chains ← sequenceFin fun chainIdx =>
    buildChain parameter lay tree leaf chainIdx (secret chainIdx) (digits chainIdx).val
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)
def buildLayerTable (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)
def buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)
def buildFtsTree (parameter : PublicParameter) (index : Index) (secret : FtsLeaf → m Digest) :
    m ((FtsLeaf → Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin fun leafIdx : FtsLeaf => do
    let value ← secret leafIdx
    let hashed ← ftsLeafHash parameter index porsTree leafIdx.val value
    return (value, hashed)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx)) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return (fun leafIdx => (leaves leafIdx).1, table)
def encodingSearch (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : Nat → Nat → m (Option (Counter × Encoding))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => return some (BitVec.ofNat counterBits counter, encoding)
      | none => encodingSearch parameter lay tree leaf message attempts (counter + 1)
abbrev LayerOutput := Counter × (ChainIndex → Digest) × (Nat → Digest)
def signTopLayer (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let values ← sequenceFin fun chainIdx => do
    let start ← secret leaf chainIdx
    chainWalk parameter topLayer tree leaf chainIdx 0 (encoding chainIdx).val start
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)
def signLayers (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayer parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTree parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayers parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none
def LayerOutput.toSignature (lay : Layer) (output : LayerOutput) : LayerSignature lay :=
  ⟨output.1, output.2.1, fun level => output.2.2 level.val⟩
def signFrom (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → m Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest)
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, table) ← buildFtsTree parameter index (ftsSecret porsTree)
  let some parts ← signLayers parameter index otsSecret topNode numLayers (table ftsTreeHeight 0)
    | return none
  return some ⟨randomness, honestFts leaves secrets table,
    fun lay => LayerOutput.toSignature lay (parts lay)⟩
attribute [irreducible] verify
def buildLeafPaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainPair → m (Digest × Digest)) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret pair
    let first ← buildChain parameter lay tree leaf (evenChain pair) (pure secrets.1) (digits (evenChain pair)).val
    let second ← buildChain parameter lay tree leaf (oddChain pair) (pure secrets.2) (digits (oddChain pair)).val
    return (first, second)
  let chains := unpairChains pairs
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)
def buildLayerTablePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeafPaired parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)
def buildLayerTreePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let (leaves, table) ← buildLayerTablePaired parameter lay tree secret leaf digits
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)
def buildFtsTreePaired (parameter : PublicParameter) (index : Index)
    (secret : FtsPair → m (Digest × Digest)) : m ((FtsLeaf → Digest) × (Nat → Nat → Digest)) := do
  let pairs ← sequenceFin fun pair : FtsPair => do
    let secrets ← secret pair
    let first ← ftsLeafHash parameter index porsTree (evenFtsLeaf pair).val secrets.1
    let second ← ftsLeafHash parameter index porsTree (oddFtsLeaf pair).val secrets.2
    return ((secrets.1, first), (secrets.2, second))
  let leaves := unpairFtsLeaves pairs
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx)) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return (fun leafIdx => (leaves leafIdx).1, table)
def signTopLayerPaired (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret leaf pair
    let first ← chainWalk parameter topLayer tree leaf (evenChain pair) 0 (encoding (evenChain pair)).val secrets.1
    let second ← chainWalk parameter topLayer tree leaf (oddChain pair) 0 (encoding (oddChain pair)).val secrets.2
    return (first, second)
  let values := unpairChains pairs
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)
def signLayersPaired (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayerPaired parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTreePaired parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayersPaired parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none
def signFromPaired (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsPair → m (Digest × Digest))
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest))
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, table) ← buildFtsTreePaired parameter index (ftsSecret porsTree)
  let some parts ← signLayersPaired parameter index otsSecret topNode numLayers (table ftsTreeHeight 0)
    | return none
  return some ⟨randomness, honestFts leaves secrets table,
    fun lay => LayerOutput.toSignature lay (parts lay)⟩
end Concrete
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))
def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (randomizerHashInput parameter seed message trial))
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  $ᵗ MasterSeed
namespace Seeded
open Concrete
structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
def splitSecrets (output : HashOutput) : Digest × Digest :=
  (truncateHash output, output.extractLsb' digestBits digestBits)
def otsSecret (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (pair : ChainPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.ots lay tree leaf pair) seed))
def ftsSecret (parameter : PublicParameter) (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (pair : FtsPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.fts index tree pair) seed))
def maskDomain (level nodeIdx : Nat) : KeygenDomain :=
  .mask ⟨level % maxLayerHeight, Nat.mod_lt _ (by decide)⟩ ⟨nodeIdx % 2 ^ maxLayerHeight, Nat.mod_lt _ (by decide)⟩
def maskSecret (parameter : PublicParameter) (seed : MasterSeed) (level nodeIdx : Nat) : m Digest :=
  deriveKey parameter (maskDomain level nodeIdx) seed
def maskRegion (parameter : PublicParameter) (seed : MasterSeed) (table : Nat → Nat → Digest) :
    m TopRegion :=
  do
  let rows ← sequenceFin fun level : Fin maxLayerHeight => do
    let row ← sequenceFin fun nodeIdx : Fin (2 ^ (maxLayerHeight - level.val)) => do
      let mask ← maskSecret parameter seed level.val nodeIdx.val
      return table level.val nodeIdx.val ^^^ mask
    return fun nodeIdx : Nat => if h : nodeIdx < 2 ^ (maxLayerHeight - level.val) then row ⟨nodeIdx, h⟩ else 0
  return fun level nodeIdx => rows level nodeIdx.val
def cachedTopNode (parameter : PublicParameter) (seed : MasterSeed) (cache : TopCache) (level nodeIdx : Nat) :
    m Digest := do
  let mask ← maskSecret parameter seed level nodeIdx
  return cache.node level nodeIdx ^^^ mask
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × TopCache × SecretKey) := do
  let (_, table) ← buildLayerTablePaired 0 topLayer rootTree (otsSecret 0 seed topLayer rootTree)
    ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  let root := table (layerHeight topLayer) 0
  let region ← maskRegion 0 seed table
  let tag ← oracleHash (macHashInput 0 seed region)
  return (⟨root, 0⟩, ⟨tag, region⟩, ⟨seed, 0, root⟩)
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none
def signDigestLoop (secretKey : SecretKey) (message : Message) : Nat → Nat →
    m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)
      match ← signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => signDigestLoop secretKey message attempts (trial + 1)
def signChecked (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let some (randomness, index, leaves) ← signDigestLoop secretKey message digestAttemptLimit 0
    | return none
  signFromPaired secretKey.parameter index (ftsSecret secretKey.parameter secretKey.seed index)
    (otsSecret secretKey.parameter secretKey.seed)
    (cachedTopNode secretKey.parameter secretKey.seed cache) randomness leaves
def sign (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let tag ← oracleHash (macHashInput secretKey.parameter secretKey.seed cache.region)
  if tag = cache.tag then signChecked secretKey cache message else return none
end Seeded
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Base_Prelude ====
section

end
-- ==== merged from SphincsSecurity_Proof_Ots_Code ====
section

namespace SphincsSecurity
namespace OtsCode
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
irreducible_def Valid (x : Encoding) : Prop := TargetSum.Valid x
irreducible_def decode (digest : Digest) : Option Encoding := TargetSum.decodeDigest digest
theorem decode_valid {digest : Digest} {word : Encoding} (hdecode : decode digest = some word) : Valid word := by
  rw [decode_def] at hdecode
  rw [Valid_def]
  by_cases hvalid : digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ TargetSum.Valid (TargetSum.digestEncoding digest)
  · rw [TargetSum.decodeDigest, if_pos hvalid] at hdecode
    exact Option.some.inj hdecode ▸ hvalid.2.2
  · rw [TargetSum.decodeDigest, if_neg hvalid] at hdecode
    simp at hdecode
private theorem digest_eq_of_encoding_eq_of_padding {left right : Digest}
    (hencoding : TargetSum.digestEncoding left = TargetSum.digestEncoding right)
    (hleft63 : left.getLsbD 63 = false) (hleft127 : left.getLsbD 127 = false)
    (hright63 : right.getLsbD 63 = false) (hright127 : right.getLsbD 127 = false) :
    left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  by_cases hlow : bit < 63
  · let chainIdx : ChainIndex := ⟨bit / 3, by
      have : bit / 3 < 21 := by omega
      exact lt_of_lt_of_le this (by decide)⟩
    have hchain := congrFun hencoding chainIdx
    change (left.extractLsb' (TargetSum.digitOffset chainIdx) winternitzBits).toFin =
      (right.extractLsb' (TargetSum.digitOffset chainIdx) winternitzBits).toFin at hchain
    have hword := BitVec.toFin_injective hchain
    have hchainVal : chainIdx.val = bit / 3 := rfl
    have hoffset : TargetSum.digitOffset chainIdx = 3 * chainIdx.val := by
      rw [TargetSum.digitOffset, if_pos]
      · norm_num [winternitzBits]
      · rw [hchainVal]
        norm_num [TargetSum.digitsPerHalf, numChains]
        omega
    have hwithin : bit - 3 * chainIdx.val < winternitzBits := by
      dsimp only [chainIdx]
      norm_num [winternitzBits]
      omega
    have hbitEq := congrArg (fun word : BitVec winternitzBits =>
      word.getLsbD (bit - 3 * chainIdx.val)) hword
    simpa only [TargetSum.digestEncoding, BitVec.getLsbD_extractLsb', hwithin, decide_true,
      Bool.true_and, hoffset, show 3 * chainIdx.val + (bit - 3 * chainIdx.val) = bit by
        dsimp only [chainIdx]
        omega] using hbitEq
  · by_cases hpad : bit = 63
    · subst bit
      rw [hleft63, hright63]
    · by_cases hhigh : bit < 127
      · let chainIdx : ChainIndex := ⟨21 + (bit - 64) / 3, by
          have hbit64 : 64 ≤ bit := by omega
          have : (bit - 64) / 3 < 21 := by omega
          norm_num [numChains]
          omega⟩
        have hchain := congrFun hencoding chainIdx
        change (left.extractLsb' (TargetSum.digitOffset chainIdx) winternitzBits).toFin =
          (right.extractLsb' (TargetSum.digitOffset chainIdx) winternitzBits).toFin at hchain
        have hword := BitVec.toFin_injective hchain
        have hchainVal : chainIdx.val = 21 + (bit - 64) / 3 := rfl
        have hoffset : TargetSum.digitOffset chainIdx = 64 + 3 * ((bit - 64) / 3) := by
          rw [TargetSum.digitOffset, if_neg (by rw [hchainVal]; norm_num [TargetSum.digitsPerHalf, numChains])]
          rw [hchainVal]
          norm_num [winternitzBits]
          omega
        have hwithin : bit - (64 + 3 * ((bit - 64) / 3)) < winternitzBits := by
          norm_num [winternitzBits]
          omega
        have hbitEq := congrArg (fun word : BitVec winternitzBits =>
          word.getLsbD (bit - (64 + 3 * ((bit - 64) / 3)))) hword
        simpa only [TargetSum.digestEncoding, BitVec.getLsbD_extractLsb', hwithin, decide_true,
          Bool.true_and, hoffset,
          show 64 + 3 * ((bit - 64) / 3) +
              (bit - (64 + 3 * ((bit - 64) / 3))) = bit by omega] using hbitEq
      · have : bit = 127 := by
          have := hbit
          norm_num [digestBits] at this
          omega
        subst bit
        rw [hleft127, hright127]
theorem decode_some_injective {left right : Digest} {word : Encoding}
    (hleft : decode left = some word) (hright : decode right = some word) : left = right := by
  rw [decode_def, TargetSum.decodeDigest] at hleft hright
  split at hleft <;> split at hright
  · rename_i hleftValid hrightValid
    exact digest_eq_of_encoding_eq_of_padding (Option.some.inj hleft |>.trans
      (Option.some.inj hright).symm) hleftValid.1 hleftValid.2.1
      hrightValid.1 hrightValid.2.1
  all_goals simp at hleft hright
theorem eq_of_le_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y := by
  rw [Valid_def] at hx hy
  have hsum : TargetSum.sum x = TargetSum.sum y := hx.trans hy.symm
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hlt
  have hstrict : (x i).val < (y i).val := by omega
  have : TargetSum.sum x < TargetSum.sum y :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega
irreducible_def defaultWord : Encoding :=
  fun index => if index.val < 25 then ⟨7, by decide⟩ else if index.val = 25 then ⟨6, by decide⟩ else ⟨0, by decide⟩
theorem defaultWord_valid : Valid defaultWord := by
  rw [Valid_def]
  change (∑ index : ChainIndex, (defaultWord index).val) = 181
  simp only [defaultWord_def]
  change (∑ index : Fin 42, if index.val < 25 then (7 : Nat) else if index.val = 25 then 6 else 0) = 181
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
def signingSteps (word : Encoding) : Nat := ∑ index, (word index).val
def UnitNeighborAt (reference candidate : Encoding) (lowered : ChainIndex) : Prop :=
  Valid reference ∧ Valid candidate ∧ (candidate lowered).val + 1 = (reference lowered).val ∧
    ∀ index, index ≠ lowered → (reference index).val ≤ (candidate index).val
theorem UnitNeighborAt.ne {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) : candidate ≠ reference := by
  intro he
  have hd := h.2.2.1
  rw [he] at hd
  omega
theorem UnitNeighborAt.lowered_unique {reference candidate : Encoding} {left right : ChainIndex}
    (hleft : UnitNeighborAt reference candidate left) (hright : UnitNeighborAt reference candidate right) : left = right := by
  by_contra hne
  have hle := hleft.2.2.2 right (Ne.symm hne)
  have hd := hright.2.2.1
  omega
noncomputable def unitNeighbors (reference : Encoding) (lowered : ChainIndex) : Finset Encoding :=
  Finset.univ.filter (fun candidate => UnitNeighborAt reference candidate lowered)
theorem mem_unitNeighbors {reference candidate : Encoding} {lowered : ChainIndex} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered := by
  simp only [unitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
noncomputable def allUnitNeighbors (reference : Encoding) : Finset Encoding :=
  Finset.univ.biUnion (unitNeighbors reference)
theorem mem_allUnitNeighbors {reference candidate : Encoding} :
    candidate ∈ allUnitNeighbors reference ↔ ∃ lowered, UnitNeighborAt reference candidate lowered := by
  simp only [allUnitNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_unitNeighbors]
irreducible_def unitNeighborBound : Nat := numChains - 1
irreducible_def neighborBound : Nat := numChains * (numChains - 1)
private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h
private theorem single_of_sum_one (f : ChainIndex → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, fun other hne => ?_⟩
  have hpair := two_terms_le_sum f hne
  omega
private theorem UnitNeighborAt.raised {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) :
    ∃ raised, raised ≠ lowered ∧ (reference raised).val + 1 = (candidate raised).val ∧
      ∀ index, index ≠ lowered → index ≠ raised → candidate index = reference index := by
  obtain ⟨hreference, hcandidate, hlow, hup⟩ := h
  rw [Valid_def] at hreference hcandidate
  have hpoint : ∀ index : ChainIndex,
      ((reference index).val - (candidate index).val) + (candidate index).val =
        ((candidate index).val - (reference index).val) + (reference index).val := fun index => by omega
  have hsum := congrArg (fun f : ChainIndex → Nat => ∑ index, f index) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hback : ∑ index, ((reference index).val - (candidate index).val) = 1 := by
    rw [Finset.sum_eq_single lowered]
    · omega
    · intro index _ hne
      have := hup index hne
      omega
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  change _ + TargetSum.sum candidate = _ + TargetSum.sum reference at hsum
  have hsums : TargetSum.sum candidate = TargetSum.sum reference := hcandidate.trans hreference.symm
  have hforward : ∑ index, ((candidate index).val - (reference index).val) = 1 := by omega
  obtain ⟨raised, hraise, hothers⟩ := single_of_sum_one _ hforward
  refine ⟨raised, fun he => ?_, by omega, fun index hl hr => ?_⟩
  · subst raised
    omega
  · have hdown := hothers index hr
    have hle := hup index hl
    apply Fin.ext
    omega
theorem unitNeighbors_card_le (reference : Encoding) (lowered : ChainIndex) :
    (unitNeighbors reference lowered).card ≤ unitNeighborBound := by
  let chooseRaised : {candidate // UnitNeighborAt reference candidate lowered} → {raised : ChainIndex // raised ≠ lowered} :=
    fun candidate => ⟨candidate.property.raised.choose, candidate.property.raised.choose_spec.1⟩
  have hinj : Function.Injective chooseRaised := by
    intro left right he
    apply Subtype.ext
    have he' : left.property.raised.choose = right.property.raised.choose := congrArg Subtype.val he
    obtain ⟨_, hup, hrest⟩ := left.property.raised.choose_spec
    obtain ⟨_, hup', hrest'⟩ := right.property.raised.choose_spec
    rw [he'] at hup hrest
    funext index
    by_cases hl : index = lowered
    · subst index
      apply Fin.ext
      have := left.property.2.2.1
      have := right.property.2.2.1
      omega
    · by_cases hr : index = right.property.raised.choose
      · subst index
        apply Fin.ext
        omega
      · exact (hrest index hl hr).trans (hrest' index hl hr).symm
  have hcard := Fintype.card_le_of_injective chooseRaised hinj
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  have hr : (Finset.univ.filter fun raised : ChainIndex => raised ≠ lowered) = Finset.univ.erase lowered := by
    ext raised
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hr, Finset.card_erase_of_mem (Finset.mem_univ lowered), Finset.card_univ, Fintype.card_fin] at hcard
  rw [unitNeighborBound_def]
  simpa only [unitNeighbors] using hcard
theorem allUnitNeighbors_card_le (reference : Encoding) : (allUnitNeighbors reference).card ≤ neighborBound := by
  calc
    _ ≤ ∑ lowered : ChainIndex, (unitNeighbors reference lowered).card := Finset.card_biUnion_le
    _ ≤ ∑ _lowered : ChainIndex, unitNeighborBound :=
      Finset.sum_le_sum fun lowered _ => unitNeighbors_card_le reference lowered
    _ = neighborBound := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, neighborBound_def,
        unitNeighborBound_def]
theorem unitNeighborBound_eq : unitNeighborBound = 41 := by
  rw [unitNeighborBound_def]
  rfl
theorem neighborBound_eq : neighborBound = 1722 := by
  rw [neighborBound_def]
  rfl
theorem two_le_chainLength : 2 ≤ chainLength := by decide
theorem two_le_numChains : 2 ≤ numChains := by decide
theorem chainTweakPosition_lt (chainIdx : ChainIndex) (step : ChainStep) :
    chainLength * chainIdx.val + step.val < 2 ^ 32 := by
  have := chainIdx.isLt
  have := step.isLt
  simp only [numChains, chainLength, winternitzBits] at *
  omega
theorem chainTweakPosition_injective {left right : ChainIndex} {leftStep rightStep : ChainStep}
    (h : chainLength * left.val + leftStep.val = chainLength * right.val + rightStep.val) :
    left = right ∧ leftStep = rightStep := by
  have := leftStep.isLt
  have := rightStep.isLt
  simp only [chainLength, winternitzBits] at *
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
end OtsCode
namespace Concrete
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
abbrev counterBytes (counter : Counter) : HashInput := bytesLE 4 counter
def encodeAttempt (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf) (bytesLE 16 message ++ counterBytes counter)
  return OtsCode.decode digest
def otsLeafAttempt (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encodeAttempt parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value
theorem encode_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    encode (m := m) parameter lay tree leaf message counter = encodeAttempt parameter lay tree leaf message counter := by
  simp only [encode, encodeAttempt, OtsCode.decode_def]
theorem otsLeaf_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    otsLeaf (m := m) parameter lay tree leaf message counter values =
      otsLeafAttempt parameter lay tree leaf message counter values := by
  simp only [otsLeaf, otsLeafAttempt, encode_eq]
  try (apply bind_congr
       intro result
       cases result <;> rfl)
end Concrete
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_SignatureLayout ====
section

section
namespace SphincsSecurity.Concrete
open ENNReal
irreducible_def ftsOpenHashCost : Nat := 2 ^ (ftsTreeHeight + 1) - 1
irreducible_def ftsKeyHashCost : Nat := 2 ^ (ftsTreeHeight + 1) - 1
theorem two_pow_ftsTreeHeight_le_ftsOpenHashCost : 2 ^ ftsTreeHeight ≤ ftsOpenHashCost := by
  rw [ftsOpenHashCost_def]
  decide
theorem ftsOpenHashCost_le_digestAttemptLimit : ftsOpenHashCost ≤ digestAttemptLimit := by
  rw [ftsOpenHashCost_def]
  decide
irreducible_def fixedProposalLength : Nat := 6455164942
irreducible_def proposalPrefixSlack : Nat := 2 ^ 23
noncomputable irreducible_def fullCertificateExcessRate : ENNReal := 1 / 2 ^ 144
noncomputable irreducible_def nearCertificatePrice : ENNReal := ((1241 : ENNReal) / 15) / (2 ^ 128 : Nat)
noncomputable irreducible_def proposalPrefixExceptionBound : ENNReal := (2 ^ 700 : ENNReal)⁻¹
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
irreducible_def oneTimeKeyHashCost : Nat := numChains * (chainLength - 1)
irreducible_def treeNodeHashCost (level : Nat) : Nat := (oneTimeKeyHashCost + 2) * 2 ^ level - 1
irreducible_def keygenHashCost : Nat := treeNodeHashCost (layerHeight topLayer)
theorem treeNodeHashCost_zero : treeNodeHashCost 0 = oneTimeKeyHashCost + 1 := by
  rw [treeNodeHashCost_def, pow_zero, mul_one]
  omega
theorem treeNodeHashCost_succ (level : Nat) :
    treeNodeHashCost (level + 1) = treeNodeHashCost level + (treeNodeHashCost level + 1) := by
  simp only [treeNodeHashCost_def, pow_succ, ← mul_assoc]
  have hpos : 0 < (oneTimeKeyHashCost + 2) * 2 ^ level := by positivity
  generalize (oneTimeKeyHashCost + 2) * 2 ^ level = nodes at hpos ⊢
  omega
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open ENNReal
irreducible_def budgetSplit : Nat := 3 * 2 ^ 114
noncomputable irreducible_def primitiveCoefficient : ENNReal := 7 / 4
theorem budgetSplit_le : budgetSplit ≤ 2 ^ 127 := by
  rw [budgetSplit_def]
  norm_num
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity
theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight maxLayerHeight
  split <;> (try split) <;> omega
abbrev Signature.counter (signature : Signature) (lay : Layer) : Counter :=
  (signature.layers lay).counter
abbrev Signature.chainValue (signature : Signature) (lay : Layer) : ChainIndex → Digest :=
  (signature.layers lay).chainValues
abbrev PaddedLayer := Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)
abbrev LayerSignature.ofPadded (lay : Layer) (part : PaddedLayer) : LayerSignature lay :=
  ⟨part.1, part.2.1, fun level => part.2.2 (level.castLE (layerHeight_le lay))⟩
@[ext]
theorem LayerSignature.ext {lay : Layer} {left right : LayerSignature lay}
    (hcounter : left.counter = right.counter) (hvalues : left.chainValues = right.chainValues)
    (hpath : left.path = right.path) : left = right := by
  cases left
  cases right
  simp_all
end SphincsSecurity
end
end
-- ==== merged from SphincsSecurity_Proof_RandomizedStatement ====
section

section
open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq
abbrev SigningSpec := Message →ₒ Option Signature
structure SigningRequest where
  message : Message
  cache : TopCache
deriving DecidableEq
abbrev RequestSpec := SigningRequest →ₒ Option Signature
namespace SigningTranscript
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit
instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature
instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))
end SigningTranscript
namespace RequestTranscript
def Valid (log : QueryLog RequestSpec) : Prop := log.length ≤ signatureLimit
instance (log : QueryLog RequestSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))
def Contains (log : QueryLog RequestSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature
instance (log : QueryLog RequestSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature))
end RequestTranscript
namespace Security
structure Adversary where
  main : PublicKey → TopCache → OracleComp (OracleWorld + RequestSpec) Forgery
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl RequestSpec (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request.cache request.message : OracleComp HashSpec _)
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, cache, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog RequestSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) + signingOracle sk) (adversary.main pk cache)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (RequestTranscript.Valid log ∧ ¬RequestTranscript.Contains log forgery) && verified
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)
end Security
abbrev SphincsSecurityStatement : Prop := Security.HasClassicalSecurityBits 127
end SphincsSecurity
end
section
open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
namespace Concrete
abbrev digestBytes (value : Digest) : HashInput := bytesLE 16 value
abbrev messageBytes (message : Message) : HashInput := bytesLE 32 message
abbrev randomnessBytes (randomness : Randomness) : HashInput := bytesLE 16 randomness
end Concrete
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
structure Scheme (Key : Type := Seeded.SecretKey) where
  keygen : OracleComp OracleWorld (PublicKey × Key)
  sign : Key → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp OracleWorld Bool
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery
def signingOracle {Key : Type} (scheme : Scheme Key) (sk : Key) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)
noncomputable def Seeded.gameRest {Key : Type} (randomizedScheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle randomizedScheme sk) (adversary.main pk)).run
  let verified ← randomizedScheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified
noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  Seeded.gameRest scheme adversary pk sk
noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]
noncomputable def countedRomImpl :=
  romImpl.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)
def HasHashQueryBound {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅),
    result.2 ≤ q
def HasClassicalSecurityBits {Key : Type} (scheme : Scheme Key) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)
end SphincsSecurity
end
end
-- ==== merged from SphincsSecurity_Proof_IdealStatement ====
section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
structure SecretKey where
  parameter : PublicParameter
  root : Digest
  otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest
  ftsSecret : Index → FtsTree → FtsLeaf → Digest
  top : Nat → Nat → Digest
namespace Concrete
noncomputable opaque randomnessSampleableType : SampleableType Randomness :=
  SampleableType.ofFintype Randomness
noncomputable local instance : SampleableType Randomness := randomnessSampleableType
noncomputable def sampleRandomness : ProbComp Randomness :=
  $ᵗ Randomness
attribute [irreducible] sampleRandomness
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter
noncomputable opaque otsSecretsSampleableType :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
noncomputable local instance :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  otsSecretsSampleableType
noncomputable opaque ftsSecretsSampleableType :
    SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  SampleableType.ofFintype (Index → FtsTree → FtsLeaf → Digest)
noncomputable local instance : SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  ftsSecretsSampleableType
def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)
def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secret chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf secret message attempts (counter + 1)
def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf secret message encodingAttemptLimit 0
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf (secret leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
      let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : m Digest :=
  treeNode parameter lay tree secret (layerHeight lay) 0
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) : m (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      treeNode parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      pure 0
def ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      ftsLeafHash parameter index tree leaf.val (secret leaf)
  | level + 1, nodeIdx => do
      let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
      let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx))
        (nodePayload left right)
def ftsKey (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) : m Digest :=
  ftsNode parameter index porsTree (secret porsTree) ftsTreeHeight 0
def ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) : m FtsSignature := do
  let slots := sortedSlots leaves
  let plan := schedule (sortedLeaves leaves)
  let segments ← sequenceFin fun j : Fin ftsSegments => do
    let segment := plan.getD j.val default
    let nodes ← sequenceFin (n := segment.folds.val) fun i =>
      let position := segment.reads.getD i.val (0, 0)
      ftsNode parameter index porsTree (secret porsTree) position.1 position.2
    return segment.toSegment nodes
  return { perm := fun s => (slots.getD s.val ⟨0, by decide⟩).castSucc
           secrets := fun s => secret porsTree (leaves (slots.getD s.val ⟨0, by decide⟩))
           segments := segments }
noncomputable def sampleParameter : ProbComp PublicParameter :=
  pure 0
noncomputable def sampleOtsSecrets :
    ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  $ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
noncomputable def sampleFtsSecrets : ProbComp (Index → FtsTree → FtsLeaf → Digest) :=
  $ᵗ (Index → FtsTree → FtsLeaf → Digest)
def keygenRoot (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) : m Digest := do
  let (_, _, root) ← buildLayerTree parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return root
def keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    m (Nat → Nat → Digest) := do
  let (_, table) ← buildLayerTable parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return table
noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  let top ← liftM
    (keygenTable parameter (otsSecret topLayer rootTree) : OracleComp HashSpec (Nat → Nat → Digest))
  let root := top (layerHeight topLayer) 0
  return (⟨root, parameter⟩, ⟨parameter, root, otsSecret, ftsSecret, top⟩)
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none
noncomputable def signDigestLoop : Nat → SecretKey → Message →
    OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _secretKey, _message => pure none
  | attempts + 1, secretKey, message => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM
        (signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))
      match attempt with
      | some (index, leaves) => pure (some (randomness, index, leaves))
      | none => signDigestLoop attempts secretKey message
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    treeRoot secretKey.parameter below (treeIndexAt index below)
      (secretKey.otsSecret below (treeIndexAt index below))
  else
    ftsKey secretKey.parameter index (secretKey.ftsSecret index)
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  match ← otsSign secretKey.parameter lay tree leaf (secretKey.otsSecret lay tree leaf) message with
  | none => return none
  | some (counter, values) => do
      let path ← treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leaf
      return some (counter, values, path)
def signAfterDigest (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : OracleComp HashSpec (Option Signature) :=
  signFrom secretKey.parameter index (fun tree leaf => pure (secretKey.ftsSecret index tree leaf))
    (fun lay tree leaf chainIdx => pure (secretKey.otsSecret lay tree leaf chainIdx))
    (fun level nodeIdx => pure (secretKey.top level nodeIdx)) randomness leaves
noncomputable def sign (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => return none
  | some (randomness, index, leaves) =>
      liftM (signAfterDigest secretKey randomness index leaves : OracleComp HashSpec (Option Signature))
attribute [irreducible] treeNode ftsNode sampleParameter sampleOtsSecrets sampleFtsSecrets keygen sign
  keygenRoot keygenTable signAfterDigest
end Concrete
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)
abbrev IndependentSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Bytes ====
section

namespace SphincsSecurity
theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb
theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat
theorem tree_eq_of_pieces {x y : BitVec 40} (hhigh : x.extractLsb' 32 8 = y.extractLsb' 32 8)
    (hlow : x.extractLsb' 0 32 = y.extractLsb' 0 32) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hsmall : i < 32
  · have h := congrArg (fun b : BitVec 32 => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hsmall] using h
  · have h := congrArg (fun b : BitVec 8 => b.getLsbD (i - 32)) hhigh
    have hlt : i - 32 < 8 := by omega
    have hsum : 32 + (i - 32) = i := by omega
    simpa [BitVec.getLsbD_extractLsb', hlt, hsum] using h
theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) : t1 = t2 := by
  obtain ⟨tag1, layer1, tree1, position1, index1⟩ := t1
  obtain ⟨tag2, layer2, tree2, position2, index2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, hindex⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htree⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hposition⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hhigh⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨htag, hlayer⟩ := List.append_inj' h (by simp [bytesLE_length])
  have htag := List.append_right_injective [protocolDomainSep] htag
  simp only [bytesLE_injective htag, bytesLE_injective hlayer,
    tree_eq_of_pieces (bytesLE_injective hhigh) (bytesLE_injective htree),
    bytesLE_injective hposition, bytesLE_injective hindex]
theorem tweakBytes_eq_iff {d1 d2 : HashDomain} :
    tweakBytes d1 = tweakBytes d2 ↔ hashDomainFields d1 = hashDomainFields d2 :=
  ⟨fun h => fieldBytes_injective h, fun h => by rw [tweakBytes, tweakBytes, h]⟩
private theorem layer_le : numLayers ≤ 2 ^ 8 := by decide
private theorem tree_le : 2 ^ totalHeight ≤ 2 ^ 40 := Nat.pow_le_pow_right (by omega) (by decide)
private theorem index_le : 2 ^ totalHeight ≤ 2 ^ 40 := tree_le
private theorem leaf_le : 2 ^ maxLayerHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by decide)
def HashDomain.InRange : HashDomain → Prop
  | .node _ _ level nodeIdx => level < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
  | .ftsLeaf _ _ leafIdx => leafIdx < 2 ^ 32
  | .ftsNode _ _ heapIdx => heapIdx < 2 ^ 32
  | _ => True
theorem HashDomain.ftsLeaf_inRange (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    (HashDomain.ftsLeaf index tree leaf.val).InRange :=
  Nat.lt_of_lt_of_le leaf.isLt (Nat.pow_le_pow_right (by omega) (by decide))
theorem HashDomain.ftsNode_inRange (index : Index) (tree : FtsTree) {heap : Nat}
    (hheap : heap < 2 ^ (ftsTreeHeight + 1)) : (HashDomain.ftsNode index tree heap).InRange :=
  Nat.lt_of_lt_of_le hheap (Nat.pow_le_pow_right (by omega) (by decide))
theorem fin_of_ofNat_eq {w n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ w)
    (h : BitVec.ofNat w a.val = BitVec.ofNat w b.val) : a = b :=
  Fin.ext (ofNat_inj_of_lt (Nat.lt_of_lt_of_le a.isLt hn) (Nat.lt_of_lt_of_le b.isLt hn) h)
theorem tweakBytes_injective {d1 d2 : HashDomain} (h1 : d1.InRange) (h2 : d2.InRange)
    (h : tweakBytes d1 = tweakBytes d2) : d1 = d2 := by
  rw [tweakBytes_eq_iff] at h
  cases d1 <;> cases d2 <;>
    simp_all [hashDomainFields, tweakFields, HashDomain.InRange, TweakFields.mk.injEq]
  case chain.chain lay1 tree1 leaf1 i1 s1 lay2 tree2 leaf2 i2 s2 =>
    obtain ⟨hl, ht, hp, hlf⟩ := h
    have hpos := ofNat_inj_of_lt (OtsCode.chainTweakPosition_lt i1 s1) (OtsCode.chainTweakPosition_lt i2 s2) hp
    obtain ⟨hi, hs⟩ := OtsCode.chainTweakPosition_injective hpos
    exact ⟨fin_of_ofNat_eq layer_le hl, fin_of_ofNat_eq tree_le ht, fin_of_ofNat_eq leaf_le hlf, hi, hs⟩
  case leaf.leaf => exact ⟨fin_of_ofNat_eq layer_le h.1, fin_of_ofNat_eq tree_le h.2.1,
      fin_of_ofNat_eq leaf_le h.2.2⟩
  case node.node lay1 tree1 level1 nodeIdx1 lay2 tree2 level2 nodeIdx2 =>
    exact ⟨fin_of_ofNat_eq layer_le h.1, fin_of_ofNat_eq tree_le h.2.1,
      ofNat_inj_of_lt h1.1 h2.1 h.2.2.1, ofNat_inj_of_lt h1.2 h2.2 h.2.2.2⟩
  case encoding.encoding => exact ⟨fin_of_ofNat_eq layer_le h.1, fin_of_ofNat_eq tree_le h.2.1,
      fin_of_ofNat_eq leaf_le h.2.2⟩
  case ftsLeaf.ftsLeaf index1 tree1 leaf1 index2 tree2 leaf2 =>
    exact ⟨fin_of_ofNat_eq index_le h.1, Subsingleton.elim _ _, ofNat_inj_of_lt h1 h2 h.2⟩
  case ftsNode.ftsNode index1 tree1 heap1 index2 tree2 heap2 =>
    exact ⟨fin_of_ofNat_eq index_le h.1, Subsingleton.elim _ _, ofNat_inj_of_lt h1 h2 h.2⟩
theorem tweakBytes_length (domain : HashDomain) : (tweakBytes domain).length = 16 := by
  simp [tweakBytes, fieldBytes, bytesLE_length]
theorem tweakableHashInput_injective (parameter : PublicParameter) {d1 d2 : HashDomain}
    (h1 : d1.InRange) (h2 : d2.InRange) {payload1 payload2 : HashInput}
    (h : tweakableHashInput parameter d1 payload1 = tweakableHashInput parameter d2 payload2) :
    d1 = d2 ∧ payload1 = payload2 := by
  simp only [tweakableHashInput] at h
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨tweakBytes_injective h1 h2 htweak, hpayload⟩
theorem tweakableHashInput_ne_message (parameter : PublicParameter) (domain : HashDomain)
    (hdomain : domain ≠ .message) (payload messagePayload : HashInput) :
    tweakableHashInput parameter domain payload ≠
      tweakableHashInput parameter .message messagePayload := by
  intro hinput
  simp only [tweakableHashInput] at hinput
  obtain ⟨hprefix, _⟩ := List.append_inj hinput
    (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  apply hdomain
  cases domain <;>
    simp_all [tweakBytes_eq_iff, hashDomainFields, tweakFields, TweakFields.mk.injEq]
theorem digestBytes_injective {x y : Digest} (h : Concrete.digestBytes x = Concrete.digestBytes y) :
    x = y :=
  bytesLE_injective h
theorem digestBytes_length (x : Digest) : (Concrete.digestBytes x).length = 16 :=
  bytesLE_length 16 x
theorem nodePayload_injective {left right left' right' : Digest}
    (h : Concrete.nodePayload left right = Concrete.nodePayload left' right') :
    left = left' ∧ right = right' := by
  obtain ⟨hleft, hright⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
  exact ⟨digestBytes_injective hleft, digestBytes_injective hright⟩
theorem flatMap_ofFn_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {n : Nat} {f f' : Fin n → α},
      (List.ofFn f).flatMap g = (List.ofFn f').flatMap g → f = f' := by
  intro n
  induction n with
  | zero => intro f f' _; funext i; exact i.elim0
  | succ n ih =>
      intro f f' h
      simp only [List.ofFn_succ, List.flatMap_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
      have hzero := hinj _ _ hhead
      have hsucc := ih htail
      funext i
      cases i using Fin.cases with
      | zero => exact hzero
      | succ j => exact congrFun hsucc j
theorem leafPayload_injective {endpoints endpoints' : ChainIndex → Digest}
    (h : Concrete.leafPayload endpoints = Concrete.leafPayload endpoints') :
    endpoints = endpoints' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Guess ====
section

namespace SphincsSecurity
open OracleComp ENNReal
theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ hashOutputBits) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (hashOutputBits - width)
      = y.extractLsb' width (hashOutputBits - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < hashOutputBits - width := by omega
    have := congrArg (fun b : BitVec (hashOutputBits - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Scheme_HashOutputSplit ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
def splitHashOutput (width : Nat) (output : HashOutput) :
    BitVec width × BitVec (hashOutputBits - width) :=
  (output.extractLsb' 0 width,
    output.extractLsb' width (hashOutputBits - width))
theorem splitHashOutput_injective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Injective (splitHashOutput width) := by
  intro left right heq
  apply hashOutput_eq_of_extract hwidth
  · exact congrArg Prod.fst heq
  · exact congrArg Prod.snd heq
theorem splitHashOutput_bijective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Bijective (splitHashOutput width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨splitHashOutput_injective hwidth, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  congr
  omega
noncomputable def splitHashOutputEquiv (width : Nat) (hwidth : width ≤ hashOutputBits) :
    HashOutput ≃ BitVec width × BitVec (hashOutputBits - width) :=
  Equiv.ofBijective (splitHashOutput width) (splitHashOutput_bijective hwidth)
theorem evalDist_hashOutput_extract_uniform {width : Nat} (hwidth : width ≤ hashOutputBits) :
    𝒮[(fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ BitVec width : ProbComp (BitVec width))] := by
  let split := splitHashOutput width
  have hmap :
      (fun output : HashOutput => output.extractLsb' 0 width) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) =
        Prod.fst <$> (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, split, splitHashOutput]
  rw [hmap]
  have hsplit :
      𝒮[split <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
        𝒮[($ᵗ (BitVec width × BitVec (hashOutputBits - width)) :
          ProbComp (BitVec width × BitVec (hashOutputBits - width)))] :=
    evalSPMF_map_bijective_uniform_cross
      (α := HashOutput) (β := BitVec width × BitVec (hashOutputBits - width))
      split (splitHashOutput_bijective hwidth)
  rw [evalSPMF_map, hsplit, ← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod
end SphincsSecurity
end
