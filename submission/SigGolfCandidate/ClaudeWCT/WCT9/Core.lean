import SigGolfCandidate.T3.Core
import SigGolfCandidate.ClaudeWCT.WCT9.Codebook

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def coordinates : Nat := 9
def children : Nat := 128
def chains : Nat := 7
def gateShift : Nat := 235
def gateBits : Nat := 21
def gateLimit : Nat := 1091
def fieldBits : Nat := 14
def fieldLimit : Nat := 16200
def jointCap : Nat := 706
abbrev Coord := Fin 9
abbrev Child := Fin 128
abbrev Rank := Fin 600
def wctHeader (tag lay tree position index : Nat) : BitVec 128 :=
  BitVec.ofNat 128 (1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 +
    (tree / 2 ^ 32 % 256) * 2 ^ 24 + position % 2 ^ 32 * 2 ^ 32 +
    tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96)
def indexShift : Nat := 33
def digestIndex (output : HashOutput) : Nat := output.toNat / 2 ^ 33 % 2 ^ 31
theorem digestIndex_lt (output : HashOutput) : digestIndex output < 2 ^ 31 := Nat.mod_lt _ (by decide)
def childBase (k : Nat) : Nat := [0,64,85,121,128,149,185,192,213].getD k 0
def fieldBase (k : Nat) : Nat := [7,71,92,107,135,156,171,199,220].getD k 0
def child (output : HashOutput) (coord : Coord) : Child :=
  ⟨output.toNat / 2 ^ childBase coord.val % 128, Nat.mod_lt _ (by decide)⟩
def field (output : HashOutput) (coord : Coord) : Nat :=
  output.toNat / 2 ^ fieldBase coord.val % 2 ^ 14
def rank (output : HashOutput) (coord : Coord) : Rank :=
  ⟨field output coord % 600, Nat.mod_lt _ (by decide)⟩
def admissible (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 235 % 2 ^ 21 < 1091) &&
    (List.range 9).all (fun coord =>
      decide (output.toNat / 2 ^ fieldBase coord % 2 ^ 14 < 16200))
def childSaveTable : List Nat :=
  [0,1,1,1,1,2,2,1,1,2,2,2,1,2,2,1,1,2,2,2,1,2,2,1,1,2,2,1,1,1,1,1,1,2,2,2,1,2,2,1,1,2,2,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,0,1,1,0]
def maxChildSave : Nat := 2
def childSave (c : Nat) : Nat := childSaveTable.getD (c % 64) 0
def childExtra (c : Child) : Nat := maxChildSave - childSave c.val
theorem childSaveTable_le : ∀ i, i < 64 → childSaveTable.getD i 0 ≤ maxChildSave := by decide
theorem childSave_le (c : Nat) : childSave c ≤ maxChildSave :=
  childSaveTable_le (c % 64) (Nat.mod_lt _ (by decide))
theorem childExtra_add (c : Child) : childExtra c + childSave c.val = maxChildSave := by
  have := childSave_le c.val
  unfold childExtra; omega
def coordCost (output : HashOutput) (coord : Coord) : Nat :=
  routineCost (rank output coord) + childExtra (child output coord)
def jointCost (output : HashOutput) : Nat :=
  ((List.finRange 9).map fun coord => coordCost output coord).sum
def capOk (output : HashOutput) : Bool := decide (jointCost output ≤ jointCap)
def producerAdmissible (output : HashOutput) : Bool := admissible output && capOk output
def digestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if producerAdmissible output then return some (BitVec.ofNat 32 counter, output)
      digestSearch rho message (counter + 1) fuel
def ftsChainLow (index coord selected chain step : Nat) : Nat :=
  0x80 + chain % 8 * 2 ^ 2 + step % 4 * 2 ^ 8 + coord % 16 * 2 ^ 16 + selected % 128 * 2 ^ 20 +
    index % 2 ^ 31 * 2 ^ 27
def ftsChainHeaderP (index coord selected chain step : Nat) (high : BitVec 64) : BitVec 128 :=
  high ++ BitVec.ofNat 64 (ftsChainLow index coord selected chain step)
def ftsChainHeader (index coord selected chain step : Nat) : BitVec 128 :=
  ftsChainHeaderP index coord selected chain step 0
def chainInput (index coord selected chain step : Nat) (value : Digest) : HashInput :=
  zero16 ++ bytesLE 16 (ftsChainHeader index coord selected chain step) ++
    zero16 ++ bytesLE 16 value
def chain (index coord selected i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInput index coord selected i step value)) value
def ftsLeafLow (index coord selected : Nat) : Nat :=
  1 + 6 * 2 ^ 8 + coord % 16 * 2 ^ 16 + selected % 128 * 2 ^ 20 + index % 2 ^ 31 * 2 ^ 27
def ftsLeafHeader (index coord selected : Nat) : BitVec 128 :=
  0#64 ++ BitVec.ofNat 64 (ftsLeafLow index coord selected)
def leafHash (index coord selected : Nat) (ends : List Digest) : M Digest :=
  shortHash (bytesLE 16 (ends.getD 0 0) ++
    bytesLE 16 (ftsLeafHeader index coord selected) ++ (ends.drop 1).flatMap (bytesLE 16))
def seedHalf (seeds : Digest × Digest) (q : Nat) : Digest := if q % 2 = 0 then seeds.1 else seeds.2
def packedSecret (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest) : M (Digest × Digest) :=
  if q % 2 = 0 then do
    let seeds ← pairQuery (q / 2)
    pure (seeds.1, seeds.2)
  else pure (carry, carry)
def ftsOrdinal (child chain : Nat) : Nat := 7 * child + chain
def ftsSeedHeader (coord index pair : Nat) : BitVec 128 := header 8 coord index 0 pair
def ftsSeedPair (index coord pair : Nat) : M (Digest × Digest) := privatePair 8 coord index 0 pair
def buildChild (index coord selected : Nat) (word : Rank) (carry : Digest) :
    M ((Digest × List Digest) × Digest) := do
  let state ← (List.finRange 7).foldlM
    (fun (state : List Digest × List Digest × Digest) i => do
      let (secret, carry) ← packedSecret (ftsSeedPair index coord) (ftsOrdinal selected i.val) state.2.2
      let deficit := wordDigit word i
      let value ← chain index coord selected i.val 0 (3 - deficit) secret
      let last ← chain index coord selected i.val (3 - deficit) deficit value
      pure (state.1 ++ [last], state.2.1 ++ [value], carry)) ([], [], carry)
  let root ← leafHash index coord selected state.1
  pure ((root, state.2.1), state.2.2)
def nodeLayer (coord : Nat) : Nat := 4 + coord
def wctNodeHeader (coord index heap : Nat) : BitVec 128 := nodeTweak 3 (nodeLayer coord) index heap
def wctNodeHash (coord index heap : Nat) (left right : Digest) : M Digest :=
  nodeHash 3 (nodeLayer coord) index heap left right
def heapBuild (index coord : Nat) (leaves : List Digest) : M (Array Digest) :=
  (List.range' 2 126).reverse.foldlM (fun nodes heap => do
    let value ← wctNodeHash coord index heap (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
    pure (nodes.set! heap value)) ((List.replicate 128 (0 : Digest) ++ leaves).toArray)
def heapLevels (heap : Array Digest) : List (List Digest) :=
  (List.range 7).map fun level =>
    (List.range (2 ^ (7 - level))).map fun i => heap.getD (2 ^ (7 - level) + i) 0
def buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range 128).foldlM
    (fun (state : List Digest × List Digest × Digest) j => do
      let ((root, values), carry) ← buildChild index coord.val j word state.2.2
      pure (state.1 ++ [root], (if j = selected.val then values else state.2.1), carry)) ([], [], 0)
  let nodes ← heapBuild index coord.val state.1
  pure (heapLevels nodes, state.2.1)
def forestInput (index : Nat) (pairs : List (Digest × Digest)) : HashInput :=
  zero16 ++ bytesLE 16 (header 15 0 index 0 0) ++
    pairs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)
def forestPk (index : Nat) (pairs : List (Digest × Digest)) : M Digest :=
  shortHash (forestInput index pairs)
inductive LayerMsg where
  | forest (root : Digest)
  | pair (left right : Digest)
  deriving DecidableEq
def pairEncodingInputP (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (rowTweak up tree leaf) ++ bytesLE 4 counter ++ bytesLE 12 pad ++
    bytesLE 16 right
def layerEncodingInput (lay : Layer) (tree leaf : Nat) : LayerMsg → BitVec 32 → HashInput
  | .forest root, counter => encodingInput lay tree leaf root counter
  | .pair left right, counter => pairEncodingInputP lay tree leaf left right counter 0
def producerFloor (lay : Layer) : Nat := ![8, 4, 4, 4] lay
def wordCredit (lay : Layer) (digits : List Nat) : Nat :=
  ((List.range (chainCount lay)).filter fun i => digits.getD i 0 + 1 = maxDigit lay i).length
def producerDecode (lay : Layer) (answer : Digest) : Option (List Nat) :=
  match decode lay answer with
  | some digits => if producerFloor lay ≤ wordCredit lay digits then some digits else none
  | none => none
def lowerSearchLimit : Nat := 2 ^ 21
def searchLimit (lay : Layer) : Nat := if lay = 0 then counterLimit else lowerSearchLimit
/-- The verifier accepts every 32-bit counter: its window is the whole `BitVec 32` range, so the layer check
never rejects. The signer still searches `searchLimit`. -/
def verifyWindow : Nat := 2 ^ 32
theorem ctr_not_ge_verifyWindow (c : BitVec 32) : ¬c.toNat ≥ verifyWindow := by
  unfold verifyWindow; exact Nat.not_le.mpr c.isLt
def layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    Nat → M (Option (BitVec 32 × List Nat))
  | 0 => pure none
  | fuel + 1 => do
      let answer ← shortHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
      match producerDecode lay answer with
      | none => layerCounterSearch lay tree leaf msg (counter + 1) fuel
      | some digits => pure (some (BitVec.ofNat 32 counter, digits))
def lowerOrdinal (lay : Layer) (leaf chain : Nat) : Nat := chainCount lay * leaf + chain
def lowerSeedHeader (lay : Layer) (tree pair : Nat) : BitVec 128 := header 0 lay.val tree pair 0
def lowerSeedPair (lay : Layer) (tree pair : Nat) : M (Digest × Digest) := privatePair 0 lay.val tree pair 0
def buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    M ((Digest × List Digest) × Digest) := do
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest × Digest) i => do
      let (seed, carry) ← packedSecret (lowerSeedPair lay tree) (lowerOrdinal lay leaf i) state.2.2
      let digit := digits.getD i 0
      let value ← SigGolfCandidate.T3.chain lay tree leaf i 0 digit seed
      let last ← SigGolfCandidate.T3.chain lay tree leaf i digit (maxDigit lay i - digit) value
      pure (state.1 ++ [last], state.2.1 ++ [value], carry)) ([], [], carry)
  let root ← SigGolfCandidate.T3.leafHash lay tree leaf state.1
  pure ((root, state.2.1), state.2.2)
def buildLevelsBelow (tag lay tree h : Nat) (leaves : List Digest) : M (List (List Digest)) :=
  (List.range' 1 (h - 1)).foldlM (fun levels level => do
    let nodes ← buildLevel tag lay tree h level (levels.getD (level - 1) [])
    pure (levels ++ [nodes])) [leaves]
def buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × Digest) leaf => do
      let ((root, values), carry) ← buildLeafP lay tree leaf (if leaf = selected then digits else []) state.2.2
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), carry)) ([], [], 0)
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure (levels, state.2.1)
def topLevel (lay : Layer) : Fin (height lay) :=
  ⟨height lay - 1, by fin_cases lay <;> decide⟩
def topPair (lay : Layer) (levels : List (List Digest)) : Digest × Digest :=
  ((levels.getD (height lay - 1) []).getD 0 0, (levels.getD (height lay - 1) []).getD 1 0)
def signLayersBC (cache : Cache) (index : Nat) : Nat → LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreeP lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := topPair lay levels
        let some previous ← signLayersBC cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))
structure Opening where
  values : Fin 7 → Digest
  path : Fin 7 → Digest
structure Signature where
  rho : Digest
  openings : Coord → Opening
  layers : (lay : Layer) → LayerSignature lay
structure Witness where
  signature : Signature
  digestCounter : BitVec 32
  counters : Layer → BitVec 32
def toT3Signature (sig : Signature) : SigGolfCandidate.T3.Signature :=
  ⟨sig.rho, fun _ => 0, fun _ => 0, sig.layers⟩
def toT3Witness (w : Witness) : SigGolfCandidate.T3.Witness :=
  ⟨toT3Signature w.signature, w.digestCounter, w.counters⟩
def recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    SigGolfCandidate.T3.chain lay tree leaf i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)
  let value ← SigGolfCandidate.T3.leafHash lay tree leaf ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHash 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2) value
  let other := (sig.layers lay).path (topLevel lay)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def topGroupBad (answer : Digest) (i : Nat) : Bool :=
  decide (i % 3 = 0 ∧ i < 51 ∧ 125 ≤ topCode answer / 2 ^ (7 * (i / 3)) % 128)
def topDecodeStep (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest)
    (state : Option (List Digest)) (i : Fin (chainCount 0)) : M (Option (List Digest)) := do
  let some ends := state | pure none
  if topGroupBad answer i.val then return none
  let value ← run i ((dataDigits 0 answer).getD i.val 0)
  pure (some (ends ++ [value]))
def topDecodeRun (run : Fin (chainCount 0) → Nat → M Digest) (finish : List Digest → M Digest)
    (answer : Digest) : M (Option Digest) := do
  if answer.toNat ≥ 2 ^ encodedBits 0 then return none
  let some ends ← (List.finRange (chainCount 0)).foldlM (topDecodeStep run answer) (some []) | pure none
  if (dataDigits 0 answer).sum ≠ target 0 then return none
  some <$> finish ends
def verifyTop (sig : Signature) (index : Nat) (answer : Digest) : M (Option Digest) :=
  let leaf := (route index 0).1
  let tree := (route index 0).2
  topDecodeRun
    (fun i digit => SigGolfCandidate.T3.chain 0 tree leaf i.val digit (maxDigit 0 i.val - digit)
      ((sig.layers 0).values i))
    (fun ends => do
      let value ← SigGolfCandidate.T3.leafHash 0 tree leaf ends
      (List.finRange (height 0)).foldlM (fun value j => do
        let other := (sig.layers 0).path j
        let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        nodeHash 3 (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2)
        value)
    answer
def expandLayersBC (sig : Signature) (index : Nat) :
    Nat → LayerMsg → M (Option (Digest × List (BitVec 32)))
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits) ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay) | pure none
      if n = 0 then
        let root ← recoverLayer (toT3Signature sig) index lay digits
        pure (some (root, [counter]))
      else
        let pair ← recoverLayerPair sig index lay digits
        let some (root, counters) ← expandLayersBC sig index n (.pair pair.1 pair.2) | pure none
        pure (some (root, counters ++ [counter]))
def verifyLayersBC (w : Witness) (index : Nat) : Nat → LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (layerEncodingInput lay tree leaf msg counter)
      if n = 0 then verifyTop w.signature index answer
      else do
        let some digits := decode lay answer | pure none
        let pair ← recoverLayerPair w.signature index lay digits
        verifyLayersBC w index n (.pair pair.1 pair.2)
def signPayload (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_, output) ← digestSearch rho message 0 attemptLimit | pure none
  let index := digestIndex output
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List (Digest × Digest)) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinate index coord selected (rank output coord)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening],
        state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])) ([], [])
  let root ← forestPk index state.2
  let some layers ← signLayersBC cache index 4 (.forest root) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
def sign (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message
def serializeOpening (opened : Opening) : HashInput :=
  (List.ofFn opened.values).flatMap (bytesLE 16) ++
    (List.ofFn opened.path).flatMap (bytesLE 16)
def serialize (sig : Signature) : HashInput :=
  bytesLE 16 sig.rho ++ (List.ofFn sig.openings).flatMap serializeOpening ++
    (List.ofFn fun lay => serializeLayer (sig.layers lay)).flatten
def recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput) (coord : Coord) :
    M (Digest × Digest) := do
  let selected := child output coord
  let word := rank output coord
  let ends ← (List.finRange 7).mapM fun i =>
    let deficit := wordDigit word i
    chain index coord.val selected.val i.val (3 - deficit) deficit ((sig.openings coord).values i)
  let root ← leafHash index coord.val selected.val ends
  let top ← (List.finRange 6).foldlM
    (fun value level => do
      let other := (sig.openings coord).path level.castSucc
      let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      wctNodeHash coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1))
        pair.1 pair.2) root
  let other := (sig.openings coord).path 6
  pure (if selected.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
def recoverFts (sig : Signature) (index : Nat) (output : HashOutput) : M Digest := do
  let pairs ← (List.finRange 9).mapM (recoverCoordinate sig index output)
  forestPk index pairs
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := digestIndex output
  let root ← recoverFts sig index output
  let some (root, counters) ← expandLayersBC sig index 4 (.forest root) | pure none
  if root ≠ pk then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !admissible output then return false
  let index := digestIndex output
  let root ← recoverFts w.signature index output
  let some root ← verifyLayersBC w index 4 (.forest root) | pure false
  pure (root == pk)
def keygen := SigGolfCandidate.T3.keygen
end ClaudeWCT.WCT9
