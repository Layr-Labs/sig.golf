import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Layout
import SigGolfCandidate.ClaudeWCT.WCT9.Limits
import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode

section
namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff)
def regionBase (k : Nat) : Nat := 64 + 816 * (8 - k)
def wctEnd : Nat := 7424
def wctChainBlock (k t : Nat) : Nat := regionBase k + (640 - 64 * t)
def wctLeafBlock (k : Nat) : Nat := regionBase k + 688
def wctLeafSlot (k t : Nat) : Nat := regionBase k + (if t = 0 then 688 else 720 + 16 * t)
def authPlans : List (List Nat × Nat) :=
  [([0,32,64,96,128,160], 224),
   ([0,48,80,112,144,176], 240),
   ([48,0,80,112,144,176], 240),
   ([32,112,160,192,224,256], 0),
   ([48,80,144,192,224,256], 0),
   ([32,80,144,192,224,256], 0),
   ([80,32,144,192,224,256], 0),
   ([64,16,144,192,224,256], 0),
   ([48,80,112,176,224,256], 0),
   ([32,80,112,176,224,256], 0),
   ([80,32,112,176,224,256], 0),
   ([272,16,64,160,208,96], 0),
   ([80,112,32,176,224,256], 0),
   ([64,112,16,176,224,256], 0),
   ([112,64,16,176,224,256], 0),
   ([256,208,160,0,48,80], 144),
   ([48,80,112,144,208,256], 0),
   ([32,80,112,144,208,256], 0),
   ([80,32,112,144,208,256], 0),
   ([272,16,64,176,128,208], 0),
   ([80,112,32,144,208,256], 0),
   ([64,112,16,144,208,256], 0),
   ([112,64,16,144,208,256], 0),
   ([288,240,16,64,128,176], 0),
   ([80,112,144,32,208,256], 0),
   ([64,112,144,16,208,256], 0),
   ([112,64,144,16,208,256], 0),
   ([288,112,160,240,0,48], 224),
   ([112,144,64,16,208,256], 0),
   ([128,176,288,240,0,48], 112),
   ([176,128,288,240,0,48], 112),
   ([272,224,176,128,0,48], 112),
   ([48,80,112,144,256,208], 0),
   ([32,80,112,144,256,208], 0),
   ([80,32,112,144,256,208], 0),
   ([272,16,64,96,208,160], 0),
   ([80,112,32,144,256,208], 0),
   ([64,112,16,144,256,208], 0),
   ([112,64,16,144,256,208], 0),
   ([288,240,16,64,176,128], 0),
   ([80,112,144,32,256,208], 0),
   ([64,112,144,16,256,208], 0),
   ([112,64,144,16,256,208], 0),
   ([288,112,160,0,48,240], 224),
   ([112,144,64,16,256,208], 0),
   ([128,176,288,16,64,240], 0),
   ([176,128,288,16,64,240], 0),
   ([272,224,176,48,96,0], 160),
   ([80,112,144,256,208,16], 0),
   ([64,112,144,256,208,16], 0),
   ([112,64,144,256,208,16], 0),
   ([288,112,160,48,0,240], 224),
   ([112,144,64,256,208,16], 0),
   ([128,176,16,64,288,240], 0),
   ([176,128,16,64,288,240], 0),
   ([272,224,96,144,48,0], 208),
   ([112,144,256,208,64,16], 0),
   ([128,176,64,16,288,240], 0),
   ([176,128,64,16,288,240], 0),
   ([272,144,192,96,48,0], 256),
   ([176,112,64,16,288,240], 0),
   ([192,240,144,96,48,0], 304),
   ([240,192,144,96,48,0], 304),
   ([256,208,160,112,64,16], 0)]
def authBase (child l : Nat) : Nat := ((authPlans.getD (child % 64) ([], 0)).1).getD l 0
def authRoot (child : Nat) : Nat := (authPlans.getD (child % 64) ([], 0)).2
def authSibOff (child l : Nat) : Nat :=
  if l < 6 then authBase child l + sibOff (child / 2 ^ l % 2) else authRoot child
def authPadOff (child l : Nat) : Nat := authBase child l + 32
def wopen (w : WBytes) (k t : Nat) : Digest := wdig w (wctChainBlock k t + 48)
def wleaf (w : WBytes) (k t : Nat) : Digest := wdig w (wctLeafSlot k t)
def wreveal (w : WBytes) (k t d : Nat) : Digest := if d = 0 then wleaf w k t else wopen w k t
def wcpads (w : WBytes) (k t : Nat) : Digest × Digest :=
  (wdig w (wctChainBlock k t), wdig w (wctChainBlock k t + 32))
def wsib (w : WBytes) (k child l : Nat) : Digest := wdig w (regionBase k + authSibOff child l)
def wmpad (w : WBytes) (k child l : Nat) : Digest := wdig w (regionBase k + authPadOff child l)
def wcHeaderPad (w : WBytes) (k t : Nat) : BitVec 64 := (wdig w (wctChainBlock k t + 16)).extractLsb' 64 64
/-- FTS leaf pad (campaign T8): the 16-byte slot after the leaf header (`regionBase k + 720`); the verifier never
writes it, the honest witness holds 0. -/
def wleafPad (w : WBytes) (k : Nat) : Digest := wdig w (wctLeafBlock k + 32)
def upLayer (lay : Layer) : Layer := Fin.ofNat 4 (lay.val + 1)
def rowBlock (index : Nat) (lay : Layer) : Nat :=
  if lay.val = 3 then 0 else merkleBlock (upLayer lay) (route index (upLayer lay)).1 (height (upLayer lay) - 1)
def bcCounterOff (index : Nat) (lay : Layer) : Nat := rowBlock index lay + 32
def wbcCtr (w : WBytes) (index : Nat) (lay : Layer) : BitVec 32 := wle32 w (bcCounterOff index lay)
def wbcPad (w : WBytes) (index : Nat) (lay : Layer) : BitVec 96 := w.extractLsb' (8 * (bcCounterOff index lay + 4)) 96
def wbcRight (w : WBytes) : Digest := wdig w 48
theorem wctLeafSlot_zero (k : Nat) : wctLeafSlot k 0 = wctChainBlock k 0 + 48 := by
  simp [wctLeafSlot, wctChainBlock]
theorem wleaf_zero (w : WBytes) (k : Nat) : wleaf w k 0 = wopen w k 0 := by
  unfold wleaf wopen; rw [wctLeafSlot_zero]
end ClaudeWCT.W9.T3M
end
section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (chainP nodeHashP recoverLayerP)
open SphincsSecurity (bytesLE)
def wctChainInputP (index coord child t step : Nat) (padA : Digest) (padB : BitVec 64) (padC value : Digest) :
    HashInput :=
  bytesLE 16 padA ++ bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step padB) ++ bytesLE 16 padC ++
    bytesLE 16 value
def wctChainP (index coord child t start count : Nat) (padA : Digest) (padB : BitVec 64) (padC value : Digest) :
    M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (wctChainInputP index coord child t step padA padB padC value)) value
def wctNodeHashP (coord index heap : Nat) (left pad right : Digest) : M Digest :=
  nodeHashP 3 (WCT9.nodeLayer coord) index heap left pad right
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ WCT9.digestVerifyWindow then pure none else some <$> digest (wrho w) m (wdc w)
def gateOk (N : HashOutput) : Bool := decide (N.toNat / 2 ^ 242 % 2 ^ 14 < WCT9.gateLimit)
def fieldOk (N : HashOutput) (coord : WCT9.Coord) : Bool := decide (WCT9.field N coord < WCT9.fieldLimit)
def wctCoordP (w : WBytes) (index : Nat) (coord : WCT9.Coord) (child : WCT9.Child) (word : WCT9.Rank) :
    M (Digest × Digest) := do
  let ends ← (List.finRange 6).mapM fun t =>
    wctChainP index coord.val child.val t.val (4 - WCT9.wordDigit word t) (WCT9.wordDigit word t)
      (wcpads w coord.val t.val).1 (wcHeaderPad w coord.val t.val) (wcpads w coord.val t.val).2
      (wreveal w coord.val t.val (WCT9.wordDigit word t))
  let leaf ← WCT9.leafHashP index coord.val child.val (wleafPad w coord.val) ends
  let top ← (List.finRange 6).foldlM (fun value level => do
    let other := wsib w coord.val child.val level.val
    let pair := if child.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + child.val / 2 ^ (level.val + 1)) pair.1
      (wmpad w coord.val child.val level.val) pair.2) leaf
  let other := wsib w coord.val child.val 6
  pure (if child.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
def wctStep (w : WBytes) (N : HashOutput) (state : Option (List (Digest × Digest))) (coord : WCT9.Coord) :
    M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if !fieldOk N coord then return none
  let pair ← wctCoordP w (WCT9.digestIndex N) coord (WCT9.child N coord) (WCT9.rank N coord)
  pure (some (pairs ++ [pair]))
def wctP (w : WBytes) (N : HashOutput) : M (Option Digest) := do
  let some pairs ← (List.finRange 9).foldlM (wctStep w N) (some []) | pure none
  some <$> WCT9.forestPk (WCT9.digestIndex N) pairs
def layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) : HashInput :=
  match msg with
  | .forest root => WCT9.pairEncodingInputP lay tree leaf root padR counter pad
  | .pair left right => WCT9.pairEncodingInputP lay tree leaf left right counter pad
def layerPairP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalue w lay i.val)
  let value ← leafHash lay tree leaf ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerklePad w lay leaf j.val) pair.2) value
  let other := wpath w lay leaf (height lay - 1)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def topChainP (w : WBytes) (tree leaf : Nat) (i : Fin (chainCount 0)) (digit : Nat) : M Digest :=
  chainP 0 tree leaf i.val digit (maxDigit 0 i.val - digit) (wchainPads w 0 i.val).1 (wchainPads w 0 i.val).2
    (wchainHeaderPad w 0 i.val) (wvalue w 0 i.val)
def topFinishP (w : WBytes) (tree leaf : Nat) (ends : List Digest) : M Digest := do
  let value ← leafHash 0 tree leaf ends
  (List.finRange (height 0)).foldlM (fun value j => do
    let other := wpath w 0 leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerklePad w 0 leaf j.val) pair.2) value
def topLayerP (w : WBytes) (index : Nat) (answer : Digest) : M (Option Digest) :=
  WCT9.topDecodeRun (topChainP w (route index 0).2 (route index 0).1) (topFinishP w (route index 0).2 (route index 0).1)
    answer
def layersBC (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w))
      if n = 0 then topLayerP w index answer
      else do
        let some digits := decode lay answer | pure none
        let pair ← layerPairP w index lay digits
        layersBC w index n (.pair pair.1 pair.2)
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some root ← wctP w N | pure false
  let some root ← layersBC w index 4 (.forest root) | pure false
  pure (root == pk)
def layersBCPrepass (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w))
      let some digits := decode lay answer | pure none
      if n = 0 then some <$> layerP w index lay digits
      else do
        let pair ← layerPairP w index lay digits
        layersBCPrepass w index n (.pair pair.1 pair.2)
def verifyPPrepass (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some root ← wctP w N | pure false
  let some root ← layersBCPrepass w index 4 (.forest root) | pure false
  pure (root == pk)
structure Pads where
  wctChain : WCT9.Coord → Fin 6 → Digest × Digest
  wctChainHigh : WCT9.Coord → Fin 6 → BitVec 64
  wctMerkle : WCT9.Coord → Fin 7 → Digest
  /-- FTS leaf pad (campaign T8; honest 0). -/
  wctLeaf : WCT9.Coord → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest
  chainHeader : (lay : Layer) → Fin (chainCount lay) → BitVec 64
  bc : Layer → BitVec 96
  bcRight : Digest
instance : Zero Pads :=
  ⟨⟨fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩⟩
def Pads.toT3 (pads : Pads) : SigGolfCandidate.T3M.Pads :=
  ⟨fun _ => 0, fun _ => 0, pads.chain, pads.merkle, pads.chainHeader⟩
def recoverCoordinateP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) : M (Digest × Digest) := do
  let selected := WCT9.child output coord
  let word := WCT9.rank output coord
  let ends ← (List.finRange 6).mapM fun i =>
    wctChainP index coord.val selected.val i.val (4 - WCT9.wordDigit word i) (WCT9.wordDigit word i)
      (pads.wctChain coord i).1 (pads.wctChainHigh coord i) (pads.wctChain coord i).2
      ((sig.openings coord).values i)
  let root ← WCT9.leafHashP index coord.val selected.val (pads.wctLeaf coord) ends
  let top ← (List.finRange 6).foldlM (fun value level => do
    let other := (sig.openings coord).path level.castSucc
    let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1)) pair.1
      (pads.wctMerkle coord level.castSucc) pair.2) root
  let other := (sig.openings coord).path 6
  pure (if selected.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
def recoverFtsP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput) : M Digest := do
  let pairs ← (List.finRange 9).mapM (recoverCoordinateP sig pads index output)
  WCT9.forestPk index pairs
def recoverLayerPairP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (pads.chain lay i).1 (pads.chain lay i).2 (pads.chainHeader lay i) ((sig.layers lay).values i)
  let value ← leafHash lay tree leaf ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkle lay (Fin.castLE (Nat.sub_le _ _) j)) pair.2) value
  let other := (sig.layers lay).path (WCT9.topLevel lay)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def verifyTopP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (answer : Digest) : M (Option Digest) :=
  let leaf := (route index 0).1
  let tree := (route index 0).2
  WCT9.topDecodeRun
    (fun i digit => chainP 0 tree leaf i.val digit (maxDigit 0 i.val - digit) (pads.chain 0 i).1
      (pads.chain 0 i).2 (pads.chainHeader 0 i) ((sig.layers 0).values i))
    (fun ends => do
      let value ← leafHash 0 tree leaf ends
      (List.finRange (height 0)).foldlM (fun value j => do
        let other := (sig.layers 0).path j
        let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        nodeHashP 3 (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
          (pads.merkle 0 j) pair.2) value)
    answer
def verifyLayersBCP (w : WCT9.Witness) (pads : Pads) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (layerEncodingInputP lay tree leaf msg counter (pads.bc lay) pads.bcRight)
      if n = 0 then verifyTopP w.signature pads index answer
      else do
        let some digits := decode lay answer | pure none
        let pair ← recoverLayerPairP w.signature pads index lay digits
        verifyLayersBCP w pads index n (.pair pair.1 pair.2)
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if !WCT9.admissible output then return false
  let index := WCT9.digestIndex output
  let root ← recoverFtsP w.signature pads index output
  let some root ← verifyLayersBCP w pads index 4 (.forest root) | pure false
  pure (root == pk)
def verifyPads (m : Message) (pk : Digest) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ WCT9.digestAttemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads
end ClaudeWCT.W9.T3M
end
