import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Layout
import SigGolfCandidate.ClaudeWCT.WCT9.Limits
import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode
import SigGolfCandidate.T3M.Witness.Queries

section
namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff)
/-- Nested FTS (r1-1): region stride 896; coordinate `k`'s region starts at `80 + 896 (8 - k)` (absolute
`1392 + 896 (8 - k)`; witness trim: the witness starts at 1312). -/
def regionBase (k : Nat) : Nat := 80 + 896 * (8 - k)
def wctEnd : Nat := 8096
def wctChainBlock (k t : Nat) : Nat := regionBase k + (640 - 64 * t)
def wctLeafBlock (k : Nat) : Nat := regionBase k + 688
def wctLeafSlot (k t : Nat) : Nat := regionBase k + (if t = 0 then 688 else 720 + 16 * t)
def authPlans : List (List Nat × Nat) :=
  [([0,32,64,96,128,832], 224),
   ([0,48,80,112,144,832], 240),
   ([48,0,80,112,144,832], 240),
   ([32,112,160,192,224,832], 0),
   ([48,80,144,192,224,832], 0),
   ([32,80,144,192,224,832], 0),
   ([80,32,144,192,224,832], 0),
   ([64,16,144,192,224,832], 0),
   ([48,80,112,176,224,832], 0),
   ([32,80,112,176,224,832], 0),
   ([80,32,112,176,224,832], 0),
   ([272,16,64,160,208,832], 0),
   ([80,112,32,176,224,832], 0),
   ([64,112,16,176,224,832], 0),
   ([112,64,16,176,224,832], 0),
   ([256,208,160,0,48,832], 144),
   ([48,80,112,144,208,832], 0),
   ([32,80,112,144,208,832], 0),
   ([80,32,112,144,208,832], 0),
   ([272,16,64,176,128,832], 0),
   ([80,112,32,144,208,832], 0),
   ([64,112,16,144,208,832], 0),
   ([112,64,16,144,208,832], 0),
   ([288,240,16,64,128,832], 0),
   ([80,112,144,32,208,832], 0),
   ([64,112,144,16,208,832], 0),
   ([112,64,144,16,208,832], 0),
   ([288,112,160,240,0,832], 224),
   ([112,144,64,16,208,832], 0),
   ([128,176,288,240,0,832], 112),
   ([176,128,288,240,0,832], 112),
   ([272,224,176,128,0,832], 112),
   ([48,80,112,144,256,832], 0),
   ([32,80,112,144,256,832], 0),
   ([80,32,112,144,256,832], 0),
   ([272,16,64,96,208,832], 0),
   ([80,112,32,144,256,832], 0),
   ([64,112,16,144,256,832], 0),
   ([112,64,16,144,256,832], 0),
   ([288,240,16,64,176,832], 0),
   ([80,112,144,32,256,832], 0),
   ([64,112,144,16,256,832], 0),
   ([112,64,144,16,256,832], 0),
   ([288,112,160,0,48,832], 224),
   ([112,144,64,16,256,832], 0),
   ([128,176,288,16,64,832], 0),
   ([176,128,288,16,64,832], 0),
   ([272,224,176,48,96,832], 160),
   ([80,112,144,256,208,832], 0),
   ([64,112,144,256,208,832], 0),
   ([112,64,144,256,208,832], 0),
   ([288,112,160,48,0,832], 224),
   ([112,144,64,256,208,832], 0),
   ([128,176,16,64,288,832], 0),
   ([176,128,16,64,288,832], 0),
   ([272,224,96,144,48,832], 208),
   ([112,144,256,208,64,832], 0),
   ([128,176,64,16,288,832], 0),
   ([176,128,64,16,288,832], 0),
   ([272,144,192,96,48,832], 256),
   ([176,112,64,16,288,832], 0),
   ([192,240,144,96,48,832], 304),
   ([240,192,144,96,48,832], 304),
   ([256,208,160,112,64,832], 0)]
def authBase (child l : Nat) : Nat := ((authPlans.getD (child % 64) ([], 0)).1).getD l 0
theorem authBase_five (child : Nat) : authBase child 5 = 832 := by
  have h : ∀ c < 64, ((authPlans.getD c ([], 0)).1).getD 5 0 = 832 := by decide
  exact h (child % 64) (Nat.mod_lt _ (by decide))
def authRoot (child : Nat) : Nat := (authPlans.getD (child % 64) ([], 0)).2
def authSibOff (child l : Nat) : Nat :=
  if l < 6 then authBase child l + sibOff (child / 2 ^ l % 2) else authRoot child
def authPadOff (child l : Nat) : Nat := authBase child l + 32
def wopen (w : WBytes) (k t : Nat) : Digest := wdig w (wctChainBlock k t + 48)
def wleaf (w : WBytes) (k t : Nat) : Digest := wdig w (wctLeafSlot k t)
def wreveal (w : WBytes) (k t d : Nat) : Digest := if d = 0 then wleaf w k t else wopen w k t
def wcpads (w : WBytes) (k t : Nat) : Digest × Digest :=
  (wdig w (wctChainBlock k t), wdig w (wctChainBlock k t + 32))
/-- Nested FTS (r1-1): the supplied top sibling of coordinate `k` sits in coordinate `k + 1`'s region: its leaf pad
slot (`regionBase k - 176`) when the computed top is the right one (bit 6 set), else its level-6 pad slot
(`regionBase k - 32`). For `k = 8` these are the L3 block's left slot (offset 0) and the R9 slot (witness trim:
offset 64, the 16 bytes after the L3 block's hash input). -/
def topSlot (k child : Nat) : Nat :=
  if k = 8 then (if child / 2 ^ 6 % 2 = 0 then 64 else 0)
  else regionBase k - (if child / 2 ^ 6 % 2 = 0 then 32 else 176)
/-- Pairing stage 1: the legacy level-5 window of coordinate 0 (`regionBase 0 + 832`, 64 bytes) is removed from the
witness. The legacy padded verifier reads coordinate 0's level-5 sibling from `legacySib0` (the 16 bytes after
region 0's leaf area; the live paired forest never uses coordinate 0's level 5) and its pad from `legacyPad0` (region
0's zero cell at offset 816). -/
def legacySib0 : Nat := 8080
def legacyPad0 : Nat := regionBase 0 + 816
def wsib (w : WBytes) (k child l : Nat) : Digest :=
  if l < 6 then (if k = 0 ∧ l = 5 then wdig w legacySib0 else wdig w (regionBase k + authSibOff child l))
  else wdig w (topSlot k child)
def wmpad (w : WBytes) (k child l : Nat) : Digest :=
  if k = 0 ∧ l = 5 then wdig w legacyPad0 else wdig w (regionBase k + authPadOff child l)
/-- High tweak word of a packed FTS node (levels `< 4`) whose computed child is the right input: the verifier
writes only the low tweak word there, the high word stays witness memory (honest 0). Elsewhere it is 0. -/
def wmhpad (w : WBytes) (k child l : Nat) : BitVec 64 :=
  if l < 4 ∧ child / 2 ^ l % 2 = 1 then (wdig w (regionBase k + authBase child l + 16)).extractLsb' 64 64 else 0
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
/-- C2/C3 (FULL): the high word of encoding `lay`'s row tweak (witness bytes `[rowBlock + 24, +8)`: L3 at witness 24,
else the root window of `upLayer lay`; honest 1). -/
def wbcHigh (w : WBytes) (index : Nat) (lay : Layer) : BitVec 64 := (wdig w (rowBlock index lay + 16)).extractLsb' 64 64
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
def wctNodeHashP (coord index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : M Digest :=
  shortHash (SigGolfCandidate.T3M.SecurityInputs.nodeInputPH 3 (WCT9.nodeLayer coord) index heap left hp pad right)
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ WCT9.digestVerifyWindow then pure none else some <$> digest (wrho w) m (wdc w)
def gateOk (N : HashOutput) : Bool := decide (N.toNat / 2 ^ 242 % 2 ^ 14 < WCT9.gateLimit)
def fieldOk (N : HashOutput) (coord : WCT9.Coord) : Bool := decide (WCT9.field N coord < WCT9.fieldLimit)
/-- One FTS coordinate of the padded verifier (nested FTS r1-1): `prev` is the previous coordinate's top pair; its
left value is this coordinate's leaf pad and its right value the pad of the top node hash (high half). -/
def wctCoordP (w : WBytes) (index : Nat) (coord : WCT9.Coord) (child : WCT9.Child) (word : WCT9.Rank)
    (prev : Digest × Digest) : M (Digest × Digest) := do
  let ends ← (List.finRange 6).mapM fun t =>
    wctChainP index coord.val child.val t.val (4 - WCT9.wordDigit word t) (WCT9.wordDigit word t)
      (wcpads w coord.val t.val).1 (wcHeaderPad w coord.val t.val) (wcpads w coord.val t.val).2
      (wreveal w coord.val t.val (WCT9.wordDigit word t))
  let leaf ← WCT9.leafHashP index coord.val child.val prev.1 ends
  let value ← (List.finRange 5).foldlM (fun value level => do
    let other := wsib w coord.val child.val level.val
    let pair := if child.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + child.val / 2 ^ (level.val + 1)) pair.1
      (wmhpad w coord.val child.val level.val) (wmpad w coord.val child.val level.val) pair.2) leaf
  let other5 := wsib w coord.val child.val 5
  let pair5 := if child.val / 2 ^ 5 % 2 = 0 then (value, other5) else (other5, value)
  let top ← WCT9.wctTopHash coord.val index (2 + child.val / 2 ^ 6) pair5.1 prev.2 pair5.2
  let other := wsib w coord.val child.val 6
  pure (if child.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
/-- Nested FTS (r1-1): coordinate 0's pads are free witness slots (honest 0). -/
def wctStart (w : WBytes) : Digest × Digest := (wleafPad w 0, wmpad w 0 0 5)
def wctStep (w : WBytes) (N : HashOutput) (state : Option (List (Digest × Digest))) (coord : WCT9.Coord) :
    M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if !fieldOk N coord then return none
  let pair ← wctCoordP w (WCT9.digestIndex N) coord (WCT9.child N coord) (WCT9.rank N coord)
    (WCT9.prevPair (wctStart w) pairs)
  pure (some (pairs ++ [pair]))
/-- The FTS phase (nested FTS r1-1): the last coordinate's top pair, the L3 message. -/
def wctP (w : WBytes) (N : HashOutput) : M (Option (Digest × Digest)) := do
  let some pairs ← (List.finRange 9).foldlM (wctStep w N) (some []) | pure none
  pure (some (WCT9.prevPair (wctStart w) pairs))
/-- The verifier's encoding input (C2/C3 FULL: the row tweak's high word `hi` is a witness pad, honest 1). -/
def layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) : HashInput :=
  match msg with
  | .forest root => WCT9.pairEncodingInputH lay tree leaf root padR counter pad hi
  | .pair left right => WCT9.pairEncodingInputH lay tree leaf left right counter pad hi
def layerPairP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
  let value ← WCT9.leafHashW lay tree leaf (wtopLeafPad w) (wleafHigh w lay) ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    WCT9.lowerNodeHashP lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerkleHigh w lay leaf j.val) (wmerklePad w lay leaf j.val) pair.2) value
  let other := wpath w lay leaf (height lay - 1)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def layerChainP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) (i : Nat) : M Digest :=
  chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
    (maxDigit lay i - digits.getD i 0) (wchainPads w lay (i % chainCount lay)).1
    (wchainPads w lay (i % chainCount lay)).2 (wchainHeaderPad w lay (i % chainCount lay))
    (wvalueFor w lay digits (i % chainCount lay))
def layerGuardedPairP (w : WBytes) (index : Nat) (lay : Layer) (answer : Digest) (digits : List Nat) :
    M (Option (Digest × Digest)) :=
  WCT9.lowerGuardedRun (layerChainP w index lay digits) (layerPairP w index lay digits) answer
def topChainP (w : WBytes) (tree leaf : Nat) (digits : List Nat) (i : Fin (chainCount 0)) (digit : Nat) : M Digest :=
  chainP 0 tree leaf i.val digit (maxDigit 0 i.val - digit) (wchainPads w 0 i.val).1 (wchainPads w 0 i.val).2
    (wchainHeaderPad w 0 i.val) (wvalueFor w 0 digits i.val)
/-- C4: the top leaf (half by leaf parity) and the 12 top folds with the one-word label `topNodeWord heap`, the
witness high pad `wmerkleHigh w 0` and Z pad `wmerklePad w 0` (half by heap parity; the root, heap 1, low). -/
def topFinishP (w : WBytes) (tree leaf : Nat) (ends : List Digest) : M Digest := do
  let value ← WCT9.leafHashWG 0 tree leaf (wtopLeafPad w) (wleafHigh w 0) (wtopLeafGap w) ends
  (List.finRange (height 0)).foldlM (fun value j => do
    let other := wpath w 0 leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    WCT9.lowerNodeHashP (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerkleHigh w 0 leaf j.val) (wmerklePad w 0 leaf j.val) pair.2) value
def topLayerP (w : WBytes) (index : Nat) (answer : Digest) : M (Option Digest) :=
  WCT9.topDecodeRun (topChainP w (route index 0).2 (route index 0).1 (dataDigits 0 answer)) (topFinishP w (route index 0).2 (route index 0).1)
    answer
def layersBC (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w)
        (wbcHigh w index lay))
      if n = 0 then topLayerP w index answer
      else do
        let some digits := decode lay answer | pure none
        let some pair ← layerGuardedPairP w index lay answer digits | pure none
        layersBC w index n (.pair pair.1 pair.2)
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some top ← wctP w N | pure false
  let some root ← layersBC w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def layersBCPrepass (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w)
        (wbcHigh w index lay))
      let some digits := decode lay answer | pure none
      if n = 0 then some <$> layerP w index lay digits
      else do
        let pair ← layerPairP w index lay digits
        layersBCPrepass w index n (.pair pair.1 pair.2)
def verifyPPrepass (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some top ← wctP w N | pure false
  let some root ← layersBCPrepass w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
structure Pads where
  wctChain : WCT9.Coord → Fin 6 → Digest × Digest
  wctChainHigh : WCT9.Coord → Fin 6 → BitVec 64
  wctMerkle : WCT9.Coord → Fin 7 → Digest
  /-- High tweak words of the packed FTS nodes (honest 0). -/
  wctMerkleHigh : WCT9.Coord → Fin 7 → BitVec 64
  /-- FTS leaf pad (campaign T8; honest 0). -/
  wctLeaf : WCT9.Coord → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest
  chainHeader : (lay : Layer) → Fin (chainCount lay) → BitVec 64
  bc : Layer → BitVec 96
  bcRight : Digest
  /-- Difference between the prefilled endpoint and its raw chain value. Honest witnesses have zero masks. -/
  endpointMask : (lay : Layer) → Fin (chainCount lay) → Digest
  /-- C2 + C4: high tweak words of the one-word fold labels (lay 1..3 levels `< height - 1`, and every top level;
  honest 0). -/
  merkleHigh : (lay : Layer) → Fin (height lay) → BitVec 64
  /-- C3: the top leaf pad (the leading 16 bytes of the top leaf input; honest 0). -/
  topLeaf : Digest
  /-- Campaign R6: the top leaf's 32-byte gap after the tweak (witness 22328..22359; honest `(0, 0)`). -/
  topGap : Digest × Digest
  /-- C3: the leaf tweak's high word (honest 0). -/
  leafHigh : Layer → BitVec 64
  /-- C2/C3: XOR mask of the encoding row tweak's high word (the verifier uses `bcHigh lay ^^^ 1`; honest mask 0). -/
  bcHigh : Layer → BitVec 64
instance : Zero Pads :=
  ⟨⟨fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0,
    fun _ => 0, 0, fun _ _ => 0, fun _ _ => 0, 0, (0, 0), fun _ => 0, fun _ => 0⟩⟩
def Pads.toT3 (pads : Pads) : SigGolfCandidate.T3M.Pads :=
  ⟨fun _ => 0, fun _ => 0, pads.chain, pads.merkle, pads.chainHeader⟩
def recoverCoordinateP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) (prev : Digest × Digest) : M (Digest × Digest) := do
  let selected := WCT9.child output coord
  let word := WCT9.rank output coord
  let ends ← (List.finRange 6).mapM fun i =>
    wctChainP index coord.val selected.val i.val (4 - WCT9.wordDigit word i) (WCT9.wordDigit word i)
      (pads.wctChain coord i).1 (pads.wctChainHigh coord i) (pads.wctChain coord i).2
      ((sig.openings coord).values i)
  let root ← WCT9.leafHashP index coord.val selected.val prev.1 ends
  let value ← (List.finRange 5).foldlM (fun value level => do
    let other := (sig.openings coord).path (Fin.castLE (by decide) level)
    let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1)) pair.1
      (pads.wctMerkleHigh coord (Fin.castLE (by decide) level)) (pads.wctMerkle coord (Fin.castLE (by decide) level))
      pair.2) root
  let other5 := (sig.openings coord).path 5
  let pair5 := if selected.val / 2 ^ 5 % 2 = 0 then (value, other5) else (other5, value)
  let top ← WCT9.wctTopHash coord.val index (2 + selected.val / 2 ^ 6) pair5.1 prev.2 pair5.2
  let other := (sig.openings coord).path 6
  pure (if selected.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
/-- Nested FTS (r1-1): coordinate 0's pads in the abstract padded verifier. -/
def Pads.start (pads : Pads) : Digest × Digest := (pads.wctLeaf 0, pads.wctMerkle 0 5)
def recoverFtsP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput) : M (Digest × Digest) := do
  let pairs ← (List.finRange 9).foldlM (fun (pairs : List (Digest × Digest)) coord => do
    let pair ← recoverCoordinateP sig pads index output coord (WCT9.prevPair pads.start pairs)
    pure (pairs ++ [pair])) []
  pure (WCT9.prevPair pads.start pairs)
/-- Effective input of a chain, including the endpoint stored in a skipped-copy slot. -/
def valueP (sig : WCT9.Signature) (pads : Pads) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) : Digest :=
  if WCT9.safeZeroCopy lay digits i.val then
    (sig.layers lay).values i ^^^ pads.endpointMask lay i else (sig.layers lay).values i

@[simp] theorem valueP_zero (sig : WCT9.Signature) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) : valueP sig 0 lay digits i = (sig.layers lay).values i := by
  unfold valueP
  split
  · change (sig.layers lay).values i ^^^ (0 : Digest) = (sig.layers lay).values i
    exact BitVec.xor_zero
  · rfl

/-- A single-layer view after its encoding digits are known; other layers are irrelevant to this view. -/
def effectiveSignature (sig : WCT9.Signature) (pads : Pads) (digits : List Nat) : WCT9.Signature :=
  { sig with layers := fun lay => { sig.layers lay with values := valueP sig pads lay digits } }

def recoverLayerPairP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (pads.chain lay i).1 (pads.chain lay i).2 (pads.chainHeader lay i) (valueP sig pads lay digits i)
  let value ← WCT9.leafHashW lay tree leaf pads.topLeaf (pads.leafHigh lay) ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    WCT9.lowerNodeHashP lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkleHigh lay (Fin.castLE (Nat.sub_le _ _) j)) (pads.merkle lay (Fin.castLE (Nat.sub_le _ _) j))
      pair.2) value
  let other := (sig.layers lay).path (WCT9.topLevel lay)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def recoverLayerPairGuardP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) : M (Option (Digest × Digest)) :=
  WCT9.lowerGuardedRun
    (fun i => let j : Fin (chainCount lay) := ⟨i % chainCount lay, Nat.mod_lt _ (by fin_cases lay <;> decide)⟩
      chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
        (maxDigit lay i - digits.getD i 0) (pads.chain lay j).1 (pads.chain lay j).2
        (pads.chainHeader lay j) (valueP sig pads lay digits j))
    (recoverLayerPairP sig pads index lay digits) answer
def verifyTopP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (answer : Digest) : M (Option Digest) :=
  let leaf := (route index 0).1
  let tree := (route index 0).2
  WCT9.topDecodeRun
    (fun i digit => chainP 0 tree leaf i.val digit (maxDigit 0 i.val - digit) (pads.chain 0 i).1
      (pads.chain 0 i).2 (pads.chainHeader 0 i) (valueP sig pads 0 (dataDigits 0 answer) i))
    (fun ends => do
      let value ← WCT9.leafHashWG 0 tree leaf pads.topLeaf (pads.leafHigh 0) pads.topGap ends
      (List.finRange (height 0)).foldlM (fun value j => do
        let other := (sig.layers 0).path j
        let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        WCT9.lowerNodeHashP (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
          (pads.merkleHigh 0 j) (pads.merkle 0 j) pair.2) value)
    answer
def verifyLayersBCP (w : WCT9.Witness) (pads : Pads) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter (pads.bc lay) pads.bcRight
        (pads.bcHigh lay ^^^ 1))
      if n = 0 then verifyTopP w.signature pads index answer
      else do
        let some digits := decode lay answer | pure none
        let some pair ← recoverLayerPairGuardP w.signature pads index lay answer digits | pure none
        verifyLayersBCP w pads index n (.pair pair.1 pair.2)
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if !WCT9.admissible output then return false
  let index := WCT9.digestIndex output
  let top ← recoverFtsP w.signature pads index output
  let some root ← verifyLayersBCP w pads index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def verifyPads (m : Message) (pk : Digest) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ WCT9.digestAttemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads
end ClaudeWCT.W9.T3M
end

section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (allQ_pure allQ_bind allQ_map allQ_ite allQ_mapM)

theorem allQ_lowerGuardedRun {α : Type} {P : Spec.Domain → Prop}
    (run : Nat → M Digest) (finish : M α) (answer : Digest)
    (hrun : ∀ i, AllQueriesSatisfy (run i) P) (hfinish : AllQueriesSatisfy finish P) :
    AllQueriesSatisfy (WCT9.lowerGuardedRun run finish answer) P := by
  unfold WCT9.lowerGuardedRun
  exact allQ_ite _ (allQ_map _ hfinish)
    (allQ_bind (allQ_mapM _ _ hrun) fun _ => allQ_pure _)

theorem eval_lowerGuardedRun_none {α : Type} (answers : QueryImpl Spec Id)
    (run : Nat → M Digest) (finish : M α) (answer : Digest) (h : ¬ WCT9.lowerRankGood answer) :
    evalWithAnswerFn answers (WCT9.lowerGuardedRun run finish answer) = none := by
  simp [WCT9.lowerGuardedRun, h, evalWithAnswerFn_bind]

theorem layerGuardedPairP_of_good (w : WBytes) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) (h : WCT9.lowerRankGood answer) :
    layerGuardedPairP w index lay answer digits = some <$> layerPairP w index lay digits := by
  simp [layerGuardedPairP, WCT9.lowerGuardedRun, h]

theorem layerGuardedPairP_good_of_some (answers : QueryImpl Spec Id) (w : WBytes)
    (index : Nat) (lay : Layer) (answer : Digest) (digits : List Nat) (pair : Digest × Digest)
    (h : evalWithAnswerFn answers (layerGuardedPairP w index lay answer digits) = some pair) :
    WCT9.lowerRankGood answer := by
  by_contra hn
  have hz := eval_lowerGuardedRun_none answers (layerChainP w index lay digits)
    (layerPairP w index lay digits) answer hn
  change evalWithAnswerFn answers (layerGuardedPairP w index lay answer digits) = none at hz
  rw [hz] at h
  cases h
end ClaudeWCT.W9.T3M
end

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
/-- Padded canonical layers retain the machine ordering of rank checks and HASH calls. Configuration (1)+(2): the
top word is read with the witness choice hint `wtopHigh w` (`WCT9.verificationHash`; lower layers ignore it). -/
def layersCanonicalBC (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.verificationHash lay (wtopHigh w)
        (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay))
      if n = 0 then topLayerP w index answer
      else do
        let some digits := WCT9.CanonicalPolicy.decode lay answer | pure none
        let some pair ← layerGuardedPairP w index lay answer digits | pure none
        layersCanonicalBC w index n (.pair pair.1 pair.2)
end ClaudeWCT.W9.T3M
