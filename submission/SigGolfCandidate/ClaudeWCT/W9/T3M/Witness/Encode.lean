import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (zeros layerBytes sibOff)
open SphincsSecurity (bytesLE)
/-- The H2 expander (two omitted signature bytes recovered by search), with the digest output. -/
def expandN (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) :=
  WCT9.expandS WCT9.digestAttemptLimit message pk sig
/-- The expander before H2 (the full signature), with the digest output. -/
def expandN0 (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) := do
  let some (counter, output) ← WCT9.digestSearch sig.rho message 0 WCT9.digestAttemptLimit | pure none
  let index := WCT9.digestIndex output
  let top ← WCT9.recoverFts sig index output
  let some (root, counters) ← WCT9.expandLayersBC sig index 4 (.pair top.1 top.2) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
/-- Nested FTS (r1-1): the 176 bytes before coordinate 8's region (virtual tree 9). Offset 0 is the L3 block's left
slot (L8), 32 its counter, 48 its right slot (overwritten by the verifier with the copy of offset 144), 144 the R9
slot. Coordinate 8's supplied top sibling sits at `topSlot 8 child` (offset 0 or 144). -/
def headerBytes (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
    zeros 16 ++ bytesLE 4 (w.counters 3) ++ zeros 108 ++
    (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
    zeros 16
def authByte (child : Nat) (op : WCT9.Opening) (p : Nat) : UInt8 :=
  match (List.finRange 7).find? (fun l => decide (authSibOff child l.val ≤ p ∧ p < authSibOff child l.val + 16)) with
  | some l => (bytesLE 16 (op.path l)).getD (p - authSibOff child l.val) 0
  | none => 0
/-- Nested FTS (r1-1): the fold blocks of levels 0..4 (`[0, 320)` of a region); levels 5 and 6 are placed
elsewhere. -/
def authByte5 (child : Nat) (op : WCT9.Opening) (p : Nat) : UInt8 :=
  match (List.finRange 5).find? (fun l => decide (authSibOff child l.val ≤ p ∧ p < authSibOff child l.val + 16)) with
  | some l => (bytesLE 16 (op.path (Fin.castLE (by decide) l))).getD (p - authSibOff child l.val) 0
  | none => 0
def merkleBytes (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.range 320).map (authByte5 child op)
def chainBytes (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 5).reverse.flatMap fun i => zeros 48 ++ bytesLE 16 (op.values i.succ)
/-- Leaf block: `end0 | header slot (zero) | leaf pad | end1..end5`. -/
def leafBytes (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  bytesLE 16 (op.values 0) ++ zeros 16 ++ pad ++ (List.finRange 5).flatMap fun i => bytesLE 16 (op.values i.succ)
/-- Nested FTS (r1-1): the level-6 fold block `[left | header (zero) | pad | right]` at offset 832 of a region; the
supplied level-5 sibling is on the side opposite the computed value. -/
def topBlockBytes (child : Nat) (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  (if child / 2 ^ 5 % 2 = 1 then bytesLE 16 (op.path 5) else zeros 16) ++ zeros 16 ++ pad ++
    (if child / 2 ^ 5 % 2 = 0 then bytesLE 16 (op.path 5) else zeros 16)
/-- Region of coordinate `k` (896 bytes). `padL`/`padZ` hold coordinate `k - 1`'s supplied top sibling (16 bytes in
one of them, zeros in the other; both zero for `k = 0`). -/
def regionBytes (child : Nat) (op : WCT9.Opening) (padL padZ : List UInt8) : List UInt8 :=
  merkleBytes child op ++ chainBytes op ++ zeros 48 ++ leafBytes op padL ++ zeros 16 ++ topBlockBytes child op padZ
/-- Coordinate `k - 1`'s top sibling in coordinate `k`'s leaf pad (bit 6 of its child set) or level-6 pad. -/
def prevSibL (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : List UInt8 :=
  if k = 0 then zeros 16 else
    if (WCT9.child N (Fin.ofNat 9 (k - 1))).val / 2 ^ 6 % 2 = 1 then
      bytesLE 16 ((sig.openings (Fin.ofNat 9 (k - 1))).path 6) else zeros 16
def prevSibZ (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : List UInt8 :=
  if k = 0 then zeros 16 else
    if (WCT9.child N (Fin.ofNat 9 (k - 1))).val / 2 ^ 6 % 2 = 0 then
      bytesLE 16 ((sig.openings (Fin.ofNat 9 (k - 1))).path 6) else zeros 16
def wctBytes (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).reverse.flatMap fun k =>
    regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val) ++
      (if k.val = 0 then zeros 16 else [])
def lowerSibSlot (lay : Layer) (leaf j : Nat) : Nat := 16 * (lowerPlan lay leaf).getD j 0 + sibOff (leaf / 2 ^ j % 2)
def lowerCtrSlot (lay : Layer) (leaf : Nat) : Nat := 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 32
def lowerPathByte (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) (p : Nat) : UInt8 :=
  match (List.finRange (height lay)).find?
      (fun j => decide (lowerSibSlot lay leaf j.val ≤ p ∧ p < lowerSibSlot lay leaf j.val + 16)) with
  | some j => (bytesLE 16 (ls.path j)).getD (p - lowerSibSlot lay leaf j.val) 0
  | none => if lowerCtrSlot lay leaf ≤ p ∧ p < lowerCtrSlot lay leaf + 4 then
      (bytesLE 4 ctr).getD (p - lowerCtrSlot lay leaf) 0 else 0
def lowerPathBytes (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  (List.range (16 * pathSlots lay)).map (lowerPathByte lay leaf ls ctr)
def layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then layerBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
  else lowerPathBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
      (w.counters (Fin.ofNat 4 (lay.val - 1))) ++
    (layerBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)).drop (64 * height lay)
def endpointBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  (List.finRange (chainCount lay)).flatMap fun i => bytesLE 16 ((sig.layers lay).values i)
def leafBufferBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  if lay = 0 then zeros 32 ++ endpointBytes sig lay ++ zeros 16
  else (endpointBytes sig lay).take 16 ++ zeros 16 ++ (endpointBytes sig lay).drop 16 ++ zeros (if lay = 1 then 32 else 16)
def leafBuffersBytes (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 4).reverse.flatMap (leafBufferBytes sig)
def tailBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter ++ zeros 4
def witList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++ leafBuffersBytes w.signature ++ tailBytes w
def witEnc (N : HashOutput) (w : WCT9.Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))
def expandB (message : Message) (pk : Digest) (sig : WCT9.Signature) : M (Option WBytes) :=
  (Option.map fun x => witEnc x.1 x.2) <$> expandN message pk sig
def witDecP (N : HashOutput) (w : WBytes) : WCT9.Witness where
  signature :=
    { rho := wrho w
      openings := fun k =>
        ⟨fun t => wreveal w k.val t.val (WCT9.wordDigit (WCT9.rank N k) t),
          fun l => wsib w k.val (WCT9.child N k).val l.val⟩
      layers := fun lay =>
        ⟨fun i => wvalue w lay i.val, fun j => wpath w lay (route (WCT9.digestIndex N) lay).1 j.val⟩ }
  digestCounter := wdc w
  counters := fun lay => wbcCtr w (WCT9.digestIndex N) lay
def padDecP (N : HashOutput) (w : WBytes) : Pads where
  wctChain k t := wcpads w k.val t.val
  wctChainHigh k t := wcHeaderPad w k.val t.val
  wctMerkle k l := if l.val < 5 ∨ (l.val = 5 ∧ k.val = 0) then wmpad w k.val (WCT9.child N k).val l.val else 0
  wctMerkleHigh k l := wmhpad w k.val (WCT9.child N k).val l.val
  wctLeaf k := if k.val = 0 then wleafPad w 0 else 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := if j.val + 1 < height lay ∨ lay.val = 0 then
    wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val else 0
  chainHeader lay i := wchainHeaderPad w lay i.val
  bc lay := wbcPad w (WCT9.digestIndex N) lay
  bcRight := wbcRight w
  endpointMask lay i := wvalue w lay i.val ^^^ wdig w (leafBufferSlot lay i.val)
@[simp] theorem valueP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) :
    valueP (witDecP N w).signature (padDecP N w) lay digits i = wvalueFor w lay digits i.val := by
  simp [valueP, witDecP, padDecP, wvalueFor, BitVec.xor_assoc]
def Shaped (N : HashOutput) (_w : WBytes) : Prop := WCT9.admissible N = true
instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some top ← wctP w N | pure false
  let some root ← layersBC w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def rejectTail (w : WBytes) (N : HashOutput) : M Bool :=
  if !gateOk N then pure false else (fun _ => false) <$> wctP w N
end ClaudeWCT.W9.T3M
