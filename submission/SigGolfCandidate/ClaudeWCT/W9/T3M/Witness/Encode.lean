import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (zeros layerBytes sibOff)
open SphincsSecurity (bytesLE)
def expandN (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) := do
  let some (counter, output) ← WCT9.digestSearch sig.rho message 0 WCT9.digestAttemptLimit | pure none
  let index := WCT9.digestIndex output
  let root ← WCT9.recoverFts sig index output
  let some (root, counters) ← WCT9.expandLayersBC sig index 4 (.forest root) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
def headerBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++ zeros 28
def authByte (child : Nat) (op : WCT9.Opening) (p : Nat) : UInt8 :=
  match (List.finRange 7).find? (fun l => decide (authSibOff child l.val ≤ p ∧ p < authSibOff child l.val + 16)) with
  | some l => (bytesLE 16 (op.path l)).getD (p - authSibOff child l.val) 0
  | none => 0
def merkleBytes (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.range 320).map (authByte child op)
def chainBytes (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 6).reverse.flatMap fun i => zeros 48 ++ bytesLE 16 (op.values i.succ)
def leafBytes (op : WCT9.Opening) : List UInt8 :=
  bytesLE 16 (op.values 0) ++ zeros 16 ++ (List.finRange 6).flatMap fun i => bytesLE 16 (op.values i.succ)
def regionBytes (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  merkleBytes child op ++ chainBytes op ++ zeros 48 ++ leafBytes op ++ zeros 16
def wctBytes (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).reverse.flatMap fun k =>
    (regionBytes (WCT9.child N k).val (sig.openings k)).take (if k.val = 0 then 896 else 880)
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
def tailBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter ++ zeros 4
def witList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++ tailBytes w
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
  wctMerkle k l := if l.val < 6 then wmpad w k.val (WCT9.child N k).val l.val else 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := if j.val + 1 < height lay ∨ lay.val = 0 then
    wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val else 0
  chainHeader lay i := wchainHeaderPad w lay i.val
  bc lay := wbcPad w (WCT9.digestIndex N) lay
  bcRight := wbcRight w
def Shaped (N : HashOutput) (_w : WBytes) : Prop := WCT9.admissible N = true
instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some root ← wctP w N | pure false
  let some root ← layersBC w index 4 (.forest root) | pure false
  pure (root == pk)
def rejectTail (w : WBytes) (N : HashOutput) : M Bool :=
  if !gateOk N then pure false else (fun _ => false) <$> wctP w N
end ClaudeWCT.W9.T3M
