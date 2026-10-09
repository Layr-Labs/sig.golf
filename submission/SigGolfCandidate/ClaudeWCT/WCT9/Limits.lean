import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
def digestAttemptLimit : Nat := 2 ^ 21
/- The verifier can accept the full serialized counter range without changing
the signer's bounded search.  The machine normalizes the upper padding word. -/
def digestVerifyWindow : Nat := 2 ^ 32
theorem digestAttemptLimit_eq : digestAttemptLimit = 2097152 := by
  norm_num [digestAttemptLimit]
theorem digestAttemptLimit_eq_two_mul : digestAttemptLimit = 2 * SigGolfCandidate.T3.attemptLimit := by
  norm_num [digestAttemptLimit, SigGolfCandidate.T3.attemptLimit]
theorem digestAttemptLimit_le : digestAttemptLimit ≤ 2 ^ 32 := by
  norm_num [digestAttemptLimit]
theorem attemptLimit_le_digestAttemptLimit : SigGolfCandidate.T3.attemptLimit ≤ digestAttemptLimit := by
  norm_num [digestAttemptLimit, SigGolfCandidate.T3.attemptLimit]
def signPayloadWith (limit : Nat) (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_, output) ← digestSearch rho message 0 limit | pure none
  let index := digestIndex output
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List (Digest × Digest)) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinateF index coord selected (rank output coord)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening],
        state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])) ([], [])
  let root ← forestPk index state.2
  let some layers ← signLayersBC cache index 4 (.forest root) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
def signWith (limit : Nat) (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayloadWith limit cache message
def expandWith (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    M (Option Witness) := do
  let some (counter, output) ← digestSearch sig.rho message 0 limit | pure none
  let index := digestIndex output
  let root ← recoverFts sig index output
  let some (root, counters) ← expandLayersBC sig index 4 (.forest root) | pure none
  if root ≠ pk then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)
def verifyWith (limit : Nat) (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ limit then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !admissible output then return false
  let index := digestIndex output
  let root ← recoverFts w.signature index output
  let some root ← verifyLayersBC w index 4 (.forest root) | pure false
  pure (root == pk)
theorem signPayloadWith_attemptLimit :
    signPayloadWith SigGolfCandidate.T3.attemptLimit = signPayload := rfl
theorem signWith_attemptLimit : signWith SigGolfCandidate.T3.attemptLimit = sign := rfl
theorem expandWith_attemptLimit : expandWith SigGolfCandidate.T3.attemptLimit = expand := rfl
theorem verifyWith_attemptLimit : verifyWith SigGolfCandidate.T3.attemptLimit = verify := rfl
/-! ### H2: the compact signature omits the top 16 bits of the top layer's level-11 sibling.
Expand recovers everything up to the level-11 node `v` with those bits zero, then searches the 2^16 completions
against the public key. The witness carries the completed signature, so verify is unchanged. -/
def setTop (d : Digest) (c : Nat) : Digest := BitVec.ofNat 128 (d.toNat % 2 ^ 112 + c % 2 ^ 16 * 2 ^ 112)
def fillLayer (lay : Layer) (ls : LayerSignature lay) (c : Nat) : LayerSignature lay :=
  ⟨ls.values, fun j => if lay.val = 0 ∧ j.val = 11 then setTop (ls.path j) c else ls.path j⟩
def fillTop (sig : Signature) (c : Nat) : Signature :=
  ⟨sig.rho, sig.openings, fun lay => fillLayer lay (sig.layers lay) c⟩
def proj (sig : Signature) : Signature := fillTop sig 0
def topJ : Fin (height 0) := ⟨11, by decide⟩
def topSib (sig : Signature) : Digest := (sig.layers 0).path topJ
def topStep (sig : Signature) (index : Nat) (value : Digest) (j : Fin (height 0)) : M Digest := do
  let other := (sig.layers 0).path j
  let pair := if (route index 0).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
  nodeHash 3 (0 : Layer).val (route index 0).2 (2 ^ (height 0 - j.val - 1) + (route index 0).1 / 2 ^ (j.val + 1))
    pair.1 pair.2
def topNode (index : Nat) (value other : Digest) : M Digest := do
  let pair := if (route index 0).1 / 2 ^ topJ.val % 2 = 0 then (value, other) else (other, value)
  nodeHash 3 (0 : Layer).val (route index 0).2 (2 ^ (height 0 - topJ.val - 1) + (route index 0).1 / 2 ^ (topJ.val + 1))
    pair.1 pair.2
def topEnds (sig : Signature) (index : Nat) (digits : List Nat) : M (List Digest) :=
  (List.finRange (chainCount 0)).mapM fun i =>
    SigGolfCandidate.T3.chain 0 (route index 0).2 (route index 0).1 i.val (digits.getD i.val 0)
      (maxDigit 0 i.val - digits.getD i.val 0) ((sig.layers 0).values i)
/-- The top layer folded to its level-11 node (the input of the last node hash). -/
def topFold (sig : Signature) (index : Nat) (digits : List Nat) : M Digest := do
  let ends ← topEnds sig index digits
  let value ← SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1 ends
  ((List.finRange (height 0)).take 11).foldlM (topStep sig index) value
/-- `expandLayersBC` that also returns the top layer's level-11 node and takes the top sibling as an argument. -/
def expandLayersT (sig : Signature) (index : Nat) (other : Digest) :
    Nat → LayerMsg → M (Option (Digest × Digest × List (BitVec 32)))
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits) ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay) | pure none
      if n = 0 then
        let v ← topFold sig index digits
        let root ← topNode index v other
        pure (some (v, root, [counter]))
      else
        let pair ← recoverLayerPair sig index lay digits
        let some (v, root, counters) ← expandLayersT sig index other n (.pair pair.1 pair.2) | pure none
        pure (some (v, root, counters ++ [counter]))
def searchFuel : Nat := 65535
/-- Candidates `c, c + 1, ...` for the omitted bits; the first whose root is `pk`. -/
def searchTop (index : Nat) (v sib pk : Digest) : Nat → Nat → M (Option Nat)
  | 0, _ => pure none
  | fuel + 1, c => do
      let root ← topNode index v (setTop sib c)
      if root = pk then pure (some c) else searchTop index v sib pk fuel (c + 1)
/-- The H2 expander on a signature whose omitted bits are ignored (read as zero). -/
def expandS (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    M (Option (HashOutput × Witness)) := do
  let sig0 := proj sig
  let some (counter, output) ← digestSearch sig0.rho message 0 limit | pure none
  let index := digestIndex output
  let root ← recoverFts sig0 index output
  let some (v, root, counters) ← expandLayersT sig0 index (topSib sig0) 4 (.forest root) | pure none
  if root = pk then return some (output, ⟨sig0, counter, fun lay => counters.getD lay.val 0⟩)
  let some c ← searchTop index v (topSib sig0) pk searchFuel 1 | pure none
  pure (some (output, ⟨fillTop sig0 c, counter, fun lay => counters.getD lay.val 0⟩))
namespace Rev3
def signPayload (cache : Cache) (message : Message) : M (Option Signature) :=
  signPayloadWith digestAttemptLimit cache message
def sign (cache : Cache) (message : Message) : M (Option Signature) :=
  signWith digestAttemptLimit cache message
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) :=
  Option.map Prod.snd <$> expandS digestAttemptLimit message pk sig
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool :=
  verifyWith digestAttemptLimit message pk w
def keygen : M (Digest × Cache) := ClaudeWCT.WCT9.keygen
theorem sign_eq (cache : Cache) (message : Message) : sign cache message = (do
    let tag ← privateMac cache.region
    if tag ≠ cache.tag then return none
    signPayload cache message) := rfl
end Rev3
end ClaudeWCT.WCT9
