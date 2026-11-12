import SigGolfCandidate.OuterSigning
import SigGolfCandidate.OuterSignatureCodec
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace OuterExpand
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M.Paired
open SphincsSecurity (bytesLE)

def expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    M (Option (HashOutput × SigGolfCandidate.Research.SharedForest.Witness × List Nat)) := do
  if sig.policyHints.toNat ≥ 12288 then return none
  let sig0 := fillTopSignature sig 0
  let some (counter, output) ← sharedDigestSearch sig0.rho message 0 ClaudeWCT.WCT9.digestAttemptLimit | pure none
  let index := ClaudeWCT.WCT9.digestIndex output
  let forest ← OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) sig0.forest
  let some layers ← recoverHintedLayers sig0 index ((sig0.layers 0).path ClaudeWCT.WCT9.topJ)
    4 (.pair forest.1.1 forest.1.2) | pure none
  if !OuterSigning.policyHintsValid index sig0.policyHints layers.digits layers.lows then return none
  if layers.root = pk then
    return some (output, ⟨sig0, counter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true), layers.nonces,
      fun lay => layers.lowerNonces.getD lay.val [], forest.2.1, forest.2.2.1⟩, forest.2.2.2)
  let some c ← ClaudeWCT.WCT9.searchTop index layers.foldedTop ((sig0.layers 0).path ClaudeWCT.WCT9.topJ) pk ClaudeWCT.WCT9.searchFuel 1 | pure none
  pure (some (output, ⟨fillTopSignature sig0 c, counter, fun lay => layers.counters.getD lay.val 0,
    !(layers.lows.getD 0 true), layers.nonces, fun lay => layers.lowerNonces.getD lay.val [], forest.2.1,
    forest.2.2.1⟩, forest.2.2.2))


def outerCoord (k : Nat) : Nat := if k<4 then 2*k+1 else 8
def outerNoncePos (k : Nat) : Nat := W9Machine.V3.regionOffset (outerCoord k)+784+32

def outerNonceByte (nonces : List Nat) (i : Nat) (b : UInt8) : UInt8 :=
  match (List.range 5).find? (fun k => decide (outerNoncePos k ≤ i ∧ i < outerNoncePos k + 8)) with
  | some k => (bytesLE 8 (BitVec.ofNat 64 (nonces.getD k 0))).getD (i-outerNoncePos k) 0
  | none => b

def witEncOuter (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat) :
    ClaudeWCT.W9.T3M.WBytes :=
  BitVec.ofNat _ (readLE ((witListF16 output w).mapIdx fun i b => outerNonceByte nonces i b))

def expandCompact (message : Message) (pk : Digest) (sig : OuterSignatureCodec.NewSig) :
    M (Option ClaudeWCT.W9.T3M.WBytes) :=
  (Option.map (fun p => witEncOuter p.1 p.2.1 p.2.2)) <$>
    expandN message pk (ClaudeWCT.W9.T3M.SharedCodec.sigDecC (OuterSignatureCodec.expand sig))

def signCompact (cache : Cache) (message : Message) : M (Option OuterSignatureCodec.NewSig) :=
  (Option.map (fun s => OuterSignatureCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC s))) <$>
    OuterSigning.sign cache message

theorem outer_positions : (List.range 5).map (fun k => 4256+outerNoncePos k)=[11088,9392,7696,6000,5152] := by decide +kernel
#print axioms outer_positions
end OuterExpand
