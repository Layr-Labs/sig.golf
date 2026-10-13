import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy
/-- An encoding query of layer `lay` (campaign S1): a 64-byte block whose tweak is a one-word hyper label
`hp ++ hyperWord lay routed`, with any high word `hp` (the verifier reads it from the witness; the signer writes 0). -/
def EncQ (lay : Nat) (q : Query) : Prop :=
  ∃ input : List UInt8, input.length = 64 ∧ q = toQ input ∧
    ∃ (routed : Nat) (hp : BitVec 64), (input.drop 16).take 16 = SphincsSecurity.bytesLE 16 (hp ++ T3.hyperWord lay routed)
abbrev TopEncQ (q : Query) : Prop := EncQ 0 q
def HashOk (hash : Hash) : Prop :=
  ∀ (lay : T3.Layer) q, EncQ lay.val q → ∀ ds, T3.decode lay (ClaudeWCT.WCT9.encodingAnswer lay (hash q)) = some ds →
    ClaudeWCT.WCT9.producerFloor lay + ClaudeWCT.WCT9.dispatchPenalty lay ds ≤
      ClaudeWCT.WCT9.wordCredit lay ds + 4 * ClaudeWCT.WCT9.savedCopies lay ds
end SigGolfCandidate.T3M.Verify
