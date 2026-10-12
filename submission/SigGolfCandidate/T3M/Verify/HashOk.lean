import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy
def EncQ (lay : Nat) (q : Query) : Prop :=
  ∃ input : List UInt8, input.length = 64 ∧ q = toQ input ∧
    ∃ routed, (input.drop 16).take 16 = SphincsSecurity.bytesLE 16 (1#64 ++ T3.hyperWord lay routed)
abbrev TopEncQ (q : Query) : Prop := EncQ 0 q
def HashOk (hash : Hash) : Prop :=
  ∀ (lay : T3.Layer) q, EncQ lay.val q → ∀ ds, T3.decode lay (ClaudeWCT.WCT9.encodingAnswer lay (hash q)) = some ds →
    ClaudeWCT.WCT9.producerFloor lay + ClaudeWCT.WCT9.dispatchPenalty lay ds ≤
      ClaudeWCT.WCT9.wordCredit lay ds + 4 * ClaudeWCT.WCT9.savedCopies lay ds
end SigGolfCandidate.T3M.Verify
