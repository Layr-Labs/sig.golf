import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy
/-- An encoding query of layer `lay`: a 64-byte block whose tweak is `hp ++ hyperWord lay routed` for some high word
`hp` (C2/C3 FULL: the verifier reads the row tweak's high word from the witness; honest 1). Adapted from b3cc11b. -/
def EncQ (lay : Nat) (q : Query) : Prop :=
  ∃ input : List UInt8, input.length = 64 ∧ q = toQ input ∧
    ∃ (routed : Nat) (hp : BitVec 64), (input.drop 16).take 16 = SphincsSecurity.bytesLE 16 (hp ++ T3.hyperWord lay routed)
abbrev TopEncQ (q : Query) : Prop := EncQ 0 q
def HashOk (hash : Hash) : Prop :=
  ∀ (lay : T3.Layer) q, EncQ lay.val q → ∀ ds, T3.decode lay (ClaudeWCT.WCT9.encodingAnswer lay (hash q)) = some ds →
    ClaudeWCT.WCT9.producerFloor lay + ClaudeWCT.WCT9.dispatchPenalty lay ds ≤
      ClaudeWCT.WCT9.wordCredit lay ds + 4 * ClaudeWCT.WCT9.savedCopies lay ds
end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy
/-- Fixed per-layer credit allowances for one honest canonical path. -/
def HashOkBy (floors : T3.Layer → Nat) (hash : Hash) : Prop :=
  ∀ (lay : T3.Layer) q, EncQ lay.val q → ∀ ds,
    ClaudeWCT.WCT9.CanonicalPolicy.decode lay (ClaudeWCT.WCT9.encodingAnswer lay (hash q)) = some ds →
    floors lay + ClaudeWCT.WCT9.dispatchPenalty lay ds ≤
      ClaudeWCT.WCT9.wordCredit lay ds + 4 * ClaudeWCT.WCT9.savedCopies lay ds
/-- The cap is far above any needed path allocation and keeps Nat subtraction exact. -/
def CreditFloors (floors : T3.Layer → Nat) : Prop :=
  (∀ lay, floors lay ≤ 301) ∧ 63 ≤ ((List.finRange 4).map floors).sum
end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
/-- Clip excess producer credit without needing a per-digit upper bound. -/
theorem creditFloors_clip (credits : T3.Layer → Nat)
    (h : 63 ≤ ((List.finRange 4).map credits).sum) :
    CreditFloors (fun lay => min 63 (credits lay)) := by
  constructor
  · intro lay
    exact (Nat.min_le_left _ _).trans (by decide)
  · change 63 ≤ credits 0 + (credits 1 + (credits 2 + (credits 3 + 0))) at h
    change 63 ≤ min 63 (credits 0) + (min 63 (credits 1) +
      (min 63 (credits 2) + (min 63 (credits 3) + 0)))
    omega
end SigGolfCandidate.T3M.Verify
