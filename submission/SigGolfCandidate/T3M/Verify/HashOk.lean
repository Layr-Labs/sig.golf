import SigGolfCandidate.T3M.Sim

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy
/-- Top-layer (layer 0) encoding queries: one 64-byte block whose header block (bytes 16..31) is an encoding header
(tag 4) of layer 0. -/
def TopEncQ (q : Query) : Prop :=
  ∃ input : List UInt8, input.length = 64 ∧ q = toQ input ∧
    ∃ tr p ix, (input.drop 16).take 16 = SphincsSecurity.bytesLE 16 (T3.header 4 0 tr p ix)
/-- The producer credit filter seen from the verifier: every top-encoding answer that decodes carries credit >= 9. -/
def HashOk (hash : Hash) : Prop :=
  ∀ q, TopEncQ q → ∀ ds, T3.decode 0 ((hash q).extractLsb' 0 128) = some ds →
    9 ≤ T3.topCredit ((hash q).extractLsb' 0 128)
end SigGolfCandidate.T3M.Verify
