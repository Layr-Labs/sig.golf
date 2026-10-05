import SigGolfCandidate.T3M.Sim

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy
def TopEncQ (q : Query) : Prop :=
  ∃ input : List UInt8, input.length = 64 ∧ q = toQ input ∧
    ∃ tr p ix, (input.drop 16).take 16 = SphincsSecurity.bytesLE 16 (T3.header 4 0 tr p ix)
def HashOk (hash : Hash) : Prop :=
  ∀ q, TopEncQ q → ∀ ds, T3.decode 0 ((hash q).extractLsb' 0 128) = some ds →
    9 ≤ T3.topCredit ((hash q).extractLsb' 0 128)
end SigGolfCandidate.T3M.Verify
