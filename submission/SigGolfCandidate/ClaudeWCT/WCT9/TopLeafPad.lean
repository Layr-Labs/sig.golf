import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)

def leafTweakW (lay : Layer) (tree leaf : Nat) (hi : BitVec 64) : BitVec 128 :=
  hi ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)

def leafInputW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (ends : List Digest) : HashInput :=
  if lay = 0 then
    bytesLE 16 pad ++ bytesLE 16 (leafTweakW lay tree leaf hi) ++ ends.flatMap (bytesLE 16)
  else
    bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (leafTweakW lay tree leaf hi) ++
      (ends.drop 1).flatMap (bytesLE 16)

-- This is intentionally different from public C3's lowerHash/lowerHigh definition.
def leafHashW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (ends : List Digest) : M Digest :=
  projHash (SigGolfCandidate.T3.leafHigh leaf) (leafInputW lay tree leaf pad hi ends)

theorem leafInputW_zero (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafInputW lay tree leaf 0 0 ends = SigGolfCandidate.T3.leafInput lay tree leaf ends := by
  unfold leafInputW leafTweakW SigGolfCandidate.T3.leafInput leafTweak
  split
  · rw [show bytesLE 16 (0 : Digest) = zero16 by decide]; rfl
  · rfl

theorem leafHashW_zero (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHashW lay tree leaf 0 0 ends = SigGolfCandidate.T3.leafHash lay tree leaf ends := by
  unfold leafHashW SigGolfCandidate.T3.leafHash
  rw [leafInputW_zero]


end ClaudeWCT.WCT9
