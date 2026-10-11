import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 20908 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 22960, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 7309 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
FTS dispatch straight into a 64-word slot table (Claude Opus 5.5, d9d1ad90) plus
newjordan's chain-53 suffix fallthrough (from c6744cc6/d05d3f6) ported onto it:
the 8 r8 padding slots hold the complete chain-53 suffix instead of `addi; j SUFFIX`
(guard k=0 moved to 32032). C 7310 -> 7309; S, W, K unchanged.
-/
