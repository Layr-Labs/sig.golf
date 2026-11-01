import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5195 := rfl

theorem witness_bytes : submission.sizes.witness = 22012 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26144, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4128 } := rfl

theorem certificate : SigGolf.Certificate submission 6987 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- M0 with the promoted cap-776 signer and its Route C certificate.
   Verify image: P2c + P5 + landing fix. Accepting runs save 10 cycles.
   Plus FTS digest-field repacking (dispatch 93 -> 85 words) and the topdigit lever (top body 345 -> 344).
   S = 5195, W = 22012, K = 131072, C = 6987; score = 36,297,465.
   Out-of-window lower words execute rank-checked chains before rejection,
   so the all-path cycle budget is 15,784. -/
