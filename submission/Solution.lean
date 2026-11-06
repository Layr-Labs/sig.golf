import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5190 := rfl

theorem witness_bytes : submission.sizes.witness = 21756 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26016, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4256 } := rfl

theorem certificate : SigGolf.Certificate submission 6982 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- E11 on the E4 witness relayout: credit pool 65, a 29-bit lower carrier in 12
   ground slots (widths (3,3,2,1)(4,3,2,1)(4,3,2,1)), the keygen zero window at
   bits 101..107 and a 20-bit expand search (E11); the witness starts at 4256 and
   the message at 26016, W = 21756, witness charge 85 (E4). Declared sizes and
   cycle bound: S = 5190, W = 21756, K = 131072, C = 6982; product = 36,236,580. -/
