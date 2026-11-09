import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5187 := rfl

theorem witness_bytes : submission.sizes.witness = 21756 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26016, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4256 } := rfl

theorem certificate : SigGolf.Certificate submission 6972 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Inherit Z5's security split and the dedicated-one verifier optimization,
   retain pool 70 and top floor 17, and use a restricted hint alphabet with
   52 ground carrier bits to reduce the signature to 5187 bytes.
   Target C = 6972. Complete independent verification is required before
   claiming acceptance of this composition. -/
