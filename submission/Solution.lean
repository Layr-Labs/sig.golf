import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5191 := rfl

theorem witness_bytes : submission.sizes.witness = 22012 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26144, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4128 } := rfl

theorem certificate : SigGolf.Certificate submission 6982 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- U24 extends the promoted public-cache zero-mask/37-bit upper carrier with
   a 24-bit lower carrier. Pool 66 pays for the additional lower-node grinding.
   S = 5191, W = 22012, K = 131072, C = 6982; product = 36,243,562.
   The public verifier image and witness layout are inherited unchanged. -/
