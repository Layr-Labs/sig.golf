import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5192 := rfl

theorem witness_bytes : submission.sizes.witness = 22012 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26144, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4128 } := rfl

theorem certificate : SigGolf.Certificate submission 6981 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Public-cache zero masks and a 37-bit upper carrier, combined with the
   promoted 16-bit lower carrier. Declared sizes and cycle bound:
   S = 5192, W = 22012, K = 131072, C = 6981; product = 36,245,352.
   The inherited cap-776 signer, public verifier, and witness layout remain
   part of the certificate above. -/
