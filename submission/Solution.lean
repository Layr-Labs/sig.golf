import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5188 := rfl

theorem witness_bytes : submission.sizes.witness = 21756 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26016, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4256 } := rfl

theorem certificate : SigGolf.Certificate submission 6977 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Development candidate based on Z4 (f8127b2): use FTS node bias -67073
   and the aligned chain-label translation, remap FTS heap 7 to 64 and
   Top label 7 to 520192, and separate digest queries with low word 25984.
   The target removes three verifier setup instructions.
   Claimed S = 5188, W = 21756, K = 131072, C = 6977;
   product = 36,196,676. Independent acceptance remains required. -/
