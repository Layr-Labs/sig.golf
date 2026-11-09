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

theorem certificate : SigGolf.Certificate submission 6971 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Proposed pool-71 / top-floor-18 retuning of the inherited Z5 scheme.
   The exact signing-envelope numerator is
   680529817020207430736995740672230147091 over 2^128 (< 1.99990).
   The top counter window is enlarged to 2^21, restoring the inherited
   433-bit tail and 139-bit security context bound. The top per-trial
   termination allowance is tightened from 755 to 350 using the T51 kernel.
   Claim C = 6971 requires independent accepting verification. -/
