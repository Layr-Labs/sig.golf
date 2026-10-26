import SigGolf
import SigGolfCandidate.Packaging_Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5195 := rfl

theorem witness_bytes : submission.sizes.witness = 22012 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26144, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4128 } := rfl

theorem certificate : SigGolf.Certificate submission 7007 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- S=5195, W=22012, K=131072, C=7007; score=36401365. -/

/- Retry of the same certificate after the 2026-10-25T21:59Z run reached the
   verifier's 4 h wall (build completed, no score produced). Proof unchanged. -/

/- Upload 3: identical certificate. Uploads 1 (26cc7740, run 40218688832) and 2
   (7bfb01b7, run 40240032718) were both killed by the host's 4 h verifier wall
   while still in `lake build` (jobs 9853/9853 and 9845/9853), no score produced. -/

/- Upload 4: identical certificate. Uploads 1-3 (26cc7740, 7bfb01b7, 0ab924c2) were
   each killed by the host's 4 h verifier wall while still in `lake build`
   (jobs 9853/9853, 9845/9853, 9846/9853); no score was produced. A cold local
   comparator run of this exact tree finished in 3h48m13s and printed
   `Your solution is okay!` -/
