import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5216 := rfl

theorem witness_bytes : submission.sizes.witness = 23236 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26144, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2904 } := rfl

theorem certificate : SigGolf.Certificate submission 7003 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Paired line (#900 paired FTS openings) with C1/C2/C3/C4, coordinate-8 hoist and pairing stage 1 (564ba604), plus
the restricted top-half choice with a witness hint and path-aware credit floors (top +3, lower +4).
R6 + RC (work in progress): radix-6 top (8 r6 + 9 r5 triples + r8 checksum, T 153), top floor 19, pool 73, FTS gate 804
(route C). Raw bound: 11 + (870 + 778) + 5253 = 6912. Witness charge: 91 (W 23236, witness offset 2904).
S=5216, W=23236, K=131072, C=7003; score=36527648 (main 05e8b118: 5248 x 6975 = 36604800). -/
