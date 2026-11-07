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

theorem certificate : SigGolf.Certificate submission 6980 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Z3 on mpjunior92's a52c60c9 (top chain-1 copy omission, inlined final top pair): the WOTS
   marker bound uses chainCount <= 51 (per-chain rate 88, marker sum 4488), which lifts the
   route-C FTS gate to 826; the freed sign budget restores the E11 lower ground widths
   (3,3,2,1 on layer 1, 4,3,2,1 on layers 2, 3) for a 45-bit V carrier (top sibling bits
   32..76, 4-byte tail) at credit pool 66.
   Claimed S = 5188, W = 21756, K = 131072, C = 6980;
   product = 36,217,428. -/
