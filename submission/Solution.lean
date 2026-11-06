import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5189 := rfl

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

/- E8 stage 2 (S1 point P1) on E11 + E4 + E10 savings v2 + the P1 retune: 9 FTS
   heap-8..15 carrier slots (1,1,2,2,2,2,2,2,2 bits, ground-ground trials on the 72
   FTS nodes per signature) and lower ground widths (3,2,1,1)x3 give a 37-bit V
   carrier; the signature drops to 5,189 bytes. Expand re-derives the 9 FTS nonces
   in its search and writes them into the witness pads; verify is unchanged apart
   from the retune constants (cap 777, gate 812, pool 66; E1 phase 1 top bound).
   Declared sizes and cycle bound: S = 5189, W = 21756, K = 131072, C = 6982;
   product = 36,229,598. -/
