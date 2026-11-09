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

theorem certificate : SigGolf.Certificate submission 6971 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Z5R: C13R68 (R6 rho/hint codec, R1 ladder reward, skip-2 hint codec)
   plus #993 levers: Z5 pre/post-marker WOTS split (Merge112S0/SA/SB/S/T),
   cap 776, Route C gate 926, sign pool 71, top floor 17.
   Claimed S = 5187, W = 21756, K = 131072, C = 6971;
   product = 36,158,577. Independent acceptance remains required.
   D1 (#992 port): dedicated constant-one initializer removed (verify word 77) using
   byte/control-word reuse and consistent root-label translations (verify -1 cycle). -/
