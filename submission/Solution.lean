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

theorem certificate : SigGolf.Certificate submission 6965 := by
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
   Z6: mpjunior92's dedicated-one elimination (8cff05d) on dda3ccf1: the
   verifier's `addi t2,zero,1` is removed (step-one stores use s1 with
   control words 0xfff01/0x7fc01, top root label 856064, FTS root label
   0xfff01).
   Y4: L-hyper A' (marker label words; -2 per run).
   Z6: option F (marker-only label words; the FTS node and leaf low
   words move by -2048, so no `ori 0x201`; -3 per run).
   199a9c8 (mpjunior92): credit pool 71, top floor 18, top counter window 2^21.
   Z7 (port of soispoke's f25ef952): R1 chain-0 ladder-tail reward and f25's L1/L2 floor tables,
   credit pool 72.
   Z7 stage 2 (port of soispoke's f25ef952): R6 rho/hint mixed radix (N = rho*5852 + t), skip-2 hint
   codec, N7g-B ground widths, top zero-bit reallocation, Route C gate 926 (adm 29249/2500000).
   Claimed S = 5187, W = 21756, K = 131072, C = 6965;
   product = 36,127,455. Independent acceptance remains required. -/
