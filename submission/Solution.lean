import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5248 := rfl

theorem witness_bytes : submission.sizes.witness = 24924 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26144, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 1216 } := rfl

theorem certificate : SigGolf.Certificate submission 6997 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Paired C4 reconstruction on stage2 b881a25 plus coordinate-8 hoist 188758f.
C4 donor: e244da45126332f078d6c26ed610161462afa61d. Top-tree spill-down saves
12 stores, while the coordinate-label adjustment costs one instruction.
Raw bound: 11 + (870 + 778) + 5240 = 6899. Witness charge: 98.
S=5248, W=24924, K=131072, C=6997; score=36720256.
The reconstructed proofs are UNCOMPILED; see HANDOFF.md for fresh emulator
results, provenance, and the Mac build checklist. -/
