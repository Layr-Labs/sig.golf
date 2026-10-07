import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

/-!
Reproducibility notes for the current four-stage stateless hash-based signature
submission. Keygen derives the public key and cache; sign produces a signature;
expand turns it into a witness; verify checks that witness.

The declared sizes are S = 5456 signature bytes, W = 21832 witness bytes, and
K = 131072 cache bytes. The certificate uses C = 7408 verification cycles,
decomposed by the proof as 19 + 1085 + 701 + 5517 + 86. The last term is the
ceil(W / 256) witness charge; the other terms are verification proof bounds.
These are static declarations and certified bounds, not measurements from an
accepting run. No accepting-run instruction/HASH profile is recorded here.

`SigGolf.Certificate` discharges six obligations: admission, completeness,
compressionBudgets, verificationCycles, security, and termination.

This documentation is an audit and reproduction aid only; it makes no score
improvement claim and changes no scheme behavior.
-/

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5456 := rfl

theorem witness_bytes : submission.sizes.witness = 21832 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 23880, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 7408 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate
