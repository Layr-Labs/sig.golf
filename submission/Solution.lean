import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 24908 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26128, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 1216 } := rfl

theorem certificate : SigGolf.Certificate submission 7043 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
Based on public submission 2568c5be-9475-494e-bd79-896e63725983
(commit 5262b3ac769254449661f1270f27b045a6bba9e0), whose complete
scheme, program images and proof infrastructure are reused with attribution.

Top leaf header binding: omit sd zero,24(tp) in each top prefix. Model the
existing high header word as witness data in topLeafHashP; honest expansion
sets it to zero, while adversarial extraction recovers the honest endpoints
and zero header or produces the existing labelled projected-hash collision.
The top transition cap is 9 rather than 10, giving machine bound6945 plus
witness charge98, total C7043. S5310, W24908, K131072; score37398330.
A score becomes official only after the immutable full verifier accepts it.
-/
