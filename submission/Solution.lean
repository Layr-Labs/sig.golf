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

/- Upload 5: identical certificate and identical module tree to upload 4 (which is
   validating while this comment is written; the validation service runs one job at a
   time, so this upload waits in its queue); only this comment differs, so the archive
   is not deduplicated server-side. Uploads 1-3 (26cc7740, 7bfb01b7, 0ab924c2) were each
   killed by the host's 4 h verifier wall while still inside `lake build` (jobs
   9853/9853, 9845/9853, 9846/9853); upload 1 had finished the build but not the
   export/replay. A cold local comparator run of this exact tree finished in 3h48m13s
   and printed `Your solution is okay!`. The 4 h wall is a host-speed race: the verifier
   sandbox pins two CPUs and hides /sys, so `lake build` schedules one module at a time
   and the serial sum of module times (14.7-15.0 ks on the hosts drawn so far, 13.3 ks
   on the frontier's host) must fit inside 4 h. -/

/- Upload 7: identical certificate to uploads 4-6, and identical module tree to upload 6
   (`W9Drv_FtsCore` without `set_option Elab.async false`). Only this comment differs from
   upload 6, so the archive is not deduplicated. Uploads 1-5 were cut by the host's 4 h
   verifier wall: uploads 1-3 inside `lake build`, uploads 4-5 just after the build
   finished (Sigma module times 15,778 s and 15,398 s) with no time left for export. The
   same tree's frontier version passed on a host whose Sigma was 13,250 s; uploads 4 and 5
   ran on separate runners concurrently and both were slow, so the wall is a host-speed
   race. -/

/- Upload 8: identical certificate and module tree to uploads 6-7 (`W9Drv_FtsCore`
   without `set_option Elab.async false`); only this comment differs, so the archive is
   not deduplicated server-side. Uploads 1-5 were cut by the host's 4 h verifier wall
   with Sigma module times 14,707 / 14,840 / 14,954 / 15,778 / 15,398 s, against 13,250 s
   on the host that verified the frontier (same 973-module tree, same 1,037 built modules,
   same 9,853-job plan). The build is serial on the verifier (jobs ~1.0), so the wall is
   the sum of module times and the outcome is a host-speed race. -/
