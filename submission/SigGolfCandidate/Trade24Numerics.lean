import SigGolfCandidate.Merge044

/- Arithmetic feasibility of exchanging one verification credit for eight more
   packed lower-node bits. This records the arithmetic separately from the machine and codec proofs. -/
namespace SigGolfCandidate.Trade24
open ClaudeWCT.Numerics.CanonicalCompression

def initialBound66 : Nat := 366261175301868671147750736727906733560
def groundM4 : Nat := 340311161564765781666276742203532247926
def groundBound24 : Nat :=
  mulUp (powerUp (ClaudeWCT.Numerics.TopZero.groundM 1) 24)
    (mulUp (powerUp (ClaudeWCT.Numerics.TopZero.groundM 3) 12)
      (powerUp groundM4 6))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem initial_checked66 :
    recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram
      14 66 rowOne initialBound66 = true := by
  decide +kernel

theorem groundM4_checked :
    zNum * scale ≤ groundM4 * (16 * zDen - 15 * zNum) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem moment_checked24 :
    mulUp
      (mulUp (mulUp ClaudeWCT.Numerics.TopZero.fixedBoundU16 groundBound24) ftsBound)
      initialBound66 < 2 * scale := by
  decide +kernel

theorem score_improves : 5191 * 6982 < 5192 * 6981 := by decide +kernel
end SigGolfCandidate.Trade24
