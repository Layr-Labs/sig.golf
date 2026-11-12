import SigGolfCandidate.OuterGroundCore
import SigGolfCandidate.FtsVerify
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifierHash
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open W9Drv.SharedCanonical W9Machine SigGolfCandidate.Research.SharedForest

theorem hashN_eq (coord index heap n : Nat) (left right : Digest) :
    OuterGroundCore.hashN coord index heap n left right=
      (if coord=8 ∧ heap=3 then shortHash (wctTopInput coord index heap left (nDig n) right)
       else highHash (wctTopInput coord index heap left (nDig n) right)) := by
  unfold OuterGroundCore.hashN OuterGroundCore.trial ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.fTrial
  rw [ftsNodeInputN_eq_top]
  unfold nDig OuterGroundCore.value OuterGroundCore.offset
  by_cases h : coord=8 ∧ heap=3
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]
    rfl
#print axioms hashN_eq
end OuterVerifierHash
