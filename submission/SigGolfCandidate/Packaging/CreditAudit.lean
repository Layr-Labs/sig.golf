import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace SigGolfCandidate.Packaging.CreditAudit
open SigGolfCandidate.T3 ClaudeWCT.WCT9

/-! These concrete source-decoder inputs attain the producer credit floors used by the
local chain-cost bounds. They do not establish an honest full execution or tightness
of the complete verification-cycle bound or score. -/

def topBoundary : Digest := BitVec.ofNat 128 0x007ffffffe7060c183060c1830625122
def topDigits : List Nat := List.replicate 8 3 ++ List.replicate 30 4 ++ List.replicate 16 0

theorem top_producer_accepts : producerDecode 0 topBoundary = some topDigits := by
  decide +kernel

theorem top_credit_eight : topCredit topBoundary = 8 := by
  decide +kernel

theorem top_producer_floor_attained : wordCredit 0 topDigits = producerFloor 0 := by
  decide +kernel

def lowerFiveBoundary : Digest := BitVec.ofNat 128 0x8000000001db6dffffffffffffffffff
def lowerFiveDigits : List Nat :=
  List.replicate 24 7 ++ List.replicate 5 6 ++ [1] ++ List.replicate 13 0

theorem lower_one_producer_accepts : producerDecode 1 lowerFiveBoundary = some lowerFiveDigits := by
  decide +kernel

theorem lower_two_producer_accepts : producerDecode 2 lowerFiveBoundary = some lowerFiveDigits := by
  decide +kernel

theorem lower_one_credit_five : wordCredit 1 lowerFiveDigits = 5 := by
  decide +kernel

theorem lower_two_credit_five : wordCredit 2 lowerFiveDigits = 5 := by
  decide +kernel

def lowerFourBoundary : Digest := BitVec.ofNat 128 0x8000000000db6fffffffffffffffffff
def lowerFourDigits : List Nat := List.replicate 25 7 ++ List.replicate 4 6 ++ List.replicate 14 0

theorem lower_three_producer_accepts : producerDecode 3 lowerFourBoundary = some lowerFourDigits := by
  decide +kernel

theorem lower_three_credit_four : wordCredit 3 lowerFourDigits = 4 := by
  decide +kernel

theorem lower_producer_floors_attained :
    wordCredit 1 lowerFiveDigits = producerFloor 1 ∧
    wordCredit 2 lowerFiveDigits = producerFloor 2 ∧
    wordCredit 3 lowerFourDigits = producerFloor 3 := by
  decide +kernel

end SigGolfCandidate.Packaging.CreditAudit
