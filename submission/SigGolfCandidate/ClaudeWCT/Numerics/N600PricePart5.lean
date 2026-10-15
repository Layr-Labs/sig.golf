import SigGolfCandidate.ClaudeWCT.Numerics.N600PriceGeneratedLow
import SigGolfCandidate.ClaudeWCT.Numerics.N600PriceGeneratedHigh

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedFees

theorem convolution_rows_checked (r : Nat) (hlo : 5 ≤ r) (hhi : r ≤ 18) :
    convolutionDots r (forest r)=certifiedPayoff r := by
  interval_cases r
  · exact convolution_5_checked
  · exact convolution_6_checked
  · exact convolution_7_checked
  · exact convolution_8_checked
  · exact convolution_9_checked
  · exact convolution_10_checked
  · exact convolution_11_checked
  · exact convolution_12_checked
  · exact convolution_13_checked
  · exact convolution_14_checked
  · exact convolution_15_checked
  · exact convolution_16_checked
  · exact convolution_17_checked
  · exact convolution_18_checked

end ClaudeWCT.Numerics.SharedGeneratedForest
