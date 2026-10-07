import SigGolfCandidate.T3.Secc.CaseCForecast

section
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 37/64) :
    (13/8)*(value-63/64)+2*mean*value ≤ value^2+mean^2 :=
  SigGolfResearch.Gate6.Excess.theta_excess_le_square value mean hvalue hmean
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W-63/64) ≤
      11324/100000000 :=
  fullPrice_excess_of_pointwise (63/64) theta_excess_le_square
end SigGolfCandidate.T3.BPORS.History
#print axioms SigGolfCandidate.T3.BPORS.History.theta_excess_le_square
#print axioms SigGolfCandidate.T3.BPORS.History.excess_three_quarters
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete (uniformWordAverage)
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 37/64) :
    (13/8) * (value - 63/64) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 :=
  BPORS.History.theta_excess_le_square value mean hvalue hmean
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta) ≤
      11324 / 100000000 := by
  have ht : (63/64 : ENNReal) ≤ theta := by
    unfold theta
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  refine (SphincsSecurity.Concrete.uniformWordAverage_mono BPORS.Numeric.proposalLength
    (fun W => tsub_le_tsub_left ht _)).trans
      BPORS.History.excess_three_quarters
end SigGolfCandidate.T3.Security.CaseC
end
