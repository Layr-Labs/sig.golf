import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheckParts

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_0_0_part_0 : (List.range' 0 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_0_part_5 : (List.range' 5 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_0_part_10 : (List.range' 10 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_0_part_15 : (List.range' 15 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_0_part_20 : (List.range' 20 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_0 : (List.range' 0 25).all (inlineCheck 0) = true := by
  exact (@check_range_add (inlineCheck 0) 0 5 20 inlineBatch_0_0_part_0 (@check_range_add (inlineCheck 0) 5 5 15 inlineBatch_0_0_part_5 (@check_range_add (inlineCheck 0) 10 5 10 inlineBatch_0_0_part_10 (@check_range_add (inlineCheck 0) 15 5 5 inlineBatch_0_0_part_15 inlineBatch_0_0_part_20))))
theorem inlineGroupCheck_0_0 : inlineGroupCheck 0 0 25=true := by
  exact inlineBatch_0_0
private theorem inlineBatch_0_25_part_25 : (List.range' 25 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_25_part_30 : (List.range' 30 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_25_part_35 : (List.range' 35 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_25_part_40 : (List.range' 40 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_25_part_45 : (List.range' 45 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_25 : (List.range' 25 25).all (inlineCheck 0) = true := by
  exact (@check_range_add (inlineCheck 0) 25 5 20 inlineBatch_0_25_part_25 (@check_range_add (inlineCheck 0) 30 5 15 inlineBatch_0_25_part_30 (@check_range_add (inlineCheck 0) 35 5 10 inlineBatch_0_25_part_35 (@check_range_add (inlineCheck 0) 40 5 5 inlineBatch_0_25_part_40 inlineBatch_0_25_part_45))))
theorem inlineGroupCheck_0_25 : inlineGroupCheck 0 25 25=true := by
  exact inlineBatch_0_25
private theorem inlineBatch_0_50_part_50 : (List.range' 50 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_50_part_55 : (List.range' 55 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_50_part_60 : (List.range' 60 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_50_part_65 : (List.range' 65 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_50_part_70 : (List.range' 70 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_50 : (List.range' 50 25).all (inlineCheck 0) = true := by
  exact (@check_range_add (inlineCheck 0) 50 5 20 inlineBatch_0_50_part_50 (@check_range_add (inlineCheck 0) 55 5 15 inlineBatch_0_50_part_55 (@check_range_add (inlineCheck 0) 60 5 10 inlineBatch_0_50_part_60 (@check_range_add (inlineCheck 0) 65 5 5 inlineBatch_0_50_part_65 inlineBatch_0_50_part_70))))
theorem inlineGroupCheck_0_50 : inlineGroupCheck 0 50 25=true := by
  exact inlineBatch_0_50
private theorem inlineBatch_0_75_part_75 : (List.range' 75 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_75_part_80 : (List.range' 80 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_75_part_85 : (List.range' 85 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_75_part_90 : (List.range' 90 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_75_part_95 : (List.range' 95 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_75 : (List.range' 75 25).all (inlineCheck 0) = true := by
  exact (@check_range_add (inlineCheck 0) 75 5 20 inlineBatch_0_75_part_75 (@check_range_add (inlineCheck 0) 80 5 15 inlineBatch_0_75_part_80 (@check_range_add (inlineCheck 0) 85 5 10 inlineBatch_0_75_part_85 (@check_range_add (inlineCheck 0) 90 5 5 inlineBatch_0_75_part_90 inlineBatch_0_75_part_95))))
theorem inlineGroupCheck_0_75 : inlineGroupCheck 0 75 25=true := by
  exact inlineBatch_0_75
private theorem inlineBatch_0_100_part_100 : (List.range' 100 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_100_part_105 : (List.range' 105 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_100_part_110 : (List.range' 110 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_100_part_115 : (List.range' 115 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_100_part_120 : (List.range' 120 5).all (inlineCheck 0) = true := by decide +kernel
private theorem inlineBatch_0_100 : (List.range' 100 25).all (inlineCheck 0) = true := by
  exact (@check_range_add (inlineCheck 0) 100 5 20 inlineBatch_0_100_part_100 (@check_range_add (inlineCheck 0) 105 5 15 inlineBatch_0_100_part_105 (@check_range_add (inlineCheck 0) 110 5 10 inlineBatch_0_100_part_110 (@check_range_add (inlineCheck 0) 115 5 5 inlineBatch_0_100_part_115 inlineBatch_0_100_part_120))))
theorem inlineGroupCheck_0_100 : inlineGroupCheck 0 100 25=true := by
  exact inlineBatch_0_100
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_1_0_part_0 : (List.range' 0 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_0_part_5 : (List.range' 5 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_0_part_10 : (List.range' 10 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_0_part_15 : (List.range' 15 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_0_part_20 : (List.range' 20 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_0 : (List.range' 0 25).all (inlineCheck 1) = true := by
  exact (@check_range_add (inlineCheck 1) 0 5 20 inlineBatch_1_0_part_0 (@check_range_add (inlineCheck 1) 5 5 15 inlineBatch_1_0_part_5 (@check_range_add (inlineCheck 1) 10 5 10 inlineBatch_1_0_part_10 (@check_range_add (inlineCheck 1) 15 5 5 inlineBatch_1_0_part_15 inlineBatch_1_0_part_20))))
theorem inlineGroupCheck_1_0 : inlineGroupCheck 1 0 25=true := by
  exact inlineBatch_1_0
private theorem inlineBatch_1_25_part_25 : (List.range' 25 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_25_part_30 : (List.range' 30 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_25_part_35 : (List.range' 35 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_25_part_40 : (List.range' 40 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_25_part_45 : (List.range' 45 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_25 : (List.range' 25 25).all (inlineCheck 1) = true := by
  exact (@check_range_add (inlineCheck 1) 25 5 20 inlineBatch_1_25_part_25 (@check_range_add (inlineCheck 1) 30 5 15 inlineBatch_1_25_part_30 (@check_range_add (inlineCheck 1) 35 5 10 inlineBatch_1_25_part_35 (@check_range_add (inlineCheck 1) 40 5 5 inlineBatch_1_25_part_40 inlineBatch_1_25_part_45))))
theorem inlineGroupCheck_1_25 : inlineGroupCheck 1 25 25=true := by
  exact inlineBatch_1_25
private theorem inlineBatch_1_50_part_50 : (List.range' 50 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_50_part_55 : (List.range' 55 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_50_part_60 : (List.range' 60 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_50_part_65 : (List.range' 65 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_50_part_70 : (List.range' 70 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_50 : (List.range' 50 25).all (inlineCheck 1) = true := by
  exact (@check_range_add (inlineCheck 1) 50 5 20 inlineBatch_1_50_part_50 (@check_range_add (inlineCheck 1) 55 5 15 inlineBatch_1_50_part_55 (@check_range_add (inlineCheck 1) 60 5 10 inlineBatch_1_50_part_60 (@check_range_add (inlineCheck 1) 65 5 5 inlineBatch_1_50_part_65 inlineBatch_1_50_part_70))))
theorem inlineGroupCheck_1_50 : inlineGroupCheck 1 50 25=true := by
  exact inlineBatch_1_50
private theorem inlineBatch_1_75_part_75 : (List.range' 75 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_75_part_80 : (List.range' 80 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_75_part_85 : (List.range' 85 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_75_part_90 : (List.range' 90 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_75_part_95 : (List.range' 95 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_75 : (List.range' 75 25).all (inlineCheck 1) = true := by
  exact (@check_range_add (inlineCheck 1) 75 5 20 inlineBatch_1_75_part_75 (@check_range_add (inlineCheck 1) 80 5 15 inlineBatch_1_75_part_80 (@check_range_add (inlineCheck 1) 85 5 10 inlineBatch_1_75_part_85 (@check_range_add (inlineCheck 1) 90 5 5 inlineBatch_1_75_part_90 inlineBatch_1_75_part_95))))
theorem inlineGroupCheck_1_75 : inlineGroupCheck 1 75 25=true := by
  exact inlineBatch_1_75
private theorem inlineBatch_1_100_part_100 : (List.range' 100 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_100_part_105 : (List.range' 105 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_100_part_110 : (List.range' 110 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_100_part_115 : (List.range' 115 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_100_part_120 : (List.range' 120 5).all (inlineCheck 1) = true := by decide +kernel
private theorem inlineBatch_1_100 : (List.range' 100 25).all (inlineCheck 1) = true := by
  exact (@check_range_add (inlineCheck 1) 100 5 20 inlineBatch_1_100_part_100 (@check_range_add (inlineCheck 1) 105 5 15 inlineBatch_1_100_part_105 (@check_range_add (inlineCheck 1) 110 5 10 inlineBatch_1_100_part_110 (@check_range_add (inlineCheck 1) 115 5 5 inlineBatch_1_100_part_115 inlineBatch_1_100_part_120))))
theorem inlineGroupCheck_1_100 : inlineGroupCheck 1 100 25=true := by
  exact inlineBatch_1_100
end SigGolfCandidate.T3M.Nonbinary
end
end
