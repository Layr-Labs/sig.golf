import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart7

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_13_0_part_0 : (List.range' 0 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_0_part_5 : (List.range' 5 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_0_part_10 : (List.range' 10 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_0_part_15 : (List.range' 15 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_0_part_20 : (List.range' 20 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_0 : (List.range' 0 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 0 5 20 inlineBatch_13_0_part_0 (@check_range_add (inlineCheck 13) 5 5 15 inlineBatch_13_0_part_5 (@check_range_add (inlineCheck 13) 10 5 10 inlineBatch_13_0_part_10 (@check_range_add (inlineCheck 13) 15 5 5 inlineBatch_13_0_part_15 inlineBatch_13_0_part_20))))
theorem inlineGroupCheck_13_0 : inlineGroupCheck 13 0 25=true := by
  exact inlineBatch_13_0
private theorem inlineBatch_13_25_part_25 : (List.range' 25 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_30 : (List.range' 30 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_35 : (List.range' 35 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_40 : (List.range' 40 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_45 : (List.range' 45 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25 : (List.range' 25 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 25 5 20 inlineBatch_13_25_part_25 (@check_range_add (inlineCheck 13) 30 5 15 inlineBatch_13_25_part_30 (@check_range_add (inlineCheck 13) 35 5 10 inlineBatch_13_25_part_35 (@check_range_add (inlineCheck 13) 40 5 5 inlineBatch_13_25_part_40 inlineBatch_13_25_part_45))))
theorem inlineGroupCheck_13_25 : inlineGroupCheck 13 25 25=true := by
  exact inlineBatch_13_25
private theorem inlineBatch_13_50_part_50 : (List.range' 50 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_55 : (List.range' 55 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_60 : (List.range' 60 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_65 : (List.range' 65 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_70 : (List.range' 70 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50 : (List.range' 50 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 50 5 20 inlineBatch_13_50_part_50 (@check_range_add (inlineCheck 13) 55 5 15 inlineBatch_13_50_part_55 (@check_range_add (inlineCheck 13) 60 5 10 inlineBatch_13_50_part_60 (@check_range_add (inlineCheck 13) 65 5 5 inlineBatch_13_50_part_65 inlineBatch_13_50_part_70))))
theorem inlineGroupCheck_13_50 : inlineGroupCheck 13 50 25=true := by
  exact inlineBatch_13_50
private theorem inlineBatch_13_75_part_75 : (List.range' 75 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_80 : (List.range' 80 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_85 : (List.range' 85 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_90 : (List.range' 90 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_95 : (List.range' 95 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75 : (List.range' 75 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 75 5 20 inlineBatch_13_75_part_75 (@check_range_add (inlineCheck 13) 80 5 15 inlineBatch_13_75_part_80 (@check_range_add (inlineCheck 13) 85 5 10 inlineBatch_13_75_part_85 (@check_range_add (inlineCheck 13) 90 5 5 inlineBatch_13_75_part_90 inlineBatch_13_75_part_95))))
theorem inlineGroupCheck_13_75 : inlineGroupCheck 13 75 25=true := by
  exact inlineBatch_13_75
private theorem inlineBatch_13_100_part_100 : (List.range' 100 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_100_part_105 : (List.range' 105 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_100_part_110 : (List.range' 110 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_100_part_115 : (List.range' 115 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_100_part_120 : (List.range' 120 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_100 : (List.range' 100 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 100 5 20 inlineBatch_13_100_part_100 (@check_range_add (inlineCheck 13) 105 5 15 inlineBatch_13_100_part_105 (@check_range_add (inlineCheck 13) 110 5 10 inlineBatch_13_100_part_110 (@check_range_add (inlineCheck 13) 115 5 5 inlineBatch_13_100_part_115 inlineBatch_13_100_part_120))))
theorem inlineGroupCheck_13_100 : inlineGroupCheck 13 100 25=true := by
  exact inlineBatch_13_100
end SigGolfCandidate.T3M.Nonbinary
end
end
