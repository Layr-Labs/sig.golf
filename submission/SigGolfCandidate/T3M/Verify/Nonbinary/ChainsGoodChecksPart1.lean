import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart0

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_2_0_part_0 : (List.range' 0 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_0_part_5 : (List.range' 5 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_0_part_10 : (List.range' 10 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_0_part_15 : (List.range' 15 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_0_part_20 : (List.range' 20 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_0 : (List.range' 0 25).all (inlineCheck 2) = true := by
  exact (@check_range_add (inlineCheck 2) 0 5 20 inlineBatch_2_0_part_0 (@check_range_add (inlineCheck 2) 5 5 15 inlineBatch_2_0_part_5 (@check_range_add (inlineCheck 2) 10 5 10 inlineBatch_2_0_part_10 (@check_range_add (inlineCheck 2) 15 5 5 inlineBatch_2_0_part_15 inlineBatch_2_0_part_20))))
theorem inlineGroupCheck_2_0 : inlineGroupCheck 2 0 25=true := by
  exact inlineBatch_2_0
private theorem inlineBatch_2_25_part_25 : (List.range' 25 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_25_part_30 : (List.range' 30 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_25_part_35 : (List.range' 35 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_25_part_40 : (List.range' 40 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_25_part_45 : (List.range' 45 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_25 : (List.range' 25 25).all (inlineCheck 2) = true := by
  exact (@check_range_add (inlineCheck 2) 25 5 20 inlineBatch_2_25_part_25 (@check_range_add (inlineCheck 2) 30 5 15 inlineBatch_2_25_part_30 (@check_range_add (inlineCheck 2) 35 5 10 inlineBatch_2_25_part_35 (@check_range_add (inlineCheck 2) 40 5 5 inlineBatch_2_25_part_40 inlineBatch_2_25_part_45))))
theorem inlineGroupCheck_2_25 : inlineGroupCheck 2 25 25=true := by
  exact inlineBatch_2_25
private theorem inlineBatch_2_50_part_50 : (List.range' 50 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_50_part_55 : (List.range' 55 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_50_part_60 : (List.range' 60 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_50_part_65 : (List.range' 65 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_50_part_70 : (List.range' 70 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_50 : (List.range' 50 25).all (inlineCheck 2) = true := by
  exact (@check_range_add (inlineCheck 2) 50 5 20 inlineBatch_2_50_part_50 (@check_range_add (inlineCheck 2) 55 5 15 inlineBatch_2_50_part_55 (@check_range_add (inlineCheck 2) 60 5 10 inlineBatch_2_50_part_60 (@check_range_add (inlineCheck 2) 65 5 5 inlineBatch_2_50_part_65 inlineBatch_2_50_part_70))))
theorem inlineGroupCheck_2_50 : inlineGroupCheck 2 50 25=true := by
  exact inlineBatch_2_50
private theorem inlineBatch_2_75_part_75 : (List.range' 75 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_75_part_80 : (List.range' 80 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_75_part_85 : (List.range' 85 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_75_part_90 : (List.range' 90 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_75_part_95 : (List.range' 95 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_75 : (List.range' 75 25).all (inlineCheck 2) = true := by
  exact (@check_range_add (inlineCheck 2) 75 5 20 inlineBatch_2_75_part_75 (@check_range_add (inlineCheck 2) 80 5 15 inlineBatch_2_75_part_80 (@check_range_add (inlineCheck 2) 85 5 10 inlineBatch_2_75_part_85 (@check_range_add (inlineCheck 2) 90 5 5 inlineBatch_2_75_part_90 inlineBatch_2_75_part_95))))
theorem inlineGroupCheck_2_75 : inlineGroupCheck 2 75 25=true := by
  exact inlineBatch_2_75
private theorem inlineBatch_2_100_part_100 : (List.range' 100 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_100_part_105 : (List.range' 105 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_100_part_110 : (List.range' 110 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_100_part_115 : (List.range' 115 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_100_part_120 : (List.range' 120 5).all (inlineCheck 2) = true := by decide +kernel
private theorem inlineBatch_2_100 : (List.range' 100 25).all (inlineCheck 2) = true := by
  exact (@check_range_add (inlineCheck 2) 100 5 20 inlineBatch_2_100_part_100 (@check_range_add (inlineCheck 2) 105 5 15 inlineBatch_2_100_part_105 (@check_range_add (inlineCheck 2) 110 5 10 inlineBatch_2_100_part_110 (@check_range_add (inlineCheck 2) 115 5 5 inlineBatch_2_100_part_115 inlineBatch_2_100_part_120))))
theorem inlineGroupCheck_2_100 : inlineGroupCheck 2 100 25=true := by
  exact inlineBatch_2_100
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_3_0_part_0 : (List.range' 0 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_0_part_5 : (List.range' 5 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_0_part_10 : (List.range' 10 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_0_part_15 : (List.range' 15 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_0_part_20 : (List.range' 20 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_0 : (List.range' 0 25).all (inlineCheck 3) = true := by
  exact (@check_range_add (inlineCheck 3) 0 5 20 inlineBatch_3_0_part_0 (@check_range_add (inlineCheck 3) 5 5 15 inlineBatch_3_0_part_5 (@check_range_add (inlineCheck 3) 10 5 10 inlineBatch_3_0_part_10 (@check_range_add (inlineCheck 3) 15 5 5 inlineBatch_3_0_part_15 inlineBatch_3_0_part_20))))
theorem inlineGroupCheck_3_0 : inlineGroupCheck 3 0 25=true := by
  exact inlineBatch_3_0
private theorem inlineBatch_3_25_part_25 : (List.range' 25 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_25_part_30 : (List.range' 30 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_25_part_35 : (List.range' 35 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_25_part_40 : (List.range' 40 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_25_part_45 : (List.range' 45 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_25 : (List.range' 25 25).all (inlineCheck 3) = true := by
  exact (@check_range_add (inlineCheck 3) 25 5 20 inlineBatch_3_25_part_25 (@check_range_add (inlineCheck 3) 30 5 15 inlineBatch_3_25_part_30 (@check_range_add (inlineCheck 3) 35 5 10 inlineBatch_3_25_part_35 (@check_range_add (inlineCheck 3) 40 5 5 inlineBatch_3_25_part_40 inlineBatch_3_25_part_45))))
theorem inlineGroupCheck_3_25 : inlineGroupCheck 3 25 25=true := by
  exact inlineBatch_3_25
private theorem inlineBatch_3_50_part_50 : (List.range' 50 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_50_part_55 : (List.range' 55 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_50_part_60 : (List.range' 60 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_50_part_65 : (List.range' 65 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_50_part_70 : (List.range' 70 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_50 : (List.range' 50 25).all (inlineCheck 3) = true := by
  exact (@check_range_add (inlineCheck 3) 50 5 20 inlineBatch_3_50_part_50 (@check_range_add (inlineCheck 3) 55 5 15 inlineBatch_3_50_part_55 (@check_range_add (inlineCheck 3) 60 5 10 inlineBatch_3_50_part_60 (@check_range_add (inlineCheck 3) 65 5 5 inlineBatch_3_50_part_65 inlineBatch_3_50_part_70))))
theorem inlineGroupCheck_3_50 : inlineGroupCheck 3 50 25=true := by
  exact inlineBatch_3_50
private theorem inlineBatch_3_75_part_75 : (List.range' 75 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_75_part_80 : (List.range' 80 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_75_part_85 : (List.range' 85 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_75_part_90 : (List.range' 90 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_75_part_95 : (List.range' 95 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_75 : (List.range' 75 25).all (inlineCheck 3) = true := by
  exact (@check_range_add (inlineCheck 3) 75 5 20 inlineBatch_3_75_part_75 (@check_range_add (inlineCheck 3) 80 5 15 inlineBatch_3_75_part_80 (@check_range_add (inlineCheck 3) 85 5 10 inlineBatch_3_75_part_85 (@check_range_add (inlineCheck 3) 90 5 5 inlineBatch_3_75_part_90 inlineBatch_3_75_part_95))))
theorem inlineGroupCheck_3_75 : inlineGroupCheck 3 75 25=true := by
  exact inlineBatch_3_75
private theorem inlineBatch_3_100_part_100 : (List.range' 100 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_100_part_105 : (List.range' 105 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_100_part_110 : (List.range' 110 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_100_part_115 : (List.range' 115 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_100_part_120 : (List.range' 120 5).all (inlineCheck 3) = true := by decide +kernel
private theorem inlineBatch_3_100 : (List.range' 100 25).all (inlineCheck 3) = true := by
  exact (@check_range_add (inlineCheck 3) 100 5 20 inlineBatch_3_100_part_100 (@check_range_add (inlineCheck 3) 105 5 15 inlineBatch_3_100_part_105 (@check_range_add (inlineCheck 3) 110 5 10 inlineBatch_3_100_part_110 (@check_range_add (inlineCheck 3) 115 5 5 inlineBatch_3_100_part_115 inlineBatch_3_100_part_120))))
theorem inlineGroupCheck_3_100 : inlineGroupCheck 3 100 25=true := by
  exact inlineBatch_3_100
end SigGolfCandidate.T3M.Nonbinary
end
end
