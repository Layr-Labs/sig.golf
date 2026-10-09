import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart9

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_15_0_part_0 : (List.range' 0 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_0_part_5 : (List.range' 5 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_0_part_10 : (List.range' 10 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_0_part_15 : (List.range' 15 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_0_part_20 : (List.range' 20 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_0 : (List.range' 0 25).all (inlineCheck 15) = true := by
  exact (@check_range_add (inlineCheck 15) 0 5 20 inlineBatch_15_0_part_0 (@check_range_add (inlineCheck 15) 5 5 15 inlineBatch_15_0_part_5 (@check_range_add (inlineCheck 15) 10 5 10 inlineBatch_15_0_part_10 (@check_range_add (inlineCheck 15) 15 5 5 inlineBatch_15_0_part_15 inlineBatch_15_0_part_20))))
theorem inlineGroupCheck_15_0 : inlineGroupCheck 15 0 25=true := by
  exact inlineBatch_15_0
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_15_25_part_25 : (List.range' 25 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_25_part_30 : (List.range' 30 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_25_part_35 : (List.range' 35 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_25_part_40 : (List.range' 40 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_25_part_45 : (List.range' 45 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_25 : (List.range' 25 25).all (inlineCheck 15) = true := by
  exact (@check_range_add (inlineCheck 15) 25 5 20 inlineBatch_15_25_part_25 (@check_range_add (inlineCheck 15) 30 5 15 inlineBatch_15_25_part_30 (@check_range_add (inlineCheck 15) 35 5 10 inlineBatch_15_25_part_35 (@check_range_add (inlineCheck 15) 40 5 5 inlineBatch_15_25_part_40 inlineBatch_15_25_part_45))))
theorem inlineGroupCheck_15_25 : inlineGroupCheck 15 25 25=true := by
  exact inlineBatch_15_25
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_15_50_part_50 : (List.range' 50 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_50_part_55 : (List.range' 55 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_50_part_60 : (List.range' 60 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_50_part_65 : (List.range' 65 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_50_part_70 : (List.range' 70 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_50 : (List.range' 50 25).all (inlineCheck 15) = true := by
  exact (@check_range_add (inlineCheck 15) 50 5 20 inlineBatch_15_50_part_50 (@check_range_add (inlineCheck 15) 55 5 15 inlineBatch_15_50_part_55 (@check_range_add (inlineCheck 15) 60 5 10 inlineBatch_15_50_part_60 (@check_range_add (inlineCheck 15) 65 5 5 inlineBatch_15_50_part_65 inlineBatch_15_50_part_70))))
theorem inlineGroupCheck_15_50 : inlineGroupCheck 15 50 25=true := by
  exact inlineBatch_15_50
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_15_75_part_75 : (List.range' 75 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_75_part_80 : (List.range' 80 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_75_part_85 : (List.range' 85 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_75_part_90 : (List.range' 90 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_75_part_95 : (List.range' 95 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_75 : (List.range' 75 25).all (inlineCheck 15) = true := by
  exact (@check_range_add (inlineCheck 15) 75 5 20 inlineBatch_15_75_part_75 (@check_range_add (inlineCheck 15) 80 5 15 inlineBatch_15_75_part_80 (@check_range_add (inlineCheck 15) 85 5 10 inlineBatch_15_75_part_85 (@check_range_add (inlineCheck 15) 90 5 5 inlineBatch_15_75_part_90 inlineBatch_15_75_part_95))))
theorem inlineGroupCheck_15_75 : inlineGroupCheck 15 75 25=true := by
  exact inlineBatch_15_75
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_15_100_part_100 : (List.range' 100 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_100_part_105 : (List.range' 105 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_100_part_110 : (List.range' 110 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_100_part_115 : (List.range' 115 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_100_part_120 : (List.range' 120 5).all (inlineCheck 15) = true := by decide +kernel
private theorem inlineBatch_15_100 : (List.range' 100 25).all (inlineCheck 15) = true := by
  exact (@check_range_add (inlineCheck 15) 100 5 20 inlineBatch_15_100_part_100 (@check_range_add (inlineCheck 15) 105 5 15 inlineBatch_15_100_part_105 (@check_range_add (inlineCheck 15) 110 5 10 inlineBatch_15_100_part_110 (@check_range_add (inlineCheck 15) 115 5 5 inlineBatch_15_100_part_115 inlineBatch_15_100_part_120))))
theorem inlineGroupCheck_15_100 : inlineGroupCheck 15 100 25=true := by
  exact inlineBatch_15_100
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_16_0_part_0 : (List.range' 0 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_5 : (List.range' 5 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_10 : (List.range' 10 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_15 : (List.range' 15 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_20 : (List.range' 20 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0 : (List.range' 0 25).all (inlineCheck 16) = true := by
  exact (@check_range_add (inlineCheck 16) 0 5 20 inlineBatch_16_0_part_0 (@check_range_add (inlineCheck 16) 5 5 15 inlineBatch_16_0_part_5 (@check_range_add (inlineCheck 16) 10 5 10 inlineBatch_16_0_part_10 (@check_range_add (inlineCheck 16) 15 5 5 inlineBatch_16_0_part_15 inlineBatch_16_0_part_20))))
theorem inlineGroupCheck_16_0 : inlineGroupCheck 16 0 25=true := by
  exact inlineBatch_16_0
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_16_25_part_25 : (List.range' 25 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_25_part_30 : (List.range' 30 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_25_part_35 : (List.range' 35 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_25_part_40 : (List.range' 40 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_25_part_45 : (List.range' 45 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_25 : (List.range' 25 25).all (inlineCheck 16) = true := by
  exact (@check_range_add (inlineCheck 16) 25 5 20 inlineBatch_16_25_part_25 (@check_range_add (inlineCheck 16) 30 5 15 inlineBatch_16_25_part_30 (@check_range_add (inlineCheck 16) 35 5 10 inlineBatch_16_25_part_35 (@check_range_add (inlineCheck 16) 40 5 5 inlineBatch_16_25_part_40 inlineBatch_16_25_part_45))))
theorem inlineGroupCheck_16_25 : inlineGroupCheck 16 25 25=true := by
  exact inlineBatch_16_25
end SigGolfCandidate.T3M.Nonbinary
end
end
