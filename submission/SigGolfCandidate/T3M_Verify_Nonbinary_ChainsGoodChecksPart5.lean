import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsCheckParts

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-! T51 guards: invalid r6 fields, invalid r7 ranks, checksum landings outside the arms; the 6 checksum arms. -/
theorem guard6All_0 : guard6All 0 = true := by decide +kernel
theorem guard6All_1 : guard6All 1 = true := by decide +kernel
theorem guard6All_2 : guard6All 2 = true := by decide +kernel
theorem guard6All_3 : guard6All 3 = true := by decide +kernel
theorem guard6All_4 : guard6All 4 = true := by decide +kernel
theorem guard6All_5 : guard6All 5 = true := by decide +kernel
theorem guard6All_6 : guard6All 6 = true := by decide +kernel
theorem guard6All_7 : guard6All 7 = true := by decide +kernel
theorem guard6All_8 : guard6All 8 = true := by decide +kernel
theorem r7GuardAll_ok : r7GuardAll = true := by decide +kernel
theorem ckGuardAll_ok : ckGuardAll = true := by decide +kernel
theorem ckArmAll_ok : ckArmAll = true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_9_0_part_0 : (List.range' 0 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_0_part_5 : (List.range' 5 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_0_part_10 : (List.range' 10 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_0_part_15 : (List.range' 15 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_0_part_20 : (List.range' 20 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_0 : (List.range' 0 25).all (inlineCheck 9) = true := by
  exact (@check_range_add (inlineCheck 9) 0 5 20 inlineBatch_9_0_part_0 (@check_range_add (inlineCheck 9) 5 5 15 inlineBatch_9_0_part_5 (@check_range_add (inlineCheck 9) 10 5 10 inlineBatch_9_0_part_10 (@check_range_add (inlineCheck 9) 15 5 5 inlineBatch_9_0_part_15 inlineBatch_9_0_part_20))))
theorem inlineGroupCheck_9_0 : inlineGroupCheck 9 0 25=true := by
  exact inlineBatch_9_0
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_9_25_part_25 : (List.range' 25 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_25_part_30 : (List.range' 30 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_25_part_35 : (List.range' 35 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_25_part_40 : (List.range' 40 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_25_part_45 : (List.range' 45 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_25 : (List.range' 25 25).all (inlineCheck 9) = true := by
  exact (@check_range_add (inlineCheck 9) 25 5 20 inlineBatch_9_25_part_25 (@check_range_add (inlineCheck 9) 30 5 15 inlineBatch_9_25_part_30 (@check_range_add (inlineCheck 9) 35 5 10 inlineBatch_9_25_part_35 (@check_range_add (inlineCheck 9) 40 5 5 inlineBatch_9_25_part_40 inlineBatch_9_25_part_45))))
theorem inlineGroupCheck_9_25 : inlineGroupCheck 9 25 25=true := by
  exact inlineBatch_9_25
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_9_50_part_50 : (List.range' 50 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_50_part_55 : (List.range' 55 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_50_part_60 : (List.range' 60 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_50_part_65 : (List.range' 65 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_50_part_70 : (List.range' 70 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_50 : (List.range' 50 25).all (inlineCheck 9) = true := by
  exact (@check_range_add (inlineCheck 9) 50 5 20 inlineBatch_9_50_part_50 (@check_range_add (inlineCheck 9) 55 5 15 inlineBatch_9_50_part_55 (@check_range_add (inlineCheck 9) 60 5 10 inlineBatch_9_50_part_60 (@check_range_add (inlineCheck 9) 65 5 5 inlineBatch_9_50_part_65 inlineBatch_9_50_part_70))))
theorem inlineGroupCheck_9_50 : inlineGroupCheck 9 50 25=true := by
  exact inlineBatch_9_50
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_9_75_part_75 : (List.range' 75 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_75_part_80 : (List.range' 80 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_75_part_85 : (List.range' 85 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_75_part_90 : (List.range' 90 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_75_part_95 : (List.range' 95 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_75 : (List.range' 75 25).all (inlineCheck 9) = true := by
  exact (@check_range_add (inlineCheck 9) 75 5 20 inlineBatch_9_75_part_75 (@check_range_add (inlineCheck 9) 80 5 15 inlineBatch_9_75_part_80 (@check_range_add (inlineCheck 9) 85 5 10 inlineBatch_9_75_part_85 (@check_range_add (inlineCheck 9) 90 5 5 inlineBatch_9_75_part_90 inlineBatch_9_75_part_95))))
theorem inlineGroupCheck_9_75 : inlineGroupCheck 9 75 25=true := by
  exact inlineBatch_9_75
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_9_100_part_100 : (List.range' 100 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_100_part_105 : (List.range' 105 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_100_part_110 : (List.range' 110 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_100_part_115 : (List.range' 115 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_100_part_120 : (List.range' 120 5).all (inlineCheck 9) = true := by decide +kernel
private theorem inlineBatch_9_100 : (List.range' 100 25).all (inlineCheck 9) = true := by
  exact (@check_range_add (inlineCheck 9) 100 5 20 inlineBatch_9_100_part_100 (@check_range_add (inlineCheck 9) 105 5 15 inlineBatch_9_100_part_105 (@check_range_add (inlineCheck 9) 110 5 10 inlineBatch_9_100_part_110 (@check_range_add (inlineCheck 9) 115 5 5 inlineBatch_9_100_part_115 inlineBatch_9_100_part_120))))
theorem inlineGroupCheck_9_100 : inlineGroupCheck 9 100 25=true := by
  exact inlineBatch_9_100
end SigGolfCandidate.T3M.Nonbinary
end
end
