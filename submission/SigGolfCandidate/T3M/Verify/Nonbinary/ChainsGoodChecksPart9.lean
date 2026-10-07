import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart8

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_17_part_0 : (List.range' 0 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17_part_8 : (List.range' 8 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17_part_16 : (List.range' 16 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17_part_24 : (List.range' 24 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17_part_32 : (List.range' 32 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17_part_40 : (List.range' 40 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17_part_48 : (List.range' 48 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17_part_56 : (List.range' 56 8).all (fun k => entCheck 17 k && s8Check 17 k) = true := by decide +kernel
private theorem tripleEnt_17 : (List.range' 0 64).all (fun k => entCheck 17 k && s8Check 17 k) = true := by
  exact (@check_range_add (fun k => entCheck 17 k && s8Check 17 k) 0 8 56 tripleEnt_17_part_0 (@check_range_add (fun k => entCheck 17 k && s8Check 17 k) 8 8 48 tripleEnt_17_part_8 (@check_range_add (fun k => entCheck 17 k && s8Check 17 k) 16 8 40 tripleEnt_17_part_16 (@check_range_add (fun k => entCheck 17 k && s8Check 17 k) 24 8 32 tripleEnt_17_part_24 (@check_range_add (fun k => entCheck 17 k && s8Check 17 k) 32 8 24 tripleEnt_17_part_32 (@check_range_add (fun k => entCheck 17 k && s8Check 17 k) 40 8 16 tripleEnt_17_part_40 (@check_range_add (fun k => entCheck 17 k && s8Check 17 k) 48 8 8 tripleEnt_17_part_48 tripleEnt_17_part_56)))))))
private theorem tripleBlock_17_part_0 : (List.range' 0 4).all (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) = true := by decide +kernel
private theorem tripleBlock_17_part_4 : (List.range' 4 4).all (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) = true := by decide +kernel
private theorem tripleBlock_17_part_8 : (List.range' 8 4).all (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) = true := by decide +kernel
private theorem tripleBlock_17_part_12 : (List.range' 12 4).all (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) = true := by decide +kernel
private theorem tripleBlock_17 : (List.range' 0 16).all (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) 0 4 12 tripleBlock_17_part_0 (@check_range_add (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) 4 4 8 tripleBlock_17_part_4 (@check_range_add (fun x => blockCheck 17 (x / (mx 17 + 1)) (x % (mx 17 + 1))) 8 4 4 tripleBlock_17_part_8 tripleBlock_17_part_12)))
theorem tripleCheck_17 : tripleCheck 17=true := by
  exact @tripleCheck_join 17 tripleEnt_17 tripleBlock_17
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_14_0_part_0 : (List.range' 0 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_0_part_5 : (List.range' 5 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_0_part_10 : (List.range' 10 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_0_part_15 : (List.range' 15 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_0_part_20 : (List.range' 20 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_0 : (List.range' 0 25).all (inlineCheck 14) = true := by
  exact (@check_range_add (inlineCheck 14) 0 5 20 inlineBatch_14_0_part_0 (@check_range_add (inlineCheck 14) 5 5 15 inlineBatch_14_0_part_5 (@check_range_add (inlineCheck 14) 10 5 10 inlineBatch_14_0_part_10 (@check_range_add (inlineCheck 14) 15 5 5 inlineBatch_14_0_part_15 inlineBatch_14_0_part_20))))
theorem inlineGroupCheck_14_0 : inlineGroupCheck 14 0 25=true := by
  exact inlineBatch_14_0
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_14_25_part_25 : (List.range' 25 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_25_part_30 : (List.range' 30 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_25_part_35 : (List.range' 35 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_25_part_40 : (List.range' 40 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_25_part_45 : (List.range' 45 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_25 : (List.range' 25 25).all (inlineCheck 14) = true := by
  exact (@check_range_add (inlineCheck 14) 25 5 20 inlineBatch_14_25_part_25 (@check_range_add (inlineCheck 14) 30 5 15 inlineBatch_14_25_part_30 (@check_range_add (inlineCheck 14) 35 5 10 inlineBatch_14_25_part_35 (@check_range_add (inlineCheck 14) 40 5 5 inlineBatch_14_25_part_40 inlineBatch_14_25_part_45))))
theorem inlineGroupCheck_14_25 : inlineGroupCheck 14 25 25=true := by
  exact inlineBatch_14_25
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_14_50_part_50 : (List.range' 50 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_50_part_55 : (List.range' 55 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_50_part_60 : (List.range' 60 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_50_part_65 : (List.range' 65 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_50_part_70 : (List.range' 70 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_50 : (List.range' 50 25).all (inlineCheck 14) = true := by
  exact (@check_range_add (inlineCheck 14) 50 5 20 inlineBatch_14_50_part_50 (@check_range_add (inlineCheck 14) 55 5 15 inlineBatch_14_50_part_55 (@check_range_add (inlineCheck 14) 60 5 10 inlineBatch_14_50_part_60 (@check_range_add (inlineCheck 14) 65 5 5 inlineBatch_14_50_part_65 inlineBatch_14_50_part_70))))
theorem inlineGroupCheck_14_50 : inlineGroupCheck 14 50 25=true := by
  exact inlineBatch_14_50
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_14_75_part_75 : (List.range' 75 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_75_part_80 : (List.range' 80 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_75_part_85 : (List.range' 85 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_75_part_90 : (List.range' 90 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_75_part_95 : (List.range' 95 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_75 : (List.range' 75 25).all (inlineCheck 14) = true := by
  exact (@check_range_add (inlineCheck 14) 75 5 20 inlineBatch_14_75_part_75 (@check_range_add (inlineCheck 14) 80 5 15 inlineBatch_14_75_part_80 (@check_range_add (inlineCheck 14) 85 5 10 inlineBatch_14_75_part_85 (@check_range_add (inlineCheck 14) 90 5 5 inlineBatch_14_75_part_90 inlineBatch_14_75_part_95))))
theorem inlineGroupCheck_14_75 : inlineGroupCheck 14 75 25=true := by
  exact inlineBatch_14_75
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_14_100_part_100 : (List.range' 100 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_100_part_105 : (List.range' 105 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_100_part_110 : (List.range' 110 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_100_part_115 : (List.range' 115 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_100_part_120 : (List.range' 120 5).all (inlineCheck 14) = true := by decide +kernel
private theorem inlineBatch_14_100 : (List.range' 100 25).all (inlineCheck 14) = true := by
  exact (@check_range_add (inlineCheck 14) 100 5 20 inlineBatch_14_100_part_100 (@check_range_add (inlineCheck 14) 105 5 15 inlineBatch_14_100_part_105 (@check_range_add (inlineCheck 14) 110 5 10 inlineBatch_14_100_part_110 (@check_range_add (inlineCheck 14) 115 5 5 inlineBatch_14_100_part_115 inlineBatch_14_100_part_120))))
theorem inlineGroupCheck_14_100 : inlineGroupCheck 14 100 25=true := by
  exact inlineBatch_14_100
end SigGolfCandidate.T3M.Nonbinary
end
end
