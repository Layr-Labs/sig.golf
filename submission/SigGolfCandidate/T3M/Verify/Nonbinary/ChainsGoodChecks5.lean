import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecks4

section
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
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_16_50_part_50 : (List.range' 50 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_50_part_55 : (List.range' 55 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_50_part_60 : (List.range' 60 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_50_part_65 : (List.range' 65 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_50_part_70 : (List.range' 70 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_50 : (List.range' 50 25).all (inlineCheck 16) = true := by
  exact (@check_range_add (inlineCheck 16) 50 5 20 inlineBatch_16_50_part_50 (@check_range_add (inlineCheck 16) 55 5 15 inlineBatch_16_50_part_55 (@check_range_add (inlineCheck 16) 60 5 10 inlineBatch_16_50_part_60 (@check_range_add (inlineCheck 16) 65 5 5 inlineBatch_16_50_part_65 inlineBatch_16_50_part_70))))
theorem inlineGroupCheck_16_50 : inlineGroupCheck 16 50 25=true := by
  exact inlineBatch_16_50
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_16_75_part_75 : (List.range' 75 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_75_part_80 : (List.range' 80 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_75_part_85 : (List.range' 85 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_75_part_90 : (List.range' 90 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_75_part_95 : (List.range' 95 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_75 : (List.range' 75 25).all (inlineCheck 16) = true := by
  exact (@check_range_add (inlineCheck 16) 75 5 20 inlineBatch_16_75_part_75 (@check_range_add (inlineCheck 16) 80 5 15 inlineBatch_16_75_part_80 (@check_range_add (inlineCheck 16) 85 5 10 inlineBatch_16_75_part_85 (@check_range_add (inlineCheck 16) 90 5 5 inlineBatch_16_75_part_90 inlineBatch_16_75_part_95))))
theorem inlineGroupCheck_16_75 : inlineGroupCheck 16 75 25=true := by
  exact inlineBatch_16_75
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_16_100_part_100 : (List.range' 100 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_100_part_105 : (List.range' 105 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_100_part_110 : (List.range' 110 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_100_part_115 : (List.range' 115 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_100_part_120 : (List.range' 120 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_100 : (List.range' 100 25).all (inlineCheck 16) = true := by
  exact (@check_range_add (inlineCheck 16) 100 5 20 inlineBatch_16_100_part_100 (@check_range_add (inlineCheck 16) 105 5 15 inlineBatch_16_100_part_105 (@check_range_add (inlineCheck 16) 110 5 10 inlineBatch_16_100_part_110 (@check_range_add (inlineCheck 16) 115 5 5 inlineBatch_16_100_part_115 inlineBatch_16_100_part_120))))
theorem inlineGroupCheck_16_100 : inlineGroupCheck 16 100 25=true := by
  exact inlineBatch_16_100
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem rejectBatch_part_0 : (List.range' 0 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_8 : (List.range' 8 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_16 : (List.range' 16 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_24 : (List.range' 24 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_32 : (List.range' 32 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_40 : (List.range' 40 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_48 : (List.range' 48 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_56 : (List.range' 56 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_64 : (List.range' 64 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_72 : (List.range' 72 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_80 : (List.range' 80 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_88 : (List.range' 88 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_96 : (List.range' 96 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_104 : (List.range' 104 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_112 : (List.range' 112 8).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch_part_120 : (List.range' 120 5).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by decide +kernel
private theorem rejectBatch : (List.range' 0 125).all (fun k => rOK (vrun (guardW k) 1) rejJ) = true := by
  exact (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 0 8 117 rejectBatch_part_0 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 8 8 109 rejectBatch_part_8 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 16 8 101 rejectBatch_part_16 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 24 8 93 rejectBatch_part_24 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 32 8 85 rejectBatch_part_32 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 40 8 77 rejectBatch_part_40 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 48 8 69 rejectBatch_part_48 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 56 8 61 rejectBatch_part_56 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 64 8 53 rejectBatch_part_64 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 72 8 45 rejectBatch_part_72 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 80 8 37 rejectBatch_part_80 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 88 8 29 rejectBatch_part_88 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 96 8 21 rejectBatch_part_96 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 104 8 13 rejectBatch_part_104 (@check_range_add (fun k => rOK (vrun (guardW k) 1) rejJ) 112 8 5 rejectBatch_part_112 rejectBatch_part_120)))))))))))))))
theorem rejCheck_ok : rejCheck=true := by
  unfold rejCheck
  rw [List.range_eq_range']
  exact rejectBatch
end SigGolfCandidate.T3M.Nonbinary
end
end
