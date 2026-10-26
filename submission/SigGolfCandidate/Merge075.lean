import SigGolfCandidate.Merge074

-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart4 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_8_part_0 : (List.range' 0 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_8 : (List.range' 8 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_16 : (List.range' 16 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_24 : (List.range' 24 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_32 : (List.range' 32 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_40 : (List.range' 40 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_48 : (List.range' 48 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_56 : (List.range' 56 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_64 : (List.range' 64 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_72 : (List.range' 72 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_80 : (List.range' 80 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_88 : (List.range' 88 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_96 : (List.range' 96 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_104 : (List.range' 104 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_112 : (List.range' 112 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_120 : (List.range' 120 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_128 : (List.range' 128 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_136 : (List.range' 136 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_144 : (List.range' 144 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_152 : (List.range' 152 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_160 : (List.range' 160 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_168 : (List.range' 168 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_176 : (List.range' 176 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_184 : (List.range' 184 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_192 : (List.range' 192 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_200 : (List.range' 200 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8_part_208 : (List.range' 208 8).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8 : (List.range' 0 216).all (fun k => entCheck 8 k && s8Check 8 k) = true := by
  exact (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 0 8 208 tripleEnt_8_part_0 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 8 8 200 tripleEnt_8_part_8 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 16 8 192 tripleEnt_8_part_16 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 24 8 184 tripleEnt_8_part_24 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 32 8 176 tripleEnt_8_part_32 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 40 8 168 tripleEnt_8_part_40 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 48 8 160 tripleEnt_8_part_48 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 56 8 152 tripleEnt_8_part_56 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 64 8 144 tripleEnt_8_part_64 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 72 8 136 tripleEnt_8_part_72 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 80 8 128 tripleEnt_8_part_80 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 88 8 120 tripleEnt_8_part_88 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 96 8 112 tripleEnt_8_part_96 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 104 8 104 tripleEnt_8_part_104 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 112 8 96 tripleEnt_8_part_112 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 120 8 88 tripleEnt_8_part_120 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 128 8 80 tripleEnt_8_part_128 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 136 8 72 tripleEnt_8_part_136 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 144 8 64 tripleEnt_8_part_144 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 152 8 56 tripleEnt_8_part_152 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 160 8 48 tripleEnt_8_part_160 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 168 8 40 tripleEnt_8_part_168 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 176 8 32 tripleEnt_8_part_176 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 184 8 24 tripleEnt_8_part_184 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 192 8 16 tripleEnt_8_part_192 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 200 8 8 tripleEnt_8_part_200 tripleEnt_8_part_208))))))))))))))))))))))))))
private theorem tripleBlock_8_part_0 : (List.range' 0 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_4 : (List.range' 4 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_8 : (List.range' 8 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_12 : (List.range' 12 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_16 : (List.range' 16 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_20 : (List.range' 20 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_24 : (List.range' 24 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_28 : (List.range' 28 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8_part_32 : (List.range' 32 4).all (liveBlock 8) = true := by decide +kernel
private theorem tripleBlock_8 : (List.range' 0 36).all (liveBlock 8) = true := by
  exact (@check_range_add (liveBlock 8) 0 4 32 tripleBlock_8_part_0 (@check_range_add (liveBlock 8) 4 4 28 tripleBlock_8_part_4 (@check_range_add (liveBlock 8) 8 4 24 tripleBlock_8_part_8 (@check_range_add (liveBlock 8) 12 4 20 tripleBlock_8_part_12 (@check_range_add (liveBlock 8) 16 4 16 tripleBlock_8_part_16 (@check_range_add (liveBlock 8) 20 4 12 tripleBlock_8_part_20 (@check_range_add (liveBlock 8) 24 4 8 tripleBlock_8_part_24 (@check_range_add (liveBlock 8) 28 4 4 tripleBlock_8_part_28 tripleBlock_8_part_32))))))))
theorem tripleCheck_8 : tripleCheck 8=true := by
  exact @tripleCheck_join 8 tripleEnt_8 tripleBlock_8
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_16_part_0 : (List.range' 0 8).all (fun k => entCheck 16 k && s8Check 16 k) = true := by decide +kernel
private theorem tripleEnt_16_part_8 : (List.range' 8 8).all (fun k => entCheck 16 k && s8Check 16 k) = true := by decide +kernel
private theorem tripleEnt_16_part_16 : (List.range' 16 8).all (fun k => entCheck 16 k && s8Check 16 k) = true := by decide +kernel
private theorem tripleEnt_16_part_24 : (List.range' 24 8).all (fun k => entCheck 16 k && s8Check 16 k) = true := by decide +kernel
private theorem tripleEnt_16_part_32 : (List.range' 32 8).all (fun k => entCheck 16 k && s8Check 16 k) = true := by decide +kernel
private theorem tripleEnt_16_part_40 : (List.range' 40 8).all (fun k => entCheck 16 k && s8Check 16 k) = true := by decide +kernel
private theorem tripleEnt_16_part_48 : (List.range' 48 1).all (fun k => entCheck 16 k && s8Check 16 k) = true := by decide +kernel
private theorem tripleEnt_16 : (List.range' 0 49).all (fun k => entCheck 16 k && s8Check 16 k) = true := by
  exact (@check_range_add (fun k => entCheck 16 k && s8Check 16 k) 0 8 41 tripleEnt_16_part_0 (@check_range_add (fun k => entCheck 16 k && s8Check 16 k) 8 8 33 tripleEnt_16_part_8 (@check_range_add (fun k => entCheck 16 k && s8Check 16 k) 16 8 25 tripleEnt_16_part_16 (@check_range_add (fun k => entCheck 16 k && s8Check 16 k) 24 8 17 tripleEnt_16_part_24 (@check_range_add (fun k => entCheck 16 k && s8Check 16 k) 32 8 9 tripleEnt_16_part_32 (@check_range_add (fun k => entCheck 16 k && s8Check 16 k) 40 8 1 tripleEnt_16_part_40 tripleEnt_16_part_48))))))
private theorem tripleBlock_16_part_0 : (List.range' 0 4).all (liveBlock 16) = true := by decide +kernel
private theorem tripleBlock_16_part_4 : (List.range' 4 3).all (liveBlock 16) = true := by decide +kernel
private theorem tripleBlock_16 : (List.range' 0 7).all (liveBlock 16) = true := by
  exact (@check_range_add (liveBlock 16) 0 4 3 tripleBlock_16_part_0 tripleBlock_16_part_4)
theorem tripleCheck_16 : tripleCheck 16=true := by
  exact @tripleCheck_join 16 tripleEnt_16 tripleBlock_16
end SigGolfCandidate.T3M.Nonbinary
end
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart5 ====
section

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
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart6 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_10_part_0 : (List.range' 0 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_8 : (List.range' 8 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_16 : (List.range' 16 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_24 : (List.range' 24 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_32 : (List.range' 32 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_40 : (List.range' 40 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_48 : (List.range' 48 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_56 : (List.range' 56 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_64 : (List.range' 64 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_72 : (List.range' 72 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_80 : (List.range' 80 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_88 : (List.range' 88 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_96 : (List.range' 96 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_104 : (List.range' 104 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_112 : (List.range' 112 8).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10_part_120 : (List.range' 120 5).all (fun k => entCheck 10 k && s8Check 10 k) = true := by decide +kernel
private theorem tripleEnt_10 : (List.range' 0 125).all (fun k => entCheck 10 k && s8Check 10 k) = true := by
  exact (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 0 8 117 tripleEnt_10_part_0 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 8 8 109 tripleEnt_10_part_8 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 16 8 101 tripleEnt_10_part_16 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 24 8 93 tripleEnt_10_part_24 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 32 8 85 tripleEnt_10_part_32 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 40 8 77 tripleEnt_10_part_40 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 48 8 69 tripleEnt_10_part_48 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 56 8 61 tripleEnt_10_part_56 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 64 8 53 tripleEnt_10_part_64 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 72 8 45 tripleEnt_10_part_72 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 80 8 37 tripleEnt_10_part_80 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 88 8 29 tripleEnt_10_part_88 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 96 8 21 tripleEnt_10_part_96 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 104 8 13 tripleEnt_10_part_104 (@check_range_add (fun k => entCheck 10 k && s8Check 10 k) 112 8 5 tripleEnt_10_part_112 tripleEnt_10_part_120)))))))))))))))
private theorem tripleBlock_10_part_0 : (List.range' 0 4).all (liveBlock 10) = true := by decide +kernel
private theorem tripleBlock_10_part_4 : (List.range' 4 4).all (liveBlock 10) = true := by decide +kernel
private theorem tripleBlock_10_part_8 : (List.range' 8 4).all (liveBlock 10) = true := by decide +kernel
private theorem tripleBlock_10_part_12 : (List.range' 12 4).all (liveBlock 10) = true := by decide +kernel
private theorem tripleBlock_10_part_16 : (List.range' 16 4).all (liveBlock 10) = true := by decide +kernel
private theorem tripleBlock_10_part_20 : (List.range' 20 4).all (liveBlock 10) = true := by decide +kernel
private theorem tripleBlock_10_part_24 : (List.range' 24 1).all (liveBlock 10) = true := by decide +kernel
private theorem tripleBlock_10 : (List.range' 0 25).all (liveBlock 10) = true := by
  exact (@check_range_add (liveBlock 10) 0 4 21 tripleBlock_10_part_0 (@check_range_add (liveBlock 10) 4 4 17 tripleBlock_10_part_4 (@check_range_add (liveBlock 10) 8 4 13 tripleBlock_10_part_8 (@check_range_add (liveBlock 10) 12 4 9 tripleBlock_10_part_12 (@check_range_add (liveBlock 10) 16 4 5 tripleBlock_10_part_16 (@check_range_add (liveBlock 10) 20 4 1 tripleBlock_10_part_20 tripleBlock_10_part_24))))))
theorem tripleCheck_10 : tripleCheck 10=true := by
  exact @tripleCheck_join 10 tripleEnt_10 tripleBlock_10
end SigGolfCandidate.T3M.Nonbinary
end
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart7 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_11_part_0 : (List.range' 0 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_8 : (List.range' 8 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_16 : (List.range' 16 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_24 : (List.range' 24 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_32 : (List.range' 32 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_40 : (List.range' 40 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_48 : (List.range' 48 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_56 : (List.range' 56 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_64 : (List.range' 64 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_72 : (List.range' 72 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_80 : (List.range' 80 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_88 : (List.range' 88 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_96 : (List.range' 96 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_104 : (List.range' 104 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_112 : (List.range' 112 8).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11_part_120 : (List.range' 120 5).all (fun k => entCheck 11 k && s8Check 11 k) = true := by decide +kernel
private theorem tripleEnt_11 : (List.range' 0 125).all (fun k => entCheck 11 k && s8Check 11 k) = true := by
  exact (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 0 8 117 tripleEnt_11_part_0 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 8 8 109 tripleEnt_11_part_8 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 16 8 101 tripleEnt_11_part_16 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 24 8 93 tripleEnt_11_part_24 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 32 8 85 tripleEnt_11_part_32 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 40 8 77 tripleEnt_11_part_40 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 48 8 69 tripleEnt_11_part_48 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 56 8 61 tripleEnt_11_part_56 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 64 8 53 tripleEnt_11_part_64 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 72 8 45 tripleEnt_11_part_72 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 80 8 37 tripleEnt_11_part_80 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 88 8 29 tripleEnt_11_part_88 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 96 8 21 tripleEnt_11_part_96 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 104 8 13 tripleEnt_11_part_104 (@check_range_add (fun k => entCheck 11 k && s8Check 11 k) 112 8 5 tripleEnt_11_part_112 tripleEnt_11_part_120)))))))))))))))
private theorem tripleBlock_11_part_0 : (List.range' 0 4).all (liveBlock 11) = true := by decide +kernel
private theorem tripleBlock_11_part_4 : (List.range' 4 4).all (liveBlock 11) = true := by decide +kernel
private theorem tripleBlock_11_part_8 : (List.range' 8 4).all (liveBlock 11) = true := by decide +kernel
private theorem tripleBlock_11_part_12 : (List.range' 12 4).all (liveBlock 11) = true := by decide +kernel
private theorem tripleBlock_11_part_16 : (List.range' 16 4).all (liveBlock 11) = true := by decide +kernel
private theorem tripleBlock_11_part_20 : (List.range' 20 4).all (liveBlock 11) = true := by decide +kernel
private theorem tripleBlock_11_part_24 : (List.range' 24 1).all (liveBlock 11) = true := by decide +kernel
private theorem tripleBlock_11 : (List.range' 0 25).all (liveBlock 11) = true := by
  exact (@check_range_add (liveBlock 11) 0 4 21 tripleBlock_11_part_0 (@check_range_add (liveBlock 11) 4 4 17 tripleBlock_11_part_4 (@check_range_add (liveBlock 11) 8 4 13 tripleBlock_11_part_8 (@check_range_add (liveBlock 11) 12 4 9 tripleBlock_11_part_12 (@check_range_add (liveBlock 11) 16 4 5 tripleBlock_11_part_16 (@check_range_add (liveBlock 11) 20 4 1 tripleBlock_11_part_20 tripleBlock_11_part_24))))))
theorem tripleCheck_11 : tripleCheck 11=true := by
  exact @tripleCheck_join 11 tripleEnt_11 tripleBlock_11
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_12_part_0 : (List.range' 0 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_8 : (List.range' 8 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_16 : (List.range' 16 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_24 : (List.range' 24 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_32 : (List.range' 32 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_40 : (List.range' 40 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_48 : (List.range' 48 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_56 : (List.range' 56 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_64 : (List.range' 64 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_72 : (List.range' 72 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_80 : (List.range' 80 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_88 : (List.range' 88 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_96 : (List.range' 96 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_104 : (List.range' 104 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_112 : (List.range' 112 8).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12_part_120 : (List.range' 120 5).all (fun k => entCheck 12 k && s8Check 12 k) = true := by decide +kernel
private theorem tripleEnt_12 : (List.range' 0 125).all (fun k => entCheck 12 k && s8Check 12 k) = true := by
  exact (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 0 8 117 tripleEnt_12_part_0 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 8 8 109 tripleEnt_12_part_8 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 16 8 101 tripleEnt_12_part_16 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 24 8 93 tripleEnt_12_part_24 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 32 8 85 tripleEnt_12_part_32 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 40 8 77 tripleEnt_12_part_40 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 48 8 69 tripleEnt_12_part_48 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 56 8 61 tripleEnt_12_part_56 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 64 8 53 tripleEnt_12_part_64 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 72 8 45 tripleEnt_12_part_72 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 80 8 37 tripleEnt_12_part_80 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 88 8 29 tripleEnt_12_part_88 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 96 8 21 tripleEnt_12_part_96 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 104 8 13 tripleEnt_12_part_104 (@check_range_add (fun k => entCheck 12 k && s8Check 12 k) 112 8 5 tripleEnt_12_part_112 tripleEnt_12_part_120)))))))))))))))
private theorem tripleBlock_12_part_0 : (List.range' 0 4).all (liveBlock 12) = true := by decide +kernel
private theorem tripleBlock_12_part_4 : (List.range' 4 4).all (liveBlock 12) = true := by decide +kernel
private theorem tripleBlock_12_part_8 : (List.range' 8 4).all (liveBlock 12) = true := by decide +kernel
private theorem tripleBlock_12_part_12 : (List.range' 12 4).all (liveBlock 12) = true := by decide +kernel
private theorem tripleBlock_12_part_16 : (List.range' 16 4).all (liveBlock 12) = true := by decide +kernel
private theorem tripleBlock_12_part_20 : (List.range' 20 4).all (liveBlock 12) = true := by decide +kernel
private theorem tripleBlock_12_part_24 : (List.range' 24 1).all (liveBlock 12) = true := by decide +kernel
private theorem tripleBlock_12 : (List.range' 0 25).all (liveBlock 12) = true := by
  exact (@check_range_add (liveBlock 12) 0 4 21 tripleBlock_12_part_0 (@check_range_add (liveBlock 12) 4 4 17 tripleBlock_12_part_4 (@check_range_add (liveBlock 12) 8 4 13 tripleBlock_12_part_8 (@check_range_add (liveBlock 12) 12 4 9 tripleBlock_12_part_12 (@check_range_add (liveBlock 12) 16 4 5 tripleBlock_12_part_16 (@check_range_add (liveBlock 12) 20 4 1 tripleBlock_12_part_20 tripleBlock_12_part_24))))))
theorem tripleCheck_12 : tripleCheck 12=true := by
  exact @tripleCheck_join 12 tripleEnt_12 tripleBlock_12
end SigGolfCandidate.T3M.Nonbinary
end
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart8 ====
section

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
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_13_25_part_25 : (List.range' 25 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_30 : (List.range' 30 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_35 : (List.range' 35 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_40 : (List.range' 40 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_45 : (List.range' 45 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25 : (List.range' 25 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 25 5 20 inlineBatch_13_25_part_25 (@check_range_add (inlineCheck 13) 30 5 15 inlineBatch_13_25_part_30 (@check_range_add (inlineCheck 13) 35 5 10 inlineBatch_13_25_part_35 (@check_range_add (inlineCheck 13) 40 5 5 inlineBatch_13_25_part_40 inlineBatch_13_25_part_45))))
theorem inlineGroupCheck_13_25 : inlineGroupCheck 13 25 25=true := by
  exact inlineBatch_13_25
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_13_50_part_50 : (List.range' 50 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_55 : (List.range' 55 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_60 : (List.range' 60 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_65 : (List.range' 65 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_70 : (List.range' 70 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50 : (List.range' 50 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 50 5 20 inlineBatch_13_50_part_50 (@check_range_add (inlineCheck 13) 55 5 15 inlineBatch_13_50_part_55 (@check_range_add (inlineCheck 13) 60 5 10 inlineBatch_13_50_part_60 (@check_range_add (inlineCheck 13) 65 5 5 inlineBatch_13_50_part_65 inlineBatch_13_50_part_70))))
theorem inlineGroupCheck_13_50 : inlineGroupCheck 13 50 25=true := by
  exact inlineBatch_13_50
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_13_75_part_75 : (List.range' 75 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_80 : (List.range' 80 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_85 : (List.range' 85 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_90 : (List.range' 90 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_95 : (List.range' 95 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75 : (List.range' 75 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 75 5 20 inlineBatch_13_75_part_75 (@check_range_add (inlineCheck 13) 80 5 15 inlineBatch_13_75_part_80 (@check_range_add (inlineCheck 13) 85 5 10 inlineBatch_13_75_part_85 (@check_range_add (inlineCheck 13) 90 5 5 inlineBatch_13_75_part_90 inlineBatch_13_75_part_95))))
theorem inlineGroupCheck_13_75 : inlineGroupCheck 13 75 25=true := by
  exact inlineBatch_13_75
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
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
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart9 ====
section

section

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
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart10 ====
section

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
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart11 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-- T51: the r5 groups' (9 <= q < 16) invalid ranks 125 / 126 land on zero words (127: below the code). -/
theorem fault_top_word (q : Nat) (hq : q<16) (h9 : 9≤q) : (lcode (entOff q)).head?=some 0 := by
  interval_cases q <;> decide +kernel
theorem fault_top126_word (q : Nat) (hq : q<16) (h9 : 9≤q) (he : 1024≤entOff q) :
    (lcode (entOff q-1024)).head?=some 0 := by
  interval_cases q <;> first | (norm_num [entOff] at he; done) | decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
theorem tripleCheck_at (q : Nat) (hq : q<17) (hn : inl q=false) : tripleCheck q=true := by
  interval_cases q
  all_goals first | (simp [inl] at hn) | skip
  exacts [tripleCheck_0, tripleCheck_1, tripleCheck_2, tripleCheck_3, tripleCheck_4, tripleCheck_5,
    tripleCheck_6, tripleCheck_7, tripleCheck_8, tripleCheck_10, tripleCheck_11, tripleCheck_12, tripleCheck_16]
theorem inlineGroupCheck_at (q : Nat) (hq : inl q=true) :
    inlineGroupCheck q 0 25=true ∧ inlineGroupCheck q 25 25=true ∧ inlineGroupCheck q 50 25=true ∧
      inlineGroupCheck q 75 25=true ∧ inlineGroupCheck q 100 25=true := by
  have h : q=9 ∨ q=13 ∨ q=14 ∨ q=15 := by simp [inl] at hq; omega
  rcases h with rfl|rfl|rfl|rfl
  · exact ⟨inlineGroupCheck_9_0,inlineGroupCheck_9_25,inlineGroupCheck_9_50,inlineGroupCheck_9_75,inlineGroupCheck_9_100⟩
  · exact ⟨inlineGroupCheck_13_0,inlineGroupCheck_13_25,inlineGroupCheck_13_50,inlineGroupCheck_13_75,inlineGroupCheck_13_100⟩
  · exact ⟨inlineGroupCheck_14_0,inlineGroupCheck_14_25,inlineGroupCheck_14_50,inlineGroupCheck_14_75,
      inlineGroupCheck_14_100⟩
  · exact ⟨inlineGroupCheck_15_0,inlineGroupCheck_15_25,inlineGroupCheck_15_50,inlineGroupCheck_15_75,
      inlineGroupCheck_15_100⟩
theorem inlineCheck_static_at (q k : Nat) (hq : inl q=true) (hk : k<125) : inlineCheck q k=true := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := inlineGroupCheck_at q hq
  have pick : ∀ lo, inlineGroupCheck q lo 25=true → lo ≤ k → k<lo+25 → inlineCheck q k=true := by
    intro lo h hl hh
    exact List.all_eq_true.mp h k (List.mem_range'_1.mpr ⟨hl,by omega⟩)
  by_cases a : k<25
  · exact pick 0 h0 (by omega) (by omega)
  by_cases b : k<50
  · exact pick 25 h1 (by omega) (by omega)
  by_cases d : k<75
  · exact pick 50 h2 (by omega) (by omega)
  by_cases e : k<100
  · exact pick 75 h3 (by omega) (by omega)
  · exact pick 100 h4 (by omega) (by omega)
theorem entCheck_at (q k : Nat) (hq : q<17) (hn : inl q=false) (hk : k<nRank q) : entCheck q k=true := by
  have h := tripleCheck_at q hq hn
  simp only [tripleCheck,Bool.and_eq_true] at h
  exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).1
theorem static_false_of_row_false (q k : Nat) (h : rowInl q k=false) : inl q=false := by
  simp [rowInl, Bool.or_eq_false_iff] at h
  exact h.1
theorem rowInl_lt (q k : Nat) (h : rowInl q k=true) : q<16 := by
  simp [rowInl, inl] at h
  omega
theorem rowInl_ge (q k : Nat) (h : rowInl q k=true) : 9≤q := by
  simp [rowInl, inl] at h
  omega
theorem mx_inl (q : Nat) (hq : inl q=true) : mx q=4 := by
  simp [inl] at hq; unfold mx; rw [if_neg (by omega), if_pos (by omega)]
theorem mx_rowInl (q k : Nat) (hq : rowInl q k=true) : mx q=4 := by
  have h1 := rowInl_lt q k hq
  have h2 := rowInl_ge q k hq
  unfold mx; rw [if_neg (by omega), if_pos h1]
theorem nRank_rowInl (q k : Nat) (hq : rowInl q k=true) : nRank q=125 := by
  have h1 := rowInl_lt q k hq
  unfold nRank; rw [if_neg (by omega), mx_rowInl q k hq]; norm_num
theorem inlineCheck_at (q k : Nat) (hq : rowInl q k=true) (hk : k<125) : inlineCheck q k=true := by
  cases hn : inl q
  · have hq16 := rowInl_lt q k hq
    have h := entCheck_at q k (by omega) hn (by rw [nRank_rowInl q k hq]; exact hk)
    simpa only [entCheck,hq,if_true] using h
  · exact inlineCheck_static_at q k hn hk
theorem s8Check_at (q k : Nat) (hq : q<17) (hk : k<nRank q) : s8Check q k=true := by
  cases hn : inl q
  · have h := tripleCheck_at q hq hn
    simp only [tripleCheck,Bool.and_eq_true] at h
    exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).2
  · have hm := mx_inl q hn
    have h16 : q ≠ 16 := by rintro rfl; simp [inl] at hn
    unfold nRank at hk; rw [if_neg h16, hm] at hk
    have h := inlineCheck_static_at q k hn (by norm_num at hk; omega)
    simp only [inlineCheck,Bool.and_eq_true] at h
    exact h.1.1.1.1
/-- Shared bodies of the r6 groups (all `dB, dC ≤ 5`) and of #938's non-inline r5 groups (`dB + dC < 3`). -/
theorem blockCheck_at (q dB dC : Nat) (hq : q<16) (hn : inl q=false) (hB : dB ≤ mx q) (hC : dC ≤ mx q)
    (hBC : q<9 ∨ dB+dC < 3) : blockCheck q dB dC=true := by
  have h := tripleCheck_at q (by omega) hn
  simp only [tripleCheck,Bool.and_eq_true] at h
  have h16 : q ≠ 16 := by omega
  have hh : (mx q+1)*dB+dC<nBlock q := by
    unfold nBlock; rw [if_neg h16]
    unfold mx at *
    split_ifs at * <;> nlinarith
  have e1 : ((mx q+1)*dB+dC)/(mx q+1)=dB := by
    unfold mx at *
    split_ifs at * <;> omega
  have e2 : ((mx q+1)*dB+dC)%(mx q+1)=dC := by
    unfold mx at *
    split_ifs at * <;> omega
  have hb := List.all_eq_true.mp h.2 ((mx q+1)*dB+dC) (List.mem_range.mpr hh)
  unfold liveBlock at hb
  rw [if_neg h16, e1, e2, if_pos (by omega)] at hb
  exact hb
/-- The r7 pair's 7 bodies (ladder of chain 48, chain 49 with digit `dB`, checksum dispatch). -/
theorem pairBlockCheck_at (dB : Nat) (hB : dB ≤ 6) : blockCheck 16 dB 0=true := by
  have h := tripleCheck_16
  simp only [tripleCheck,Bool.and_eq_true] at h
  have hb := List.all_eq_true.mp h.2 dB (List.mem_range.mpr (by unfold nBlock; simp; omega))
  unfold liveBlock at hb
  rw [if_pos rfl] at hb
  exact hb
theorem s8Run_at (q k : Nat) (hq : q<17) (hk : k<nRank q) :
    (if q=0 then rOK (vrun (entW 0 k) 1) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k)))=true := by
  have h := s8Check_at q k hq hk
  simp only [s8Check,Bool.and_eq_true] at h
  exact h.1
theorem bge9_at (k : Nat) (hk : k<125) (he : k%2=0) : vrun (cellW 9 k) 1=some (bge9R (cellW 9 k)) := by
  have h := s8Check_at 9 k (by decide +kernel) (by unfold nRank mx; norm_num; omega)
  simp only [s8Check,Bool.and_eq_true] at h
  have h2 := h.2
  rw [if_pos (by simp [he])] at h2
  exact rOK_eq h2
/-! ### T51: guards, checksum landings and arms (Part5) -/
theorem guard6Check_at (g raw : Nat) (hg : g<9) (hr : raw<256) : guard6Check g raw=true := by
  have h : guard6All g=true := by
    interval_cases g
    exacts [guard6All_0, guard6All_1, guard6All_2, guard6All_3, guard6All_4, guard6All_5, guard6All_6, guard6All_7,
      guard6All_8]
  exact List.all_eq_true.mp h raw (List.mem_range.mpr hr)
theorem r7GuardCheck_at (k : Nat) (hk : k<126) : r7GuardCheck k=true :=
  List.all_eq_true.mp r7GuardAll_ok k (List.mem_range.mpr hk)
theorem ckGuardCheck_at (ds : Nat) (hd : ds<232) : ckGuardCheck ds=true :=
  List.all_eq_true.mp ckGuardAll_ok ds (List.mem_range.mpr hd)
theorem ckArmCheck_at (d : Nat) (hd : d<6) : ckArmCheck d=true :=
  List.all_eq_true.mp ckArmAll_ok d (List.mem_range.mpr hd)
end SigGolfCandidate.T3M.Nonbinary
end
end
end
