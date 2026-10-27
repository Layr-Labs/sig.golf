import SigGolfCandidate.Merge112

-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart2 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_4_part_0 : (List.range' 0 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_8 : (List.range' 8 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_16 : (List.range' 16 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_24 : (List.range' 24 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_32 : (List.range' 32 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_40 : (List.range' 40 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_48 : (List.range' 48 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_56 : (List.range' 56 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_64 : (List.range' 64 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_72 : (List.range' 72 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_80 : (List.range' 80 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_88 : (List.range' 88 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_96 : (List.range' 96 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_104 : (List.range' 104 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_112 : (List.range' 112 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_120 : (List.range' 120 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_128 : (List.range' 128 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_136 : (List.range' 136 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_144 : (List.range' 144 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_152 : (List.range' 152 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_160 : (List.range' 160 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_168 : (List.range' 168 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_176 : (List.range' 176 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_184 : (List.range' 184 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_192 : (List.range' 192 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_200 : (List.range' 200 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_208 : (List.range' 208 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4 : (List.range' 0 216).all (fun k => entCheck 4 k && s8Check 4 k) = true := by
  exact (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 0 8 208 tripleEnt_4_part_0 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 8 8 200 tripleEnt_4_part_8 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 16 8 192 tripleEnt_4_part_16 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 24 8 184 tripleEnt_4_part_24 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 32 8 176 tripleEnt_4_part_32 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 40 8 168 tripleEnt_4_part_40 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 48 8 160 tripleEnt_4_part_48 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 56 8 152 tripleEnt_4_part_56 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 64 8 144 tripleEnt_4_part_64 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 72 8 136 tripleEnt_4_part_72 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 80 8 128 tripleEnt_4_part_80 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 88 8 120 tripleEnt_4_part_88 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 96 8 112 tripleEnt_4_part_96 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 104 8 104 tripleEnt_4_part_104 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 112 8 96 tripleEnt_4_part_112 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 120 8 88 tripleEnt_4_part_120 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 128 8 80 tripleEnt_4_part_128 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 136 8 72 tripleEnt_4_part_136 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 144 8 64 tripleEnt_4_part_144 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 152 8 56 tripleEnt_4_part_152 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 160 8 48 tripleEnt_4_part_160 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 168 8 40 tripleEnt_4_part_168 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 176 8 32 tripleEnt_4_part_176 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 184 8 24 tripleEnt_4_part_184 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 192 8 16 tripleEnt_4_part_192 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 200 8 8 tripleEnt_4_part_200 tripleEnt_4_part_208))))))))))))))))))))))))))
private theorem tripleBlock_4_part_0 : (List.range' 0 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_4 : (List.range' 4 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_8 : (List.range' 8 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_12 : (List.range' 12 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_16 : (List.range' 16 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_20 : (List.range' 20 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_24 : (List.range' 24 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_28 : (List.range' 28 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_32 : (List.range' 32 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4 : (List.range' 0 36).all (liveBlock 4) = true := by
  exact (@check_range_add (liveBlock 4) 0 4 32 tripleBlock_4_part_0 (@check_range_add (liveBlock 4) 4 4 28 tripleBlock_4_part_4 (@check_range_add (liveBlock 4) 8 4 24 tripleBlock_4_part_8 (@check_range_add (liveBlock 4) 12 4 20 tripleBlock_4_part_12 (@check_range_add (liveBlock 4) 16 4 16 tripleBlock_4_part_16 (@check_range_add (liveBlock 4) 20 4 12 tripleBlock_4_part_20 (@check_range_add (liveBlock 4) 24 4 8 tripleBlock_4_part_24 (@check_range_add (liveBlock 4) 28 4 4 tripleBlock_4_part_28 tripleBlock_4_part_32))))))))
theorem tripleCheck_4 : tripleCheck 4=true := by
  exact @tripleCheck_join 4 tripleEnt_4 tripleBlock_4
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_5_part_0 : (List.range' 0 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_8 : (List.range' 8 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_16 : (List.range' 16 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_24 : (List.range' 24 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_32 : (List.range' 32 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_40 : (List.range' 40 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_48 : (List.range' 48 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_56 : (List.range' 56 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_64 : (List.range' 64 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_72 : (List.range' 72 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_80 : (List.range' 80 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_88 : (List.range' 88 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_96 : (List.range' 96 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_104 : (List.range' 104 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_112 : (List.range' 112 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_120 : (List.range' 120 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_128 : (List.range' 128 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_136 : (List.range' 136 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_144 : (List.range' 144 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_152 : (List.range' 152 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_160 : (List.range' 160 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_168 : (List.range' 168 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_176 : (List.range' 176 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_184 : (List.range' 184 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_192 : (List.range' 192 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_200 : (List.range' 200 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_208 : (List.range' 208 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5 : (List.range' 0 216).all (fun k => entCheck 5 k && s8Check 5 k) = true := by
  exact (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 0 8 208 tripleEnt_5_part_0 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 8 8 200 tripleEnt_5_part_8 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 16 8 192 tripleEnt_5_part_16 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 24 8 184 tripleEnt_5_part_24 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 32 8 176 tripleEnt_5_part_32 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 40 8 168 tripleEnt_5_part_40 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 48 8 160 tripleEnt_5_part_48 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 56 8 152 tripleEnt_5_part_56 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 64 8 144 tripleEnt_5_part_64 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 72 8 136 tripleEnt_5_part_72 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 80 8 128 tripleEnt_5_part_80 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 88 8 120 tripleEnt_5_part_88 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 96 8 112 tripleEnt_5_part_96 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 104 8 104 tripleEnt_5_part_104 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 112 8 96 tripleEnt_5_part_112 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 120 8 88 tripleEnt_5_part_120 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 128 8 80 tripleEnt_5_part_128 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 136 8 72 tripleEnt_5_part_136 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 144 8 64 tripleEnt_5_part_144 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 152 8 56 tripleEnt_5_part_152 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 160 8 48 tripleEnt_5_part_160 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 168 8 40 tripleEnt_5_part_168 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 176 8 32 tripleEnt_5_part_176 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 184 8 24 tripleEnt_5_part_184 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 192 8 16 tripleEnt_5_part_192 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 200 8 8 tripleEnt_5_part_200 tripleEnt_5_part_208))))))))))))))))))))))))))
private theorem tripleBlock_5_part_0 : (List.range' 0 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_4 : (List.range' 4 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_8 : (List.range' 8 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_12 : (List.range' 12 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_16 : (List.range' 16 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_20 : (List.range' 20 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_24 : (List.range' 24 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_28 : (List.range' 28 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_32 : (List.range' 32 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5 : (List.range' 0 36).all (liveBlock 5) = true := by
  exact (@check_range_add (liveBlock 5) 0 4 32 tripleBlock_5_part_0 (@check_range_add (liveBlock 5) 4 4 28 tripleBlock_5_part_4 (@check_range_add (liveBlock 5) 8 4 24 tripleBlock_5_part_8 (@check_range_add (liveBlock 5) 12 4 20 tripleBlock_5_part_12 (@check_range_add (liveBlock 5) 16 4 16 tripleBlock_5_part_16 (@check_range_add (liveBlock 5) 20 4 12 tripleBlock_5_part_20 (@check_range_add (liveBlock 5) 24 4 8 tripleBlock_5_part_24 (@check_range_add (liveBlock 5) 28 4 4 tripleBlock_5_part_28 tripleBlock_5_part_32))))))))
theorem tripleCheck_5 : tripleCheck 5=true := by
  exact @tripleCheck_join 5 tripleEnt_5 tripleBlock_5
end SigGolfCandidate.T3M.Nonbinary
end
end
end
