import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsCheckParts

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
