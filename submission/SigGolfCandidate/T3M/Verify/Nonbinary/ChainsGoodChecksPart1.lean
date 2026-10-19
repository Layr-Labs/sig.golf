import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheckParts

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_2_part_0 : (List.range' 0 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_8 : (List.range' 8 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_16 : (List.range' 16 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_24 : (List.range' 24 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_32 : (List.range' 32 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_40 : (List.range' 40 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_48 : (List.range' 48 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_56 : (List.range' 56 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_64 : (List.range' 64 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_72 : (List.range' 72 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_80 : (List.range' 80 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_88 : (List.range' 88 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_96 : (List.range' 96 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_104 : (List.range' 104 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_112 : (List.range' 112 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_120 : (List.range' 120 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_128 : (List.range' 128 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_136 : (List.range' 136 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_144 : (List.range' 144 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_152 : (List.range' 152 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_160 : (List.range' 160 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_168 : (List.range' 168 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_176 : (List.range' 176 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_184 : (List.range' 184 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_192 : (List.range' 192 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_200 : (List.range' 200 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_208 : (List.range' 208 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2 : (List.range' 0 216).all (fun k => entCheck 2 k && s8Check 2 k) = true := by
  exact (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 0 8 208 tripleEnt_2_part_0 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 8 8 200 tripleEnt_2_part_8 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 16 8 192 tripleEnt_2_part_16 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 24 8 184 tripleEnt_2_part_24 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 32 8 176 tripleEnt_2_part_32 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 40 8 168 tripleEnt_2_part_40 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 48 8 160 tripleEnt_2_part_48 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 56 8 152 tripleEnt_2_part_56 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 64 8 144 tripleEnt_2_part_64 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 72 8 136 tripleEnt_2_part_72 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 80 8 128 tripleEnt_2_part_80 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 88 8 120 tripleEnt_2_part_88 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 96 8 112 tripleEnt_2_part_96 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 104 8 104 tripleEnt_2_part_104 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 112 8 96 tripleEnt_2_part_112 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 120 8 88 tripleEnt_2_part_120 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 128 8 80 tripleEnt_2_part_128 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 136 8 72 tripleEnt_2_part_136 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 144 8 64 tripleEnt_2_part_144 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 152 8 56 tripleEnt_2_part_152 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 160 8 48 tripleEnt_2_part_160 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 168 8 40 tripleEnt_2_part_168 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 176 8 32 tripleEnt_2_part_176 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 184 8 24 tripleEnt_2_part_184 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 192 8 16 tripleEnt_2_part_192 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 200 8 8 tripleEnt_2_part_200 tripleEnt_2_part_208))))))))))))))))))))))))))
private theorem tripleBlock_2_part_0 : (List.range' 0 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_4 : (List.range' 4 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_8 : (List.range' 8 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_12 : (List.range' 12 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_16 : (List.range' 16 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_20 : (List.range' 20 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_24 : (List.range' 24 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_28 : (List.range' 28 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_32 : (List.range' 32 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2 : (List.range' 0 36).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 0 4 32 tripleBlock_2_part_0 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 4 4 28 tripleBlock_2_part_4 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 8 4 24 tripleBlock_2_part_8 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 12 4 20 tripleBlock_2_part_12 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 16 4 16 tripleBlock_2_part_16 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 20 4 12 tripleBlock_2_part_20 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 24 4 8 tripleBlock_2_part_24 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 28 4 4 tripleBlock_2_part_28 tripleBlock_2_part_32))))))))
theorem tripleCheck_2 : tripleCheck 2=true := by
  exact @tripleCheck_join 2 tripleEnt_2 tripleBlock_2
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_3_part_0 : (List.range' 0 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_8 : (List.range' 8 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_16 : (List.range' 16 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_24 : (List.range' 24 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_32 : (List.range' 32 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_40 : (List.range' 40 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_48 : (List.range' 48 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_56 : (List.range' 56 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_64 : (List.range' 64 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_72 : (List.range' 72 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_80 : (List.range' 80 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_88 : (List.range' 88 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_96 : (List.range' 96 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_104 : (List.range' 104 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_112 : (List.range' 112 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_120 : (List.range' 120 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_128 : (List.range' 128 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_136 : (List.range' 136 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_144 : (List.range' 144 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_152 : (List.range' 152 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_160 : (List.range' 160 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_168 : (List.range' 168 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_176 : (List.range' 176 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_184 : (List.range' 184 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_192 : (List.range' 192 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_200 : (List.range' 200 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_208 : (List.range' 208 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3 : (List.range' 0 216).all (fun k => entCheck 3 k && s8Check 3 k) = true := by
  exact (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 0 8 208 tripleEnt_3_part_0 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 8 8 200 tripleEnt_3_part_8 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 16 8 192 tripleEnt_3_part_16 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 24 8 184 tripleEnt_3_part_24 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 32 8 176 tripleEnt_3_part_32 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 40 8 168 tripleEnt_3_part_40 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 48 8 160 tripleEnt_3_part_48 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 56 8 152 tripleEnt_3_part_56 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 64 8 144 tripleEnt_3_part_64 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 72 8 136 tripleEnt_3_part_72 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 80 8 128 tripleEnt_3_part_80 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 88 8 120 tripleEnt_3_part_88 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 96 8 112 tripleEnt_3_part_96 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 104 8 104 tripleEnt_3_part_104 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 112 8 96 tripleEnt_3_part_112 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 120 8 88 tripleEnt_3_part_120 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 128 8 80 tripleEnt_3_part_128 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 136 8 72 tripleEnt_3_part_136 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 144 8 64 tripleEnt_3_part_144 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 152 8 56 tripleEnt_3_part_152 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 160 8 48 tripleEnt_3_part_160 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 168 8 40 tripleEnt_3_part_168 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 176 8 32 tripleEnt_3_part_176 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 184 8 24 tripleEnt_3_part_184 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 192 8 16 tripleEnt_3_part_192 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 200 8 8 tripleEnt_3_part_200 tripleEnt_3_part_208))))))))))))))))))))))))))
private theorem tripleBlock_3_part_0 : (List.range' 0 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_4 : (List.range' 4 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_8 : (List.range' 8 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_12 : (List.range' 12 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_16 : (List.range' 16 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_20 : (List.range' 20 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_24 : (List.range' 24 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_28 : (List.range' 28 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_32 : (List.range' 32 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3 : (List.range' 0 36).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 0 4 32 tripleBlock_3_part_0 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 4 4 28 tripleBlock_3_part_4 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 8 4 24 tripleBlock_3_part_8 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 12 4 20 tripleBlock_3_part_12 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 16 4 16 tripleBlock_3_part_16 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 20 4 12 tripleBlock_3_part_20 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 24 4 8 tripleBlock_3_part_24 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 28 4 4 tripleBlock_3_part_28 tripleBlock_3_part_32))))))))
theorem tripleCheck_3 : tripleCheck 3=true := by
  exact @tripleCheck_join 3 tripleEnt_3 tripleBlock_3
end SigGolfCandidate.T3M.Nonbinary
end
end
