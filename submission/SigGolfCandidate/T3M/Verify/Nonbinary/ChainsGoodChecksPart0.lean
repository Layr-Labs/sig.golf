import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheckParts

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_0_part_0 : (List.range' 0 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_8 : (List.range' 8 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_16 : (List.range' 16 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_24 : (List.range' 24 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_32 : (List.range' 32 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_40 : (List.range' 40 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_48 : (List.range' 48 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_56 : (List.range' 56 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_64 : (List.range' 64 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_72 : (List.range' 72 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_80 : (List.range' 80 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_88 : (List.range' 88 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_96 : (List.range' 96 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_104 : (List.range' 104 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_112 : (List.range' 112 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_120 : (List.range' 120 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_128 : (List.range' 128 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_136 : (List.range' 136 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_144 : (List.range' 144 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_152 : (List.range' 152 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_160 : (List.range' 160 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_168 : (List.range' 168 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_176 : (List.range' 176 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_184 : (List.range' 184 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_192 : (List.range' 192 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_200 : (List.range' 200 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_208 : (List.range' 208 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0 : (List.range' 0 216).all (fun k => entCheck 0 k && s8Check 0 k) = true := by
  exact (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 0 8 208 tripleEnt_0_part_0 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 8 8 200 tripleEnt_0_part_8 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 16 8 192 tripleEnt_0_part_16 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 24 8 184 tripleEnt_0_part_24 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 32 8 176 tripleEnt_0_part_32 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 40 8 168 tripleEnt_0_part_40 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 48 8 160 tripleEnt_0_part_48 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 56 8 152 tripleEnt_0_part_56 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 64 8 144 tripleEnt_0_part_64 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 72 8 136 tripleEnt_0_part_72 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 80 8 128 tripleEnt_0_part_80 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 88 8 120 tripleEnt_0_part_88 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 96 8 112 tripleEnt_0_part_96 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 104 8 104 tripleEnt_0_part_104 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 112 8 96 tripleEnt_0_part_112 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 120 8 88 tripleEnt_0_part_120 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 128 8 80 tripleEnt_0_part_128 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 136 8 72 tripleEnt_0_part_136 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 144 8 64 tripleEnt_0_part_144 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 152 8 56 tripleEnt_0_part_152 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 160 8 48 tripleEnt_0_part_160 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 168 8 40 tripleEnt_0_part_168 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 176 8 32 tripleEnt_0_part_176 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 184 8 24 tripleEnt_0_part_184 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 192 8 16 tripleEnt_0_part_192 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 200 8 8 tripleEnt_0_part_200 tripleEnt_0_part_208))))))))))))))))))))))))))
private theorem tripleBlock_0_part_0 : (List.range' 0 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_4 : (List.range' 4 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_8 : (List.range' 8 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_12 : (List.range' 12 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_16 : (List.range' 16 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_20 : (List.range' 20 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_24 : (List.range' 24 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_28 : (List.range' 28 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_32 : (List.range' 32 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0 : (List.range' 0 36).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 0 4 32 tripleBlock_0_part_0 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 4 4 28 tripleBlock_0_part_4 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 8 4 24 tripleBlock_0_part_8 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 12 4 20 tripleBlock_0_part_12 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 16 4 16 tripleBlock_0_part_16 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 20 4 12 tripleBlock_0_part_20 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 24 4 8 tripleBlock_0_part_24 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 28 4 4 tripleBlock_0_part_28 tripleBlock_0_part_32))))))))
theorem tripleCheck_0 : tripleCheck 0=true := by
  exact @tripleCheck_join 0 tripleEnt_0 tripleBlock_0
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_1_part_0 : (List.range' 0 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_8 : (List.range' 8 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_16 : (List.range' 16 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_24 : (List.range' 24 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_32 : (List.range' 32 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_40 : (List.range' 40 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_48 : (List.range' 48 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_56 : (List.range' 56 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_64 : (List.range' 64 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_72 : (List.range' 72 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_80 : (List.range' 80 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_88 : (List.range' 88 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_96 : (List.range' 96 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_104 : (List.range' 104 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_112 : (List.range' 112 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_120 : (List.range' 120 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_128 : (List.range' 128 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_136 : (List.range' 136 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_144 : (List.range' 144 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_152 : (List.range' 152 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_160 : (List.range' 160 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_168 : (List.range' 168 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_176 : (List.range' 176 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_184 : (List.range' 184 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_192 : (List.range' 192 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_200 : (List.range' 200 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_208 : (List.range' 208 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1 : (List.range' 0 216).all (fun k => entCheck 1 k && s8Check 1 k) = true := by
  exact (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 0 8 208 tripleEnt_1_part_0 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 8 8 200 tripleEnt_1_part_8 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 16 8 192 tripleEnt_1_part_16 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 24 8 184 tripleEnt_1_part_24 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 32 8 176 tripleEnt_1_part_32 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 40 8 168 tripleEnt_1_part_40 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 48 8 160 tripleEnt_1_part_48 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 56 8 152 tripleEnt_1_part_56 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 64 8 144 tripleEnt_1_part_64 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 72 8 136 tripleEnt_1_part_72 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 80 8 128 tripleEnt_1_part_80 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 88 8 120 tripleEnt_1_part_88 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 96 8 112 tripleEnt_1_part_96 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 104 8 104 tripleEnt_1_part_104 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 112 8 96 tripleEnt_1_part_112 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 120 8 88 tripleEnt_1_part_120 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 128 8 80 tripleEnt_1_part_128 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 136 8 72 tripleEnt_1_part_136 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 144 8 64 tripleEnt_1_part_144 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 152 8 56 tripleEnt_1_part_152 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 160 8 48 tripleEnt_1_part_160 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 168 8 40 tripleEnt_1_part_168 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 176 8 32 tripleEnt_1_part_176 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 184 8 24 tripleEnt_1_part_184 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 192 8 16 tripleEnt_1_part_192 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 200 8 8 tripleEnt_1_part_200 tripleEnt_1_part_208))))))))))))))))))))))))))
private theorem tripleBlock_1_part_0 : (List.range' 0 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_4 : (List.range' 4 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_8 : (List.range' 8 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_12 : (List.range' 12 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_16 : (List.range' 16 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_20 : (List.range' 20 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_24 : (List.range' 24 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_28 : (List.range' 28 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_32 : (List.range' 32 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1 : (List.range' 0 36).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 0 4 32 tripleBlock_1_part_0 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 4 4 28 tripleBlock_1_part_4 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 8 4 24 tripleBlock_1_part_8 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 12 4 20 tripleBlock_1_part_12 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 16 4 16 tripleBlock_1_part_16 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 20 4 12 tripleBlock_1_part_20 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 24 4 8 tripleBlock_1_part_24 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 28 4 4 tripleBlock_1_part_28 tripleBlock_1_part_32))))))))
theorem tripleCheck_1 : tripleCheck 1=true := by
  exact @tripleCheck_join 1 tripleEnt_1 tripleBlock_1
end SigGolfCandidate.T3M.Nonbinary
end
end
