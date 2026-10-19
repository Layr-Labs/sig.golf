import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheckParts

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_6_part_0 : (List.range' 0 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_8 : (List.range' 8 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_16 : (List.range' 16 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_24 : (List.range' 24 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_32 : (List.range' 32 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_40 : (List.range' 40 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_48 : (List.range' 48 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_56 : (List.range' 56 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_64 : (List.range' 64 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_72 : (List.range' 72 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_80 : (List.range' 80 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_88 : (List.range' 88 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_96 : (List.range' 96 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_104 : (List.range' 104 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_112 : (List.range' 112 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_120 : (List.range' 120 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_128 : (List.range' 128 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_136 : (List.range' 136 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_144 : (List.range' 144 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_152 : (List.range' 152 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_160 : (List.range' 160 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_168 : (List.range' 168 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_176 : (List.range' 176 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_184 : (List.range' 184 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_192 : (List.range' 192 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_200 : (List.range' 200 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_208 : (List.range' 208 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6 : (List.range' 0 216).all (fun k => entCheck 6 k && s8Check 6 k) = true := by
  exact (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 0 8 208 tripleEnt_6_part_0 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 8 8 200 tripleEnt_6_part_8 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 16 8 192 tripleEnt_6_part_16 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 24 8 184 tripleEnt_6_part_24 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 32 8 176 tripleEnt_6_part_32 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 40 8 168 tripleEnt_6_part_40 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 48 8 160 tripleEnt_6_part_48 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 56 8 152 tripleEnt_6_part_56 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 64 8 144 tripleEnt_6_part_64 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 72 8 136 tripleEnt_6_part_72 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 80 8 128 tripleEnt_6_part_80 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 88 8 120 tripleEnt_6_part_88 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 96 8 112 tripleEnt_6_part_96 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 104 8 104 tripleEnt_6_part_104 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 112 8 96 tripleEnt_6_part_112 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 120 8 88 tripleEnt_6_part_120 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 128 8 80 tripleEnt_6_part_128 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 136 8 72 tripleEnt_6_part_136 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 144 8 64 tripleEnt_6_part_144 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 152 8 56 tripleEnt_6_part_152 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 160 8 48 tripleEnt_6_part_160 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 168 8 40 tripleEnt_6_part_168 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 176 8 32 tripleEnt_6_part_176 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 184 8 24 tripleEnt_6_part_184 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 192 8 16 tripleEnt_6_part_192 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 200 8 8 tripleEnt_6_part_200 tripleEnt_6_part_208))))))))))))))))))))))))))
private theorem tripleBlock_6_part_0 : (List.range' 0 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_4 : (List.range' 4 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_8 : (List.range' 8 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_12 : (List.range' 12 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_16 : (List.range' 16 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_20 : (List.range' 20 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_24 : (List.range' 24 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_28 : (List.range' 28 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_32 : (List.range' 32 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6 : (List.range' 0 36).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 0 4 32 tripleBlock_6_part_0 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 4 4 28 tripleBlock_6_part_4 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 8 4 24 tripleBlock_6_part_8 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 12 4 20 tripleBlock_6_part_12 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 16 4 16 tripleBlock_6_part_16 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 20 4 12 tripleBlock_6_part_20 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 24 4 8 tripleBlock_6_part_24 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 28 4 4 tripleBlock_6_part_28 tripleBlock_6_part_32))))))))
theorem tripleCheck_6 : tripleCheck 6=true := by
  exact @tripleCheck_join 6 tripleEnt_6 tripleBlock_6
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_7_part_0 : (List.range' 0 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_8 : (List.range' 8 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_16 : (List.range' 16 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_24 : (List.range' 24 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_32 : (List.range' 32 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_40 : (List.range' 40 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_48 : (List.range' 48 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_56 : (List.range' 56 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_64 : (List.range' 64 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_72 : (List.range' 72 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_80 : (List.range' 80 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_88 : (List.range' 88 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_96 : (List.range' 96 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_104 : (List.range' 104 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_112 : (List.range' 112 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_120 : (List.range' 120 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_128 : (List.range' 128 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_136 : (List.range' 136 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_144 : (List.range' 144 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_152 : (List.range' 152 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_160 : (List.range' 160 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_168 : (List.range' 168 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_176 : (List.range' 176 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_184 : (List.range' 184 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_192 : (List.range' 192 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_200 : (List.range' 200 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_208 : (List.range' 208 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7 : (List.range' 0 216).all (fun k => entCheck 7 k && s8Check 7 k) = true := by
  exact (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 0 8 208 tripleEnt_7_part_0 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 8 8 200 tripleEnt_7_part_8 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 16 8 192 tripleEnt_7_part_16 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 24 8 184 tripleEnt_7_part_24 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 32 8 176 tripleEnt_7_part_32 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 40 8 168 tripleEnt_7_part_40 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 48 8 160 tripleEnt_7_part_48 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 56 8 152 tripleEnt_7_part_56 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 64 8 144 tripleEnt_7_part_64 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 72 8 136 tripleEnt_7_part_72 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 80 8 128 tripleEnt_7_part_80 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 88 8 120 tripleEnt_7_part_88 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 96 8 112 tripleEnt_7_part_96 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 104 8 104 tripleEnt_7_part_104 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 112 8 96 tripleEnt_7_part_112 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 120 8 88 tripleEnt_7_part_120 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 128 8 80 tripleEnt_7_part_128 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 136 8 72 tripleEnt_7_part_136 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 144 8 64 tripleEnt_7_part_144 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 152 8 56 tripleEnt_7_part_152 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 160 8 48 tripleEnt_7_part_160 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 168 8 40 tripleEnt_7_part_168 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 176 8 32 tripleEnt_7_part_176 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 184 8 24 tripleEnt_7_part_184 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 192 8 16 tripleEnt_7_part_192 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 200 8 8 tripleEnt_7_part_200 tripleEnt_7_part_208))))))))))))))))))))))))))
private theorem tripleBlock_7_part_0 : (List.range' 0 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_4 : (List.range' 4 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_8 : (List.range' 8 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_12 : (List.range' 12 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_16 : (List.range' 16 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_20 : (List.range' 20 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_24 : (List.range' 24 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_28 : (List.range' 28 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_32 : (List.range' 32 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7 : (List.range' 0 36).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 0 4 32 tripleBlock_7_part_0 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 4 4 28 tripleBlock_7_part_4 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 8 4 24 tripleBlock_7_part_8 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 12 4 20 tripleBlock_7_part_12 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 16 4 16 tripleBlock_7_part_16 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 20 4 12 tripleBlock_7_part_20 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 24 4 8 tripleBlock_7_part_24 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 28 4 4 tripleBlock_7_part_28 tripleBlock_7_part_32))))))))
theorem tripleCheck_7 : tripleCheck 7=true := by
  exact @tripleCheck_join 7 tripleEnt_7 tripleBlock_7
end SigGolfCandidate.T3M.Nonbinary
end
end
