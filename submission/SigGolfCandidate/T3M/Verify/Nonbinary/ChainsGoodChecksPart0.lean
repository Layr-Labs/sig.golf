import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem
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
private theorem tripleEnt_0_part_120 : (List.range' 120 5).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0 : (List.range' 0 125).all (fun k => entCheck 0 k && s8Check 0 k) = true := by
  exact (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 0 8 117 tripleEnt_0_part_0 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 8 8 109 tripleEnt_0_part_8 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 16 8 101 tripleEnt_0_part_16 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 24 8 93 tripleEnt_0_part_24 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 32 8 85 tripleEnt_0_part_32 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 40 8 77 tripleEnt_0_part_40 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 48 8 69 tripleEnt_0_part_48 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 56 8 61 tripleEnt_0_part_56 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 64 8 53 tripleEnt_0_part_64 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 72 8 45 tripleEnt_0_part_72 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 80 8 37 tripleEnt_0_part_80 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 88 8 29 tripleEnt_0_part_88 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 96 8 21 tripleEnt_0_part_96 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 104 8 13 tripleEnt_0_part_104 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 112 8 5 tripleEnt_0_part_112 tripleEnt_0_part_120)))))))))))))))
private theorem tripleBlock_0_part_0 : (List.range' 0 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_4 : (List.range' 4 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_8 : (List.range' 8 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_12 : (List.range' 12 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_16 : (List.range' 16 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_20 : (List.range' 20 4).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0_part_24 : (List.range' 24 1).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by decide +kernel
private theorem tripleBlock_0 : (List.range' 0 25).all (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 0 4 21 tripleBlock_0_part_0 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 4 4 17 tripleBlock_0_part_4 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 8 4 13 tripleBlock_0_part_8 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 12 4 9 tripleBlock_0_part_12 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 16 4 5 tripleBlock_0_part_16 (@check_range_add (fun x => blockCheck 0 (x / (mx 0 + 1)) (x % (mx 0 + 1))) 20 4 1 tripleBlock_0_part_20 tripleBlock_0_part_24))))))
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
private theorem tripleEnt_1_part_120 : (List.range' 120 5).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1 : (List.range' 0 125).all (fun k => entCheck 1 k && s8Check 1 k) = true := by
  exact (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 0 8 117 tripleEnt_1_part_0 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 8 8 109 tripleEnt_1_part_8 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 16 8 101 tripleEnt_1_part_16 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 24 8 93 tripleEnt_1_part_24 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 32 8 85 tripleEnt_1_part_32 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 40 8 77 tripleEnt_1_part_40 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 48 8 69 tripleEnt_1_part_48 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 56 8 61 tripleEnt_1_part_56 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 64 8 53 tripleEnt_1_part_64 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 72 8 45 tripleEnt_1_part_72 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 80 8 37 tripleEnt_1_part_80 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 88 8 29 tripleEnt_1_part_88 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 96 8 21 tripleEnt_1_part_96 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 104 8 13 tripleEnt_1_part_104 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 112 8 5 tripleEnt_1_part_112 tripleEnt_1_part_120)))))))))))))))
private theorem tripleBlock_1_part_0 : (List.range' 0 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_4 : (List.range' 4 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_8 : (List.range' 8 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_12 : (List.range' 12 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_16 : (List.range' 16 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_20 : (List.range' 20 4).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1_part_24 : (List.range' 24 1).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by decide +kernel
private theorem tripleBlock_1 : (List.range' 0 25).all (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 0 4 21 tripleBlock_1_part_0 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 4 4 17 tripleBlock_1_part_4 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 8 4 13 tripleBlock_1_part_8 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 12 4 9 tripleBlock_1_part_12 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 16 4 5 tripleBlock_1_part_16 (@check_range_add (fun x => blockCheck 1 (x / (mx 1 + 1)) (x % (mx 1 + 1))) 20 4 1 tripleBlock_1_part_20 tripleBlock_1_part_24))))))
theorem tripleCheck_1 : tripleCheck 1=true := by
  exact @tripleCheck_join 1 tripleEnt_1 tripleBlock_1
end SigGolfCandidate.T3M.Nonbinary
end
end
