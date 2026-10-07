import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheckParts

set_option Elab.async false
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
private theorem tripleEnt_2_part_120 : (List.range' 120 5).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2 : (List.range' 0 125).all (fun k => entCheck 2 k && s8Check 2 k) = true := by
  exact (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 0 8 117 tripleEnt_2_part_0 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 8 8 109 tripleEnt_2_part_8 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 16 8 101 tripleEnt_2_part_16 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 24 8 93 tripleEnt_2_part_24 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 32 8 85 tripleEnt_2_part_32 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 40 8 77 tripleEnt_2_part_40 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 48 8 69 tripleEnt_2_part_48 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 56 8 61 tripleEnt_2_part_56 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 64 8 53 tripleEnt_2_part_64 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 72 8 45 tripleEnt_2_part_72 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 80 8 37 tripleEnt_2_part_80 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 88 8 29 tripleEnt_2_part_88 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 96 8 21 tripleEnt_2_part_96 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 104 8 13 tripleEnt_2_part_104 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 112 8 5 tripleEnt_2_part_112 tripleEnt_2_part_120)))))))))))))))
private theorem tripleBlock_2_part_0 : (List.range' 0 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_4 : (List.range' 4 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_8 : (List.range' 8 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_12 : (List.range' 12 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_16 : (List.range' 16 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_20 : (List.range' 20 4).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2_part_24 : (List.range' 24 1).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by decide +kernel
private theorem tripleBlock_2 : (List.range' 0 25).all (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 0 4 21 tripleBlock_2_part_0 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 4 4 17 tripleBlock_2_part_4 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 8 4 13 tripleBlock_2_part_8 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 12 4 9 tripleBlock_2_part_12 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 16 4 5 tripleBlock_2_part_16 (@check_range_add (fun x => blockCheck 2 (x / (mx 2 + 1)) (x % (mx 2 + 1))) 20 4 1 tripleBlock_2_part_20 tripleBlock_2_part_24))))))
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
private theorem tripleEnt_3_part_120 : (List.range' 120 5).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3 : (List.range' 0 125).all (fun k => entCheck 3 k && s8Check 3 k) = true := by
  exact (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 0 8 117 tripleEnt_3_part_0 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 8 8 109 tripleEnt_3_part_8 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 16 8 101 tripleEnt_3_part_16 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 24 8 93 tripleEnt_3_part_24 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 32 8 85 tripleEnt_3_part_32 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 40 8 77 tripleEnt_3_part_40 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 48 8 69 tripleEnt_3_part_48 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 56 8 61 tripleEnt_3_part_56 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 64 8 53 tripleEnt_3_part_64 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 72 8 45 tripleEnt_3_part_72 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 80 8 37 tripleEnt_3_part_80 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 88 8 29 tripleEnt_3_part_88 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 96 8 21 tripleEnt_3_part_96 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 104 8 13 tripleEnt_3_part_104 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 112 8 5 tripleEnt_3_part_112 tripleEnt_3_part_120)))))))))))))))
private theorem tripleBlock_3_part_0 : (List.range' 0 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_4 : (List.range' 4 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_8 : (List.range' 8 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_12 : (List.range' 12 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_16 : (List.range' 16 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_20 : (List.range' 20 4).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3_part_24 : (List.range' 24 1).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by decide +kernel
private theorem tripleBlock_3 : (List.range' 0 25).all (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 0 4 21 tripleBlock_3_part_0 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 4 4 17 tripleBlock_3_part_4 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 8 4 13 tripleBlock_3_part_8 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 12 4 9 tripleBlock_3_part_12 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 16 4 5 tripleBlock_3_part_16 (@check_range_add (fun x => blockCheck 3 (x / (mx 3 + 1)) (x % (mx 3 + 1))) 20 4 1 tripleBlock_3_part_20 tripleBlock_3_part_24))))))
theorem tripleCheck_3 : tripleCheck 3=true := by
  exact @tripleCheck_join 3 tripleEnt_3 tripleBlock_3
end SigGolfCandidate.T3M.Nonbinary
end
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
private theorem tripleEnt_4_part_120 : (List.range' 120 5).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4 : (List.range' 0 125).all (fun k => entCheck 4 k && s8Check 4 k) = true := by
  exact (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 0 8 117 tripleEnt_4_part_0 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 8 8 109 tripleEnt_4_part_8 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 16 8 101 tripleEnt_4_part_16 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 24 8 93 tripleEnt_4_part_24 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 32 8 85 tripleEnt_4_part_32 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 40 8 77 tripleEnt_4_part_40 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 48 8 69 tripleEnt_4_part_48 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 56 8 61 tripleEnt_4_part_56 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 64 8 53 tripleEnt_4_part_64 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 72 8 45 tripleEnt_4_part_72 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 80 8 37 tripleEnt_4_part_80 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 88 8 29 tripleEnt_4_part_88 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 96 8 21 tripleEnt_4_part_96 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 104 8 13 tripleEnt_4_part_104 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 112 8 5 tripleEnt_4_part_112 tripleEnt_4_part_120)))))))))))))))
private theorem tripleBlock_4_part_0 : (List.range' 0 4).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by decide +kernel
private theorem tripleBlock_4_part_4 : (List.range' 4 4).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by decide +kernel
private theorem tripleBlock_4_part_8 : (List.range' 8 4).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by decide +kernel
private theorem tripleBlock_4_part_12 : (List.range' 12 4).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by decide +kernel
private theorem tripleBlock_4_part_16 : (List.range' 16 4).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by decide +kernel
private theorem tripleBlock_4_part_20 : (List.range' 20 4).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by decide +kernel
private theorem tripleBlock_4_part_24 : (List.range' 24 1).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by decide +kernel
private theorem tripleBlock_4 : (List.range' 0 25).all (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) 0 4 21 tripleBlock_4_part_0 (@check_range_add (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) 4 4 17 tripleBlock_4_part_4 (@check_range_add (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) 8 4 13 tripleBlock_4_part_8 (@check_range_add (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) 12 4 9 tripleBlock_4_part_12 (@check_range_add (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) 16 4 5 tripleBlock_4_part_16 (@check_range_add (fun x => blockCheck 4 (x / (mx 4 + 1)) (x % (mx 4 + 1))) 20 4 1 tripleBlock_4_part_20 tripleBlock_4_part_24))))))
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
private theorem tripleEnt_5_part_120 : (List.range' 120 5).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5 : (List.range' 0 125).all (fun k => entCheck 5 k && s8Check 5 k) = true := by
  exact (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 0 8 117 tripleEnt_5_part_0 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 8 8 109 tripleEnt_5_part_8 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 16 8 101 tripleEnt_5_part_16 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 24 8 93 tripleEnt_5_part_24 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 32 8 85 tripleEnt_5_part_32 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 40 8 77 tripleEnt_5_part_40 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 48 8 69 tripleEnt_5_part_48 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 56 8 61 tripleEnt_5_part_56 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 64 8 53 tripleEnt_5_part_64 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 72 8 45 tripleEnt_5_part_72 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 80 8 37 tripleEnt_5_part_80 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 88 8 29 tripleEnt_5_part_88 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 96 8 21 tripleEnt_5_part_96 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 104 8 13 tripleEnt_5_part_104 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 112 8 5 tripleEnt_5_part_112 tripleEnt_5_part_120)))))))))))))))
private theorem tripleBlock_5_part_0 : (List.range' 0 4).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by decide +kernel
private theorem tripleBlock_5_part_4 : (List.range' 4 4).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by decide +kernel
private theorem tripleBlock_5_part_8 : (List.range' 8 4).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by decide +kernel
private theorem tripleBlock_5_part_12 : (List.range' 12 4).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by decide +kernel
private theorem tripleBlock_5_part_16 : (List.range' 16 4).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by decide +kernel
private theorem tripleBlock_5_part_20 : (List.range' 20 4).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by decide +kernel
private theorem tripleBlock_5_part_24 : (List.range' 24 1).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by decide +kernel
private theorem tripleBlock_5 : (List.range' 0 25).all (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) 0 4 21 tripleBlock_5_part_0 (@check_range_add (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) 4 4 17 tripleBlock_5_part_4 (@check_range_add (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) 8 4 13 tripleBlock_5_part_8 (@check_range_add (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) 12 4 9 tripleBlock_5_part_12 (@check_range_add (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) 16 4 5 tripleBlock_5_part_16 (@check_range_add (fun x => blockCheck 5 (x / (mx 5 + 1)) (x % (mx 5 + 1))) 20 4 1 tripleBlock_5_part_20 tripleBlock_5_part_24))))))
theorem tripleCheck_5 : tripleCheck 5=true := by
  exact @tripleCheck_join 5 tripleEnt_5 tripleBlock_5
end SigGolfCandidate.T3M.Nonbinary
end
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
private theorem tripleEnt_6_part_120 : (List.range' 120 5).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6 : (List.range' 0 125).all (fun k => entCheck 6 k && s8Check 6 k) = true := by
  exact (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 0 8 117 tripleEnt_6_part_0 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 8 8 109 tripleEnt_6_part_8 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 16 8 101 tripleEnt_6_part_16 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 24 8 93 tripleEnt_6_part_24 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 32 8 85 tripleEnt_6_part_32 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 40 8 77 tripleEnt_6_part_40 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 48 8 69 tripleEnt_6_part_48 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 56 8 61 tripleEnt_6_part_56 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 64 8 53 tripleEnt_6_part_64 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 72 8 45 tripleEnt_6_part_72 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 80 8 37 tripleEnt_6_part_80 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 88 8 29 tripleEnt_6_part_88 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 96 8 21 tripleEnt_6_part_96 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 104 8 13 tripleEnt_6_part_104 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 112 8 5 tripleEnt_6_part_112 tripleEnt_6_part_120)))))))))))))))
private theorem tripleBlock_6_part_0 : (List.range' 0 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_4 : (List.range' 4 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_8 : (List.range' 8 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_12 : (List.range' 12 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_16 : (List.range' 16 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_20 : (List.range' 20 4).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6_part_24 : (List.range' 24 1).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by decide +kernel
private theorem tripleBlock_6 : (List.range' 0 25).all (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 0 4 21 tripleBlock_6_part_0 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 4 4 17 tripleBlock_6_part_4 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 8 4 13 tripleBlock_6_part_8 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 12 4 9 tripleBlock_6_part_12 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 16 4 5 tripleBlock_6_part_16 (@check_range_add (fun x => blockCheck 6 (x / (mx 6 + 1)) (x % (mx 6 + 1))) 20 4 1 tripleBlock_6_part_20 tripleBlock_6_part_24))))))
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
private theorem tripleEnt_7_part_120 : (List.range' 120 5).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7 : (List.range' 0 125).all (fun k => entCheck 7 k && s8Check 7 k) = true := by
  exact (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 0 8 117 tripleEnt_7_part_0 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 8 8 109 tripleEnt_7_part_8 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 16 8 101 tripleEnt_7_part_16 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 24 8 93 tripleEnt_7_part_24 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 32 8 85 tripleEnt_7_part_32 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 40 8 77 tripleEnt_7_part_40 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 48 8 69 tripleEnt_7_part_48 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 56 8 61 tripleEnt_7_part_56 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 64 8 53 tripleEnt_7_part_64 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 72 8 45 tripleEnt_7_part_72 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 80 8 37 tripleEnt_7_part_80 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 88 8 29 tripleEnt_7_part_88 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 96 8 21 tripleEnt_7_part_96 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 104 8 13 tripleEnt_7_part_104 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 112 8 5 tripleEnt_7_part_112 tripleEnt_7_part_120)))))))))))))))
private theorem tripleBlock_7_part_0 : (List.range' 0 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_4 : (List.range' 4 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_8 : (List.range' 8 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_12 : (List.range' 12 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_16 : (List.range' 16 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_20 : (List.range' 20 4).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7_part_24 : (List.range' 24 1).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by decide +kernel
private theorem tripleBlock_7 : (List.range' 0 25).all (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 0 4 21 tripleBlock_7_part_0 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 4 4 17 tripleBlock_7_part_4 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 8 4 13 tripleBlock_7_part_8 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 12 4 9 tripleBlock_7_part_12 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 16 4 5 tripleBlock_7_part_16 (@check_range_add (fun x => blockCheck 7 (x / (mx 7 + 1)) (x % (mx 7 + 1))) 20 4 1 tripleBlock_7_part_20 tripleBlock_7_part_24))))))
theorem tripleCheck_7 : tripleCheck 7=true := by
  exact @tripleCheck_join 7 tripleEnt_7 tripleBlock_7
end SigGolfCandidate.T3M.Nonbinary
end
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
private theorem tripleEnt_8_part_120 : (List.range' 120 5).all (fun k => entCheck 8 k && s8Check 8 k) = true := by decide +kernel
private theorem tripleEnt_8 : (List.range' 0 125).all (fun k => entCheck 8 k && s8Check 8 k) = true := by
  exact (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 0 8 117 tripleEnt_8_part_0 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 8 8 109 tripleEnt_8_part_8 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 16 8 101 tripleEnt_8_part_16 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 24 8 93 tripleEnt_8_part_24 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 32 8 85 tripleEnt_8_part_32 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 40 8 77 tripleEnt_8_part_40 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 48 8 69 tripleEnt_8_part_48 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 56 8 61 tripleEnt_8_part_56 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 64 8 53 tripleEnt_8_part_64 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 72 8 45 tripleEnt_8_part_72 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 80 8 37 tripleEnt_8_part_80 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 88 8 29 tripleEnt_8_part_88 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 96 8 21 tripleEnt_8_part_96 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 104 8 13 tripleEnt_8_part_104 (@check_range_add (fun k => entCheck 8 k && s8Check 8 k) 112 8 5 tripleEnt_8_part_112 tripleEnt_8_part_120)))))))))))))))
private theorem tripleBlock_8_part_0 : (List.range' 0 4).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by decide +kernel
private theorem tripleBlock_8_part_4 : (List.range' 4 4).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by decide +kernel
private theorem tripleBlock_8_part_8 : (List.range' 8 4).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by decide +kernel
private theorem tripleBlock_8_part_12 : (List.range' 12 4).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by decide +kernel
private theorem tripleBlock_8_part_16 : (List.range' 16 4).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by decide +kernel
private theorem tripleBlock_8_part_20 : (List.range' 20 4).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by decide +kernel
private theorem tripleBlock_8_part_24 : (List.range' 24 1).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by decide +kernel
private theorem tripleBlock_8 : (List.range' 0 25).all (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) 0 4 21 tripleBlock_8_part_0 (@check_range_add (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) 4 4 17 tripleBlock_8_part_4 (@check_range_add (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) 8 4 13 tripleBlock_8_part_8 (@check_range_add (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) 12 4 9 tripleBlock_8_part_12 (@check_range_add (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) 16 4 5 tripleBlock_8_part_16 (@check_range_add (fun x => blockCheck 8 (x / (mx 8 + 1)) (x % (mx 8 + 1))) 20 4 1 tripleBlock_8_part_20 tripleBlock_8_part_24))))))
theorem tripleCheck_8 : tripleCheck 8=true := by
  exact @tripleCheck_join 8 tripleEnt_8 tripleBlock_8
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_9_part_0 : (List.range' 0 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_8 : (List.range' 8 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_16 : (List.range' 16 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_24 : (List.range' 24 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_32 : (List.range' 32 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_40 : (List.range' 40 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_48 : (List.range' 48 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_56 : (List.range' 56 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_64 : (List.range' 64 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_72 : (List.range' 72 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_80 : (List.range' 80 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_88 : (List.range' 88 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_96 : (List.range' 96 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_104 : (List.range' 104 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_112 : (List.range' 112 8).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9_part_120 : (List.range' 120 5).all (fun k => entCheck 9 k && s8Check 9 k) = true := by decide +kernel
private theorem tripleEnt_9 : (List.range' 0 125).all (fun k => entCheck 9 k && s8Check 9 k) = true := by
  exact (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 0 8 117 tripleEnt_9_part_0 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 8 8 109 tripleEnt_9_part_8 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 16 8 101 tripleEnt_9_part_16 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 24 8 93 tripleEnt_9_part_24 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 32 8 85 tripleEnt_9_part_32 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 40 8 77 tripleEnt_9_part_40 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 48 8 69 tripleEnt_9_part_48 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 56 8 61 tripleEnt_9_part_56 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 64 8 53 tripleEnt_9_part_64 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 72 8 45 tripleEnt_9_part_72 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 80 8 37 tripleEnt_9_part_80 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 88 8 29 tripleEnt_9_part_88 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 96 8 21 tripleEnt_9_part_96 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 104 8 13 tripleEnt_9_part_104 (@check_range_add (fun k => entCheck 9 k && s8Check 9 k) 112 8 5 tripleEnt_9_part_112 tripleEnt_9_part_120)))))))))))))))
private theorem tripleBlock_9_part_0 : (List.range' 0 4).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by decide +kernel
private theorem tripleBlock_9_part_4 : (List.range' 4 4).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by decide +kernel
private theorem tripleBlock_9_part_8 : (List.range' 8 4).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by decide +kernel
private theorem tripleBlock_9_part_12 : (List.range' 12 4).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by decide +kernel
private theorem tripleBlock_9_part_16 : (List.range' 16 4).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by decide +kernel
private theorem tripleBlock_9_part_20 : (List.range' 20 4).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by decide +kernel
private theorem tripleBlock_9_part_24 : (List.range' 24 1).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by decide +kernel
private theorem tripleBlock_9 : (List.range' 0 25).all (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) 0 4 21 tripleBlock_9_part_0 (@check_range_add (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) 4 4 17 tripleBlock_9_part_4 (@check_range_add (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) 8 4 13 tripleBlock_9_part_8 (@check_range_add (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) 12 4 9 tripleBlock_9_part_12 (@check_range_add (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) 16 4 5 tripleBlock_9_part_16 (@check_range_add (fun x => blockCheck 9 (x / (mx 9 + 1)) (x % (mx 9 + 1))) 20 4 1 tripleBlock_9_part_20 tripleBlock_9_part_24))))))
theorem tripleCheck_9 : tripleCheck 9=true := by
  exact @tripleCheck_join 9 tripleEnt_9 tripleBlock_9
end SigGolfCandidate.T3M.Nonbinary
end
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
private theorem tripleBlock_10_part_0 : (List.range' 0 4).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by decide +kernel
private theorem tripleBlock_10_part_4 : (List.range' 4 4).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by decide +kernel
private theorem tripleBlock_10_part_8 : (List.range' 8 4).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by decide +kernel
private theorem tripleBlock_10_part_12 : (List.range' 12 4).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by decide +kernel
private theorem tripleBlock_10_part_16 : (List.range' 16 4).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by decide +kernel
private theorem tripleBlock_10_part_20 : (List.range' 20 4).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by decide +kernel
private theorem tripleBlock_10_part_24 : (List.range' 24 1).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by decide +kernel
private theorem tripleBlock_10 : (List.range' 0 25).all (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) 0 4 21 tripleBlock_10_part_0 (@check_range_add (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) 4 4 17 tripleBlock_10_part_4 (@check_range_add (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) 8 4 13 tripleBlock_10_part_8 (@check_range_add (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) 12 4 9 tripleBlock_10_part_12 (@check_range_add (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) 16 4 5 tripleBlock_10_part_16 (@check_range_add (fun x => blockCheck 10 (x / (mx 10 + 1)) (x % (mx 10 + 1))) 20 4 1 tripleBlock_10_part_20 tripleBlock_10_part_24))))))
theorem tripleCheck_10 : tripleCheck 10=true := by
  exact @tripleCheck_join 10 tripleEnt_10 tripleBlock_10
end SigGolfCandidate.T3M.Nonbinary
end
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
private theorem tripleBlock_11_part_0 : (List.range' 0 4).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by decide +kernel
private theorem tripleBlock_11_part_4 : (List.range' 4 4).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by decide +kernel
private theorem tripleBlock_11_part_8 : (List.range' 8 4).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by decide +kernel
private theorem tripleBlock_11_part_12 : (List.range' 12 4).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by decide +kernel
private theorem tripleBlock_11_part_16 : (List.range' 16 4).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by decide +kernel
private theorem tripleBlock_11_part_20 : (List.range' 20 4).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by decide +kernel
private theorem tripleBlock_11_part_24 : (List.range' 24 1).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by decide +kernel
private theorem tripleBlock_11 : (List.range' 0 25).all (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) 0 4 21 tripleBlock_11_part_0 (@check_range_add (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) 4 4 17 tripleBlock_11_part_4 (@check_range_add (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) 8 4 13 tripleBlock_11_part_8 (@check_range_add (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) 12 4 9 tripleBlock_11_part_12 (@check_range_add (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) 16 4 5 tripleBlock_11_part_16 (@check_range_add (fun x => blockCheck 11 (x / (mx 11 + 1)) (x % (mx 11 + 1))) 20 4 1 tripleBlock_11_part_20 tripleBlock_11_part_24))))))
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
private theorem tripleBlock_12_part_0 : (List.range' 0 4).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by decide +kernel
private theorem tripleBlock_12_part_4 : (List.range' 4 4).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by decide +kernel
private theorem tripleBlock_12_part_8 : (List.range' 8 4).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by decide +kernel
private theorem tripleBlock_12_part_12 : (List.range' 12 4).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by decide +kernel
private theorem tripleBlock_12_part_16 : (List.range' 16 4).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by decide +kernel
private theorem tripleBlock_12_part_20 : (List.range' 20 4).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by decide +kernel
private theorem tripleBlock_12_part_24 : (List.range' 24 1).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by decide +kernel
private theorem tripleBlock_12 : (List.range' 0 25).all (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) = true := by
  exact (@check_range_add (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) 0 4 21 tripleBlock_12_part_0 (@check_range_add (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) 4 4 17 tripleBlock_12_part_4 (@check_range_add (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) 8 4 13 tripleBlock_12_part_8 (@check_range_add (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) 12 4 9 tripleBlock_12_part_12 (@check_range_add (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) 16 4 5 tripleBlock_12_part_16 (@check_range_add (fun x => blockCheck 12 (x / (mx 12 + 1)) (x % (mx 12 + 1))) 20 4 1 tripleBlock_12_part_20 tripleBlock_12_part_24))))))
theorem tripleCheck_12 : tripleCheck 12=true := by
  exact @tripleCheck_join 12 tripleEnt_12 tripleBlock_12
end SigGolfCandidate.T3M.Nonbinary
end
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
private theorem inlineBatch_13_25_part_25 : (List.range' 25 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_30 : (List.range' 30 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_35 : (List.range' 35 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_40 : (List.range' 40 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25_part_45 : (List.range' 45 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_25 : (List.range' 25 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 25 5 20 inlineBatch_13_25_part_25 (@check_range_add (inlineCheck 13) 30 5 15 inlineBatch_13_25_part_30 (@check_range_add (inlineCheck 13) 35 5 10 inlineBatch_13_25_part_35 (@check_range_add (inlineCheck 13) 40 5 5 inlineBatch_13_25_part_40 inlineBatch_13_25_part_45))))
theorem inlineGroupCheck_13_25 : inlineGroupCheck 13 25 25=true := by
  exact inlineBatch_13_25
private theorem inlineBatch_13_50_part_50 : (List.range' 50 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_55 : (List.range' 55 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_60 : (List.range' 60 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_65 : (List.range' 65 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50_part_70 : (List.range' 70 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_50 : (List.range' 50 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 50 5 20 inlineBatch_13_50_part_50 (@check_range_add (inlineCheck 13) 55 5 15 inlineBatch_13_50_part_55 (@check_range_add (inlineCheck 13) 60 5 10 inlineBatch_13_50_part_60 (@check_range_add (inlineCheck 13) 65 5 5 inlineBatch_13_50_part_65 inlineBatch_13_50_part_70))))
theorem inlineGroupCheck_13_50 : inlineGroupCheck 13 50 25=true := by
  exact inlineBatch_13_50
private theorem inlineBatch_13_75_part_75 : (List.range' 75 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_80 : (List.range' 80 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_85 : (List.range' 85 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_90 : (List.range' 90 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75_part_95 : (List.range' 95 5).all (inlineCheck 13) = true := by decide +kernel
private theorem inlineBatch_13_75 : (List.range' 75 25).all (inlineCheck 13) = true := by
  exact (@check_range_add (inlineCheck 13) 75 5 20 inlineBatch_13_75_part_75 (@check_range_add (inlineCheck 13) 80 5 15 inlineBatch_13_75_part_80 (@check_range_add (inlineCheck 13) 85 5 10 inlineBatch_13_75_part_85 (@check_range_add (inlineCheck 13) 90 5 5 inlineBatch_13_75_part_90 inlineBatch_13_75_part_95))))
theorem inlineGroupCheck_13_75 : inlineGroupCheck 13 75 25=true := by
  exact inlineBatch_13_75
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
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem inlineBatch_16_0_part_0 : (List.range' 0 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_5 : (List.range' 5 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_10 : (List.range' 10 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_15 : (List.range' 15 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0_part_20 : (List.range' 20 5).all (inlineCheck 16) = true := by decide +kernel
private theorem inlineBatch_16_0 : (List.range' 0 25).all (inlineCheck 16) = true := by
  exact (@check_range_add (inlineCheck 16) 0 5 20 inlineBatch_16_0_part_0 (@check_range_add (inlineCheck 16) 5 5 15 inlineBatch_16_0_part_5 (@check_range_add (inlineCheck 16) 10 5 10 inlineBatch_16_0_part_10 (@check_range_add (inlineCheck 16) 15 5 5 inlineBatch_16_0_part_15 inlineBatch_16_0_part_20))))
theorem inlineGroupCheck_16_0 : inlineGroupCheck 16 0 25=true := by
  exact inlineBatch_16_0
end SigGolfCandidate.T3M.Nonbinary
end
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
section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
theorem tripleCheck_at (q : Nat) (hq : q<18) (hn : inl q=false) : tripleCheck q=true := by
  interval_cases q
  all_goals first | (simp [inl] at hn) | skip
  exacts [tripleCheck_0, tripleCheck_1, tripleCheck_2, tripleCheck_3, tripleCheck_4, tripleCheck_5,
    tripleCheck_6, tripleCheck_7, tripleCheck_8, tripleCheck_9, tripleCheck_10, tripleCheck_11, tripleCheck_12,
    tripleCheck_17]
theorem inlineGroupCheck_at (q : Nat) (hq : inl q=true) :
    inlineGroupCheck q 0 25=true ∧ inlineGroupCheck q 25 25=true ∧ inlineGroupCheck q 50 25=true ∧
      inlineGroupCheck q 75 25=true ∧ inlineGroupCheck q 100 25=true := by
  have h : q=13 ∨ q=14 ∨ q=15 ∨ q=16 := by simp [inl] at hq; omega
  rcases h with rfl|rfl|rfl|rfl
  · exact ⟨inlineGroupCheck_13_0,inlineGroupCheck_13_25,inlineGroupCheck_13_50,inlineGroupCheck_13_75,inlineGroupCheck_13_100⟩
  · exact ⟨inlineGroupCheck_14_0,inlineGroupCheck_14_25,inlineGroupCheck_14_50,inlineGroupCheck_14_75,
      inlineGroupCheck_14_100⟩
  · exact ⟨inlineGroupCheck_15_0,inlineGroupCheck_15_25,inlineGroupCheck_15_50,inlineGroupCheck_15_75,
      inlineGroupCheck_15_100⟩
  · exact ⟨inlineGroupCheck_16_0,inlineGroupCheck_16_25,inlineGroupCheck_16_50,inlineGroupCheck_16_75,
      inlineGroupCheck_16_100⟩
theorem inlineCheck_at (q k : Nat) (hq : inl q=true) (hk : k<125) : inlineCheck q k=true := by
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
theorem entCheck_at (q k : Nat) (hq : q<18) (hn : inl q=false) (hk : k<(mx q+1)^3) : entCheck q k=true := by
  have h := tripleCheck_at q hq hn
  simp only [tripleCheck,Bool.and_eq_true] at h
  exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).1
theorem mx_inl (q : Nat) (hq : inl q=true) : mx q=4 := by
  simp [inl] at hq; unfold mx; rw [if_pos (by omega)]
theorem s8Check_at (q k : Nat) (hq : q<18) (hk : k<(mx q+1)^3) : s8Check q k=true := by
  cases hn : inl q
  · have h := tripleCheck_at q hq hn
    simp only [tripleCheck,Bool.and_eq_true] at h
    exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).2
  · have hm := mx_inl q hn
    rw [hm] at hk
    have h := inlineCheck_at q k hn (by norm_num at hk; omega)
    simp only [inlineCheck,Bool.and_eq_true] at h
    exact h.1.1.1.1
theorem blockCheck_at (q dB dC : Nat) (hq : q<18) (hn : inl q=false) (hB : dB ≤ mx q) (hC : dC ≤ mx q) :
    blockCheck q dB dC=true := by
  have h := tripleCheck_at q hq hn
  simp only [tripleCheck,Bool.and_eq_true] at h
  have hh : (mx q+1)*dB+dC<(mx q+1)^2 := by
    unfold mx at *
    split_ifs at * <;> nlinarith
  have e1 : ((mx q+1)*dB+dC)/(mx q+1)=dB := by
    unfold mx at *
    split_ifs at * <;> omega
  have e2 : ((mx q+1)*dB+dC)%(mx q+1)=dC := by
    unfold mx at *
    split_ifs at * <;> omega
  have hb := List.all_eq_true.mp h.2 ((mx q+1)*dB+dC) (List.mem_range.mpr hh)
  rwa [e1,e2] at hb
theorem stub_at (k : Nat) (hk : k<125) : vrun (guardW k) 1=some rejJ := by
  have h := rejCheck_ok
  simp only [rejCheck] at h
  exact rOK_eq (List.all_eq_true.mp h k (List.mem_range.mpr hk))
theorem s8Run_at (q k : Nat) (hq : q<18) (hk : k<(mx q+1)^3) :
    (if q=0 then rOK (vrun (entW 0 k) 3) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k)))=true := by
  have h := s8Check_at q k hq hk
  simp only [s8Check,Bool.and_eq_true] at h
  exact h.1
theorem bge9_at (k : Nat) (hk : k<125) (he : k%2=0) : vrun (cellW 9 k) 1=some (bge9R (cellW 9 k)) := by
  have h := s8Check_at 9 k (by decide +kernel) (by unfold mx; norm_num; omega)
  simp only [s8Check,Bool.and_eq_true] at h
  have h2 := h.2
  rw [if_pos (by simp [he])] at h2
  exact rOK_eq h2
end SigGolfCandidate.T3M.Nonbinary
end
end

section


section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
theorem gbase_noninl (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) (hn : inl q=false) :
    gbase q (c.kOf q)=base q (c.dig (3*q+1)) (c.dig (3*q+2)) := by
  obtain ⟨-,k2,k3⟩ := c.kdig_kOf hd q hq
  simp only [gbase,hn,Bool.false_eq_true,if_false,k2,k3]
theorem gB_noninl (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) (hn : inl q=false) :
    gB q (c.kOf q)=pcB q (c.dig (3*q+1)) (c.dig (3*q+2)) := by
  simp only [gB,pcB,c.gbase_noninl hd q hq hn]
theorem gC_eq (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    gC q (c.kOf q)=gB q (c.kOf q)+partLen q (c.dig (3*q+1)) := by
  obtain ⟨-,k2,-⟩ := c.kdig_kOf hd q hq
  simp only [gC,k2]
theorem gX_eq (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    gX q (c.kOf q)=gC q (c.kOf q)+partLen q (c.dig (3*q+2)) := by
  obtain ⟨-,-,k3⟩ := c.kdig_kOf hd q hq
  simp only [gX,k3]
structure GroupFacts (c : NCtx) (q : Nat) : Prop where
  copyJ : inl q=false → c.dig (3*q)=mx q →
    vrun (leadPc q (c.kOf q)) 7=some (copyN .x8 (off (3*q)) (slot (3*q)) (gB q (c.kOf q)))
  headJ : inl q=false → c.dig (3*q)+1< mx q →
    vrun (leadPc q (c.kOf q)) 7=some (headJD .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  headJT : inl q=false → c.dig (3*q)+1=mx q →
    vrun (leadPc q (c.kOf q)) 7=
      some (headJDTerm .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  copyF : inl q=true → c.dig (3*q)=mx q →
    vrun (leadPc q (c.kOf q)) 4=some (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q (c.kOf q)))
  headF : inl q=true → c.dig (3*q)+1< mx q →
    vrun (leadPc q (c.kOf q)) 4=some (headJDF .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  headFT : inl q=true → c.dig (3*q)+1=mx q →
    vrun (leadPc q (c.kOf q)) 3=
      some (headJDTermF .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  tail : c.dig (3*q)< mx q →
    vrun (gbase q (c.kOf q)+2*c.dig (3*q)+1) 2=
      some (tailR (if c.dig (3*q)+1=mx q then some (slot (3*q)) else none) (gbase q (c.kOf q)+2*c.dig (3*q)+1))
  rungs : rungsOK q (c.dig (3*q)+1) (slot (3*q)) (gbase q (c.kOf q)+2*(c.dig (3*q)+1))=true
  partB : partOK q (3*q+1) (c.dig (3*q+1)) (gB q (c.kOf q))=true
  partC : partOK q (3*q+2) (c.dig (3*q+2)) (gC q (c.kOf q))=true
  disp : q<17 → vrun (gX q (c.kOf q)) 5=some (if q=8 then dispatch9R else if q<16 then dispatchR (q+1) else tailDispatchR)
  s8 : s8Check q (c.kOf q)=true
theorem mx_bounds' (q : Nat) : 3≤ mx q ∧ mx q≤4 := by unfold mx;split <;> omega
theorem rungsOK_mono (q d0 d1 sl b : Nat) (h : d0 ≤ d1) (hk : rungsOK q d0 sl (b+2*d0)=true) :
    rungsOK q d1 sl (b+2*d1)=true := by
  unfold rungsOK at hk ⊢
  rw [List.all_eq_true] at hk ⊢
  intro m hm
  rw [List.mem_range'_1] at hm
  have := hk m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
  rwa [show b+2*d0+2*(m-d0)=b+2*d1+2*(m-d1) by omega] at this
theorem groupFacts (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<18) : c.GroupFacts q := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q hq
  have hk := c.kOf_lt hds q hq
  have hA := c.dig_group_le hds q 0 hq (by decide +kernel)
  simp only [Nat.add_zero] at hA
  have hB := c.dig_group_le hds q 1 hq (by decide +kernel)
  have hC := c.dig_group_le hds q 2 hq (by decide +kernel)
  have hm := mx_bounds' q
  cases hn : inl q
  · have he := entCheck_at q (c.kOf q) hq hn hk
    have hb := blockCheck_at q _ _ hq hn hB hC
    simp only [entCheck,k1] at he
    simp only [blockCheck,dispatchOK,Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨htails,hrungs⟩,hpB⟩,hpC⟩,hdisp⟩ := hb
    have eB := c.gB_noninl hds q hq hn
    have eb := c.gbase_noninl hds q hq hn
    have eC : gC q (c.kOf q)=pcC q (c.dig (3*q+1)) (c.dig (3*q+2)) := by rw [c.gC_eq hds q hq,eB]; rfl
    have eX : gX q (c.kOf q)=pcX q (c.dig (3*q+1)) (c.dig (3*q+2)) := by rw [c.gX_eq hds q hq,eC]; rfl
    refine ⟨fun _ hd => ?_,fun _ hd => ?_,fun _ hd => ?_,fun h => by simp [hn] at h,fun h => by simp [hn] at h,
      fun h => by simp [hn] at h,fun hd => ?_,?_,?_,?_,?_,s8Check_at q _ hq hk⟩
    · rw [if_pos hd] at he; exact rOK_eq he
    · rw [if_neg (by omega),if_neg (by omega)] at he; exact rOK_eq he
    · rw [if_neg (by omega),if_pos hd] at he; exact rOK_eq he
    · have h := List.all_eq_true.mp htails (c.dig (3*q)) (List.mem_range.mpr hd)
      rw [eb]; simpa only [Nat.add_assoc] using rOK_eq h
    · rw [eb]
      have h0 : rungsOK q 0 (slot (3*q)) (base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*0)=true := by simpa using hrungs
      exact rungsOK_mono q 0 _ _ _ (by omega) h0
    · rw [eB]; exact hpB
    · rw [eC]; exact hpC
    · intro hq17; rw [eX]; rw [if_pos hq17] at hdisp; exact rOK_eq hdisp
  · have hm4 := mx_inl q hn
    rw [hm4] at hk
    have he := inlineCheck_at q (c.kOf q) hn (by norm_num at hk; omega)
    have hq16 : 13 ≤ q ∧ q ≤ 16 := by simp [inl] at hn; omega
    simp only [inlineCheck,k1,k2,k3] at he
    by_cases hd : c.dig (3*q)=mx q
    · rw [if_pos hd] at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨⟨⟨⟨hs8,hcopy⟩,hpB⟩,hpC⟩,hdisp⟩ := he
      refine ⟨fun h => by simp [hn] at h,fun h => by simp [hn] at h,fun h => by simp [hn] at h,
        fun _ _ => rOK_eq hcopy,fun _ h => absurd h (by omega),fun _ h => absurd h (by omega),
        fun h => absurd h (by omega),?_,hpB,hpC,fun _ => by rw [if_neg (show q≠8 by omega)]; exact rOK_eq hdisp,hs8⟩
      unfold rungsOK; rw [List.all_eq_true]; intro m hm'; rw [List.mem_range'_1] at hm'; omega
    · rw [if_neg hd] at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨⟨⟨⟨hs8,⟨⟨hhead,htail⟩,hrungs⟩⟩,hpB⟩,hpC⟩,hdisp⟩ := he
      refine ⟨fun h => by simp [hn] at h,fun h => by simp [hn] at h,fun h => by simp [hn] at h,
        fun _ h => absurd h hd,fun _ h => ?_,fun _ h => ?_,fun _ => rOK_eq htail,hrungs,hpB,hpC,
        fun _ => by rw [if_neg (show q≠8 by omega)]; exact rOK_eq hdisp,hs8⟩
      · rw [if_neg (by omega)] at hhead; simpa only [if_neg (show ¬ c.dig (3*q)+1=mx q by omega)] using rOK_eq hhead
      · rw [if_pos h] at hhead; simpa only [if_pos h] using rOK_eq hhead
theorem kOf_eq_lead (c : NCtx) (i : Nat) (h0 : i%3=0) : 3*(i/3)=i := by omega
theorem chk_headJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hn : inl (i/3)=false) (hd : c.dig i< last i) :
    vrun (c.startPc i) 7=some (headJD .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).headJ hn (by simpa only [last,topMax,eq] using (show c.dig (3*q)+1<topMax (3*q) by unfold last at hd; omega))
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq]
  rw [hs,hr]; exact hf
theorem chk_headJTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hn : inl (i/3)=false) (hd : c.dig i=last i) :
    vrun (c.startPc i) 7=some (headJDTerm .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hm := topMax_bounds (3*q)
  have hf := (c.groupFacts hds q (by omega)).headJT hn (by simp only [last,topMax,eq] at hd hm; omega)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq]
  rw [hs,hr]; exact hf
theorem chk_copyJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hn : inl (i/3)=false) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 7=some (copyN .x8 (off i) (slot i) (c.endPc i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).copyJ hn (by simpa only [topMax,eq] using hd)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq]
  have he : c.endPc (3*q)=gB q (c.kOf q) := by simp [endPc,qB,eq]
  rw [hs,he]; exact hf
theorem chk_headJF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hn : inl (i/3)=true) (hd : c.dig i< last i) :
    vrun (c.startPc i) 4=some (headJDF .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).headF hn (by simpa only [last,topMax,eq] using (show c.dig (3*q)+1<topMax (3*q) by unfold last at hd; omega))
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq]
  rw [hs,hr]; exact hf
theorem chk_headJTermF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hn : inl (i/3)=true) (hd : c.dig i=last i) :
    vrun (c.startPc i) 3=some (headJDTermF .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hm := topMax_bounds (3*q)
  have hf := (c.groupFacts hds q (by omega)).headFT hn (by simp only [last,topMax,eq] at hd hm; omega)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq]
  rw [hs,hr]; exact hf
theorem chk_copyFL (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hn : inl (i/3)=true) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 4=some (copyFH .x8 (off i) (slot i) (c.startPc i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).copyF hn (by simpa only [topMax,eq] using hd)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq]
  rw [hs]; exact hf
theorem part_at (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) (h0 : i%3≠0) :
    partOK (i/3) i (c.dig i) (c.startPc i)=true := by
  obtain ⟨q,r,rfl,hr⟩ : ∃q r,i=3*q+r ∧ r<3 := ⟨i/3,i%3,by omega,by omega⟩
  have eq : (3*q+r)/3=q := by omega
  have hf := c.groupFacts hds q (by omega)
  unfold startPc qB qC
  rw [if_neg h0,eq]
  rcases (show r=1 ∨ r=2 by omega) with rfl|rfl
  · rw [if_pos (by omega)];exact hf.partB
  · rw [if_neg (by omega)];exact hf.partC
theorem chk_headR (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i< last i) :
    vrun (c.startPc i) 8=some (headRH .x8 (off i) (c.dig i) none (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i< mx (i/3)-1 := hd
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_neg (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_headRTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=last i) :
    vrun (c.startPc i) 8=some (headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i=mx (i/3)-1 := hd
  have hm : 3≤ mx (i/3) := (topMax_bounds i).1
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_pos (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_copyF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 4=some (copyFH .x8 (off i) (slot i) (c.startPc i)) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  change c.dig i=mx (i/3) at hd
  rw [if_pos hd] at hp
  exact rOK_eq hp
theorem chk_rung (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<54)
    (hm : c.dig i< m) (hm2 : m ≤ last i) :
    vrun (c.rungPc i m) 3=some (rungR m (if m=last i then some (slot i) else none) (c.rungPc i m)) := by
  have hmx := topMax_bounds i
  by_cases h0 : i%3=0
  · obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
    have eq : 3*q/3=q := by omega
    have hf := c.groupFacts hds q (by omega)
    have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
    have hh := List.all_eq_true.mp hf.rungs m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc (3*q) m=gbase q (c.kOf q)+2*(c.dig (3*q)+1)+2*(m-(c.dig (3*q)+1)) := by
      simp [rungPc,qb,eq]; omega
    have ht : (m+1=mx q) ↔ m=last (3*q) := by unfold last topMax;rw [eq];omega
    simpa only [rungsOK,hr,ht] using rOK_eq hh
  · have hp := c.part_at hds i hi h0
    have hn : c.dig i< mx (i/3) := by change c.dig i< topMax i;unfold last at hm2;omega
    unfold partOK at hp
    rw [if_neg (by omega),Bool.and_eq_true] at hp
    have hmmax : m< mx (i/3) := by change m<topMax i;unfold last at hm2;omega
    have hh := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc i m=c.startPc i+5+2*(m-(c.dig i+1)) := by
      unfold rungPc
      rw [if_neg h0,if_neg (by omega)]
      omega
    have ht : (m+1=mx (i/3)) ↔ m=last i := by unfold last topMax;omega
    simpa only [hr,ht] using rOK_eq hh
theorem chk_tail (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) (h0 : i%3=0) (hd : c.dig i<topMax i) :
    vrun (c.rungPc i (c.dig i)+1) 2=
      some (tailR (if c.dig i=last i then some (slot i) else none) (c.rungPc i (c.dig i)+1)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have hf := c.groupFacts hds q (by omega)
  have hmx := mx_bounds' q
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq]
  have ht : (c.dig (3*q)+1=mx q) ↔ c.dig (3*q)=last (3*q) := by unfold last topMax;rw [eq];omega
  have h := hf.tail (by simpa only [topMax,eq] using hd)
  rw [hr]
  simpa only [ht] using h
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
end
