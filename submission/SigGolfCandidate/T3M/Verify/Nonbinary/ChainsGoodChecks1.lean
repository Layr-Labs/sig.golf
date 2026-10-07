import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecks0

set_option Elab.async false

section
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
end
