import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecks1

set_option Elab.async false

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
end
