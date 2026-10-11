import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart4

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
private theorem i9_0 : (List.range' 0 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_5 : (List.range' 5 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_10 : (List.range' 10 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_15 : (List.range' 15 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_20 : (List.range' 20 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_25 : (List.range' 25 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_30 : (List.range' 30 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_35 : (List.range' 35 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_40 : (List.range' 40 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_45 : (List.range' 45 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_50 : (List.range' 50 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_55 : (List.range' 55 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_60 : (List.range' 60 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_65 : (List.range' 65 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_70 : (List.range' 70 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_75 : (List.range' 75 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_80 : (List.range' 80 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_85 : (List.range' 85 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_90 : (List.range' 90 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_95 : (List.range' 95 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_100 : (List.range' 100 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_105 : (List.range' 105 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_110 : (List.range' 110 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_115 : (List.range' 115 5).all (inlineCheck 9) = true := by decide +kernel
private theorem i9_120 : (List.range' 120 5).all (inlineCheck 9) = true := by decide +kernel
theorem inlineGroupCheck_9_0 : inlineGroupCheck 9 0 25=true :=
  @check_range_add (inlineCheck 9) 0 5 20 i9_0 (@check_range_add (inlineCheck 9) 5 5 15 i9_5
    (@check_range_add (inlineCheck 9) 10 5 10 i9_10 (@check_range_add (inlineCheck 9) 15 5 5 i9_15 i9_20)))
theorem inlineGroupCheck_9_25 : inlineGroupCheck 9 25 25=true :=
  @check_range_add (inlineCheck 9) 25 5 20 i9_25 (@check_range_add (inlineCheck 9) 30 5 15 i9_30
    (@check_range_add (inlineCheck 9) 35 5 10 i9_35 (@check_range_add (inlineCheck 9) 40 5 5 i9_40 i9_45)))
theorem inlineGroupCheck_9_50 : inlineGroupCheck 9 50 25=true :=
  @check_range_add (inlineCheck 9) 50 5 20 i9_50 (@check_range_add (inlineCheck 9) 55 5 15 i9_55
    (@check_range_add (inlineCheck 9) 60 5 10 i9_60 (@check_range_add (inlineCheck 9) 65 5 5 i9_65 i9_70)))
theorem inlineGroupCheck_9_75 : inlineGroupCheck 9 75 25=true :=
  @check_range_add (inlineCheck 9) 75 5 20 i9_75 (@check_range_add (inlineCheck 9) 80 5 15 i9_80
    (@check_range_add (inlineCheck 9) 85 5 10 i9_85 (@check_range_add (inlineCheck 9) 90 5 5 i9_90 i9_95)))
theorem inlineGroupCheck_9_100 : inlineGroupCheck 9 100 25=true :=
  @check_range_add (inlineCheck 9) 100 5 20 i9_100 (@check_range_add (inlineCheck 9) 105 5 15 i9_105
    (@check_range_add (inlineCheck 9) 110 5 10 i9_110 (@check_range_add (inlineCheck 9) 115 5 5 i9_115 i9_120)))
end SigGolfCandidate.T3M.Nonbinary
end
end
