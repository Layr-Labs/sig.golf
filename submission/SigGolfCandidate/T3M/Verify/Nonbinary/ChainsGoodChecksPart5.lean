import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart4

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-! BIG74 (design D'): group 8 is an inline group with 250 entry indices `k = rank8 + 125 b63`; its checks replace
the old q8 triple checks. -/
private theorem i8_0 : (List.range' 0 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_5 : (List.range' 5 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_10 : (List.range' 10 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_15 : (List.range' 15 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_20 : (List.range' 20 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_25 : (List.range' 25 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_30 : (List.range' 30 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_35 : (List.range' 35 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_40 : (List.range' 40 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_45 : (List.range' 45 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_50 : (List.range' 50 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_55 : (List.range' 55 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_60 : (List.range' 60 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_65 : (List.range' 65 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_70 : (List.range' 70 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_75 : (List.range' 75 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_80 : (List.range' 80 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_85 : (List.range' 85 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_90 : (List.range' 90 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_95 : (List.range' 95 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_100 : (List.range' 100 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_105 : (List.range' 105 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_110 : (List.range' 110 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_115 : (List.range' 115 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_120 : (List.range' 120 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_125 : (List.range' 125 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_130 : (List.range' 130 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_135 : (List.range' 135 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_140 : (List.range' 140 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_145 : (List.range' 145 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_150 : (List.range' 150 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_155 : (List.range' 155 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_160 : (List.range' 160 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_165 : (List.range' 165 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_170 : (List.range' 170 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_175 : (List.range' 175 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_180 : (List.range' 180 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_185 : (List.range' 185 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_190 : (List.range' 190 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_195 : (List.range' 195 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_200 : (List.range' 200 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_205 : (List.range' 205 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_210 : (List.range' 210 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_215 : (List.range' 215 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_220 : (List.range' 220 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_225 : (List.range' 225 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_230 : (List.range' 230 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_235 : (List.range' 235 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_240 : (List.range' 240 5).all (inlineCheck 8) = true := by decide +kernel
private theorem i8_245 : (List.range' 245 5).all (inlineCheck 8) = true := by decide +kernel
theorem inlineGroupCheck_8_0 : inlineGroupCheck 8 0 25=true :=
  @check_range_add (inlineCheck 8) 0 5 20 i8_0 (@check_range_add (inlineCheck 8) 5 5 15 i8_5
    (@check_range_add (inlineCheck 8) 10 5 10 i8_10 (@check_range_add (inlineCheck 8) 15 5 5 i8_15 i8_20)))
theorem inlineGroupCheck_8_25 : inlineGroupCheck 8 25 25=true :=
  @check_range_add (inlineCheck 8) 25 5 20 i8_25 (@check_range_add (inlineCheck 8) 30 5 15 i8_30
    (@check_range_add (inlineCheck 8) 35 5 10 i8_35 (@check_range_add (inlineCheck 8) 40 5 5 i8_40 i8_45)))
theorem inlineGroupCheck_8_50 : inlineGroupCheck 8 50 25=true :=
  @check_range_add (inlineCheck 8) 50 5 20 i8_50 (@check_range_add (inlineCheck 8) 55 5 15 i8_55
    (@check_range_add (inlineCheck 8) 60 5 10 i8_60 (@check_range_add (inlineCheck 8) 65 5 5 i8_65 i8_70)))
theorem inlineGroupCheck_8_75 : inlineGroupCheck 8 75 25=true :=
  @check_range_add (inlineCheck 8) 75 5 20 i8_75 (@check_range_add (inlineCheck 8) 80 5 15 i8_80
    (@check_range_add (inlineCheck 8) 85 5 10 i8_85 (@check_range_add (inlineCheck 8) 90 5 5 i8_90 i8_95)))
theorem inlineGroupCheck_8_100 : inlineGroupCheck 8 100 25=true :=
  @check_range_add (inlineCheck 8) 100 5 20 i8_100 (@check_range_add (inlineCheck 8) 105 5 15 i8_105
    (@check_range_add (inlineCheck 8) 110 5 10 i8_110 (@check_range_add (inlineCheck 8) 115 5 5 i8_115 i8_120)))
theorem inlineGroupCheck_8_125 : inlineGroupCheck 8 125 25=true :=
  @check_range_add (inlineCheck 8) 125 5 20 i8_125 (@check_range_add (inlineCheck 8) 130 5 15 i8_130
    (@check_range_add (inlineCheck 8) 135 5 10 i8_135 (@check_range_add (inlineCheck 8) 140 5 5 i8_140 i8_145)))
theorem inlineGroupCheck_8_150 : inlineGroupCheck 8 150 25=true :=
  @check_range_add (inlineCheck 8) 150 5 20 i8_150 (@check_range_add (inlineCheck 8) 155 5 15 i8_155
    (@check_range_add (inlineCheck 8) 160 5 10 i8_160 (@check_range_add (inlineCheck 8) 165 5 5 i8_165 i8_170)))
theorem inlineGroupCheck_8_175 : inlineGroupCheck 8 175 25=true :=
  @check_range_add (inlineCheck 8) 175 5 20 i8_175 (@check_range_add (inlineCheck 8) 180 5 15 i8_180
    (@check_range_add (inlineCheck 8) 185 5 10 i8_185 (@check_range_add (inlineCheck 8) 190 5 5 i8_190 i8_195)))
theorem inlineGroupCheck_8_200 : inlineGroupCheck 8 200 25=true :=
  @check_range_add (inlineCheck 8) 200 5 20 i8_200 (@check_range_add (inlineCheck 8) 205 5 15 i8_205
    (@check_range_add (inlineCheck 8) 210 5 10 i8_210 (@check_range_add (inlineCheck 8) 215 5 5 i8_215 i8_220)))
theorem inlineGroupCheck_8_225 : inlineGroupCheck 8 225 25=true :=
  @check_range_add (inlineCheck 8) 225 5 20 i8_225 (@check_range_add (inlineCheck 8) 230 5 15 i8_230
    (@check_range_add (inlineCheck 8) 235 5 10 i8_235 (@check_range_add (inlineCheck 8) 240 5 5 i8_240 i8_245)))
/-- BIG74: the six group-8 slots with `rank8 ≥ 125` hold the fault stub. -/
theorem stub8Check_ok : stub8Check=true := by decide +kernel
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
theorem stub9Check_ok : stub9Check=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end
end
