import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart0
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart1
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart2
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart3
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart4
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart5
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart6
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart7
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart8
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart9
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart10

section

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
/-- R6: the r5 groups' (8 <= q < 17) invalid ranks 125 / 126 land on zero words. -/
theorem fault_top_word (q : Nat) (hq : q<17) (h8 : 8≤q) : (lcode (entOff q)).head?=some 0 := by
  interval_cases q <;> decide +kernel
theorem fault_top126_word (q : Nat) (hq : q<17) (h8 : 8≤q) (he : 1024≤entOff q) :
    (lcode (entOff q-1024)).head?=some 0 := by
  interval_cases q <;> first | (norm_num [entOff] at he; done) | decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
theorem tripleCheck_at (q : Nat) (hq : q<17) (hn : inl q=false) : tripleCheck q=true := by
  interval_cases q
  all_goals first | (simp [inl] at hn) | skip
  exacts [tripleCheck_0, tripleCheck_1, tripleCheck_2, tripleCheck_3, tripleCheck_4, tripleCheck_5,
    tripleCheck_6, tripleCheck_7, tripleCheck_8, tripleCheck_10, tripleCheck_11, tripleCheck_12]
theorem inlineGroupCheck_at (q : Nat) (hq : inl q=true) :
    inlineGroupCheck q 0 25=true ∧ inlineGroupCheck q 25 25=true ∧ inlineGroupCheck q 50 25=true ∧
      inlineGroupCheck q 75 25=true ∧ inlineGroupCheck q 100 25=true := by
  have h : q=9 ∨ q=13 ∨ q=14 ∨ q=15 ∨ q=16 := by simp [inl] at hq; omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact ⟨inlineGroupCheck_9_0,inlineGroupCheck_9_25,inlineGroupCheck_9_50,inlineGroupCheck_9_75,inlineGroupCheck_9_100⟩
  · exact ⟨inlineGroupCheck_13_0,inlineGroupCheck_13_25,inlineGroupCheck_13_50,inlineGroupCheck_13_75,inlineGroupCheck_13_100⟩
  · exact ⟨inlineGroupCheck_14_0,inlineGroupCheck_14_25,inlineGroupCheck_14_50,inlineGroupCheck_14_75,
      inlineGroupCheck_14_100⟩
  · exact ⟨inlineGroupCheck_15_0,inlineGroupCheck_15_25,inlineGroupCheck_15_50,inlineGroupCheck_15_75,
      inlineGroupCheck_15_100⟩
  · exact ⟨inlineGroupCheck_16_0,inlineGroupCheck_16_25,inlineGroupCheck_16_50,inlineGroupCheck_16_75,
      inlineGroupCheck_16_100⟩
theorem inlineCheck_static_at (q k : Nat) (hq : inl q=true) (hk : k<125) : inlineCheck q k=true := by
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
theorem entCheck_at (q k : Nat) (hq : q<17) (hn : inl q=false) (hk : k<(mx q+1)^3) : entCheck q k=true := by
  have h := tripleCheck_at q hq hn
  simp only [tripleCheck,Bool.and_eq_true] at h
  exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).1
theorem static_false_of_row_false (q k : Nat) (h : rowInl q k=false) : inl q=false := by
  simp [rowInl, Bool.or_eq_false_iff] at h
  exact h.1
theorem rowInl_lt (q k : Nat) (h : rowInl q k=true) : q<17 := by
  simp [rowInl, inl] at h
  omega
theorem rowInl_ge (q k : Nat) (h : rowInl q k=true) : 8≤q := by
  simp [rowInl, inl] at h
  omega
theorem inlineCheck_at (q k : Nat) (hq : rowInl q k=true) (hk : k<125) : inlineCheck q k=true := by
  cases hn : inl q
  · have hq17 := rowInl_lt q k hq
    have h8 := rowInl_ge q k hq
    have h := entCheck_at q k hq17 hn (by simp [mx,hq17,show ¬ q<8 by omega]; omega)
    simpa only [entCheck,hq,if_true] using h
  · exact inlineCheck_static_at q k hn hk
theorem mx_inl (q : Nat) (hq : inl q=true) : mx q=4 := by
  simp [inl] at hq; unfold mx; rw [if_neg (by omega), if_pos (by omega)]
theorem mx_rowInl (q k : Nat) (hq : rowInl q k=true) : mx q=4 := by
  have h1 := rowInl_lt q k hq
  have h2 := rowInl_ge q k hq
  unfold mx; rw [if_neg (by omega), if_pos h1]
theorem s8Check_at (q k : Nat) (hq : q<17) (hk : k<(mx q+1)^3) : s8Check q k=true := by
  cases hn : inl q
  · have h := tripleCheck_at q hq hn
    simp only [tripleCheck,Bool.and_eq_true] at h
    exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).2
  · have hm := mx_inl q hn
    rw [hm] at hk
    have h := inlineCheck_static_at q k hn (by norm_num at hk; omega)
    simp only [inlineCheck,Bool.and_eq_true] at h
    exact h.1.1.1.1
theorem blockCheck_at (q dB dC : Nat) (hq : q<17) (hn : inl q=false) (hB : dB ≤ mx q) (hC : dC ≤ mx q) :
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
theorem s8Run_at (q k : Nat) (hq : q<17) (hk : k<(mx q+1)^3) :
    (if q=0 then rOK (vrun (entW 0 k) 1) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k)))=true := by
  have h := s8Check_at q k hq hk
  simp only [s8Check,Bool.and_eq_true] at h
  exact h.1
theorem bge9_at (k : Nat) (hk : k<125) (he : k%2=0) : vrun (cellW 9 k) 1=some (bge9R (cellW 9 k)) := by
  have h := s8Check_at 9 k (by decide +kernel) (by unfold mx; norm_num; omega)
  simp only [s8Check,Bool.and_eq_true] at h
  have h2 := h.2
  rw [if_pos (by simp [he])] at h2
  exact rOK_eq h2
/-! ### R6: guards, checksum landings and arms (Part4) -/
theorem guard6Check_at (g raw : Nat) (hg : g<8) (hr : raw<256) : guard6Check g raw=true := by
  have h : guard6All g=true := by
    interval_cases g
    exacts [guard6All_0, guard6All_1, guard6All_2, guard6All_3, guard6All_4, guard6All_5, guard6All_6, guard6All_7]
  exact List.all_eq_true.mp h raw (List.mem_range.mpr hr)
theorem ckGuardCheck_at (ds : Nat) (hd : ds<229) : ckGuardCheck ds=true :=
  List.all_eq_true.mp ckGuardAll_ok ds (List.mem_range.mpr hd)
theorem ckArmCheck_at (d : Nat) (hd : d<8) : ckArmCheck d=true :=
  List.all_eq_true.mp ckArmAll_ok d (List.mem_range.mpr hd)
end SigGolfCandidate.T3M.Nonbinary
end
end
