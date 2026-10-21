import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart0
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart1
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart2
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart3
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart4
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart5
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart6
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart7
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart8
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart9
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart10

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-- T51: the r5 groups' (9 <= q < 16) invalid ranks 125 / 126 land on zero words (127: below the code). -/
theorem fault_top_word (q : Nat) (hq : q<16) (h9 : 9≤q) : (lcode (entOff q)).head?=some 0 := by
  interval_cases q <;> decide +kernel
theorem fault_top126_word (q : Nat) (hq : q<16) (h9 : 9≤q) (he : 1024≤entOff q) :
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
    tripleCheck_6, tripleCheck_7, tripleCheck_8, tripleCheck_10, tripleCheck_11, tripleCheck_12, tripleCheck_16]
theorem inlineGroupCheck_at (q : Nat) (hq : inl q=true) :
    inlineGroupCheck q 0 25=true ∧ inlineGroupCheck q 25 25=true ∧ inlineGroupCheck q 50 25=true ∧
      inlineGroupCheck q 75 25=true ∧ inlineGroupCheck q 100 25=true := by
  have h : q=9 ∨ q=13 ∨ q=14 ∨ q=15 := by simp [inl] at hq; omega
  rcases h with rfl|rfl|rfl|rfl
  · exact ⟨inlineGroupCheck_9_0,inlineGroupCheck_9_25,inlineGroupCheck_9_50,inlineGroupCheck_9_75,inlineGroupCheck_9_100⟩
  · exact ⟨inlineGroupCheck_13_0,inlineGroupCheck_13_25,inlineGroupCheck_13_50,inlineGroupCheck_13_75,inlineGroupCheck_13_100⟩
  · exact ⟨inlineGroupCheck_14_0,inlineGroupCheck_14_25,inlineGroupCheck_14_50,inlineGroupCheck_14_75,
      inlineGroupCheck_14_100⟩
  · exact ⟨inlineGroupCheck_15_0,inlineGroupCheck_15_25,inlineGroupCheck_15_50,inlineGroupCheck_15_75,
      inlineGroupCheck_15_100⟩
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
theorem entCheck_at (q k : Nat) (hq : q<17) (hn : inl q=false) (hk : k<nRank q) : entCheck q k=true := by
  have h := tripleCheck_at q hq hn
  simp only [tripleCheck,Bool.and_eq_true] at h
  exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).1
theorem static_false_of_row_false (q k : Nat) (h : rowInl q k=false) : inl q=false := by
  simp [rowInl, Bool.or_eq_false_iff] at h
  exact h.1
theorem rowInl_lt (q k : Nat) (h : rowInl q k=true) : q<16 := by
  simp [rowInl, inl] at h
  omega
theorem rowInl_ge (q k : Nat) (h : rowInl q k=true) : 9≤q := by
  simp [rowInl, inl] at h
  omega
theorem mx_inl (q : Nat) (hq : inl q=true) : mx q=4 := by
  simp [inl] at hq; unfold mx; rw [if_neg (by omega), if_pos (by omega)]
theorem mx_rowInl (q k : Nat) (hq : rowInl q k=true) : mx q=4 := by
  have h1 := rowInl_lt q k hq
  have h2 := rowInl_ge q k hq
  unfold mx; rw [if_neg (by omega), if_pos h1]
theorem nRank_rowInl (q k : Nat) (hq : rowInl q k=true) : nRank q=125 := by
  have h1 := rowInl_lt q k hq
  unfold nRank; rw [if_neg (by omega), mx_rowInl q k hq]; norm_num
theorem inlineCheck_at (q k : Nat) (hq : rowInl q k=true) (hk : k<125) : inlineCheck q k=true := by
  cases hn : inl q
  · have hq16 := rowInl_lt q k hq
    have h := entCheck_at q k (by omega) hn (by rw [nRank_rowInl q k hq]; exact hk)
    simpa only [entCheck,hq,if_true] using h
  · exact inlineCheck_static_at q k hn hk
theorem s8Check_at (q k : Nat) (hq : q<17) (hk : k<nRank q) : s8Check q k=true := by
  cases hn : inl q
  · have h := tripleCheck_at q hq hn
    simp only [tripleCheck,Bool.and_eq_true] at h
    exact (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp h.1 k (List.mem_range.mpr hk))).2
  · have hm := mx_inl q hn
    have h16 : q ≠ 16 := by rintro rfl; simp [inl] at hn
    unfold nRank at hk; rw [if_neg h16, hm] at hk
    have h := inlineCheck_static_at q k hn (by norm_num at hk; omega)
    simp only [inlineCheck,Bool.and_eq_true] at h
    exact h.1.1.1.1
/-- Shared bodies of the r6 groups (all `dB, dC ≤ 5`) and of #938's non-inline r5 groups (`dB + dC < 3`). -/
theorem blockCheck_at (q dB dC : Nat) (hq : q<16) (hn : inl q=false) (hB : dB ≤ mx q) (hC : dC ≤ mx q)
    (hBC : q<9 ∨ dB+dC < 3) : blockCheck q dB dC=true := by
  have h := tripleCheck_at q (by omega) hn
  simp only [tripleCheck,Bool.and_eq_true] at h
  have h16 : q ≠ 16 := by omega
  have hh : (mx q+1)*dB+dC<nBlock q := by
    unfold nBlock; rw [if_neg h16]
    unfold mx at *
    split_ifs at * <;> nlinarith
  have e1 : ((mx q+1)*dB+dC)/(mx q+1)=dB := by
    unfold mx at *
    split_ifs at * <;> omega
  have e2 : ((mx q+1)*dB+dC)%(mx q+1)=dC := by
    unfold mx at *
    split_ifs at * <;> omega
  have hb := List.all_eq_true.mp h.2 ((mx q+1)*dB+dC) (List.mem_range.mpr hh)
  unfold liveBlock at hb
  rw [if_neg h16, e1, e2, if_pos (by omega)] at hb
  exact hb
/-- The r7 pair's 7 bodies (ladder of chain 48, chain 49 with digit `dB`, checksum dispatch). -/
theorem pairBlockCheck_at (dB : Nat) (hB : dB ≤ 6) : blockCheck 16 dB 0=true := by
  have h := tripleCheck_16
  simp only [tripleCheck,Bool.and_eq_true] at h
  have hb := List.all_eq_true.mp h.2 dB (List.mem_range.mpr (by unfold nBlock; simp; omega))
  unfold liveBlock at hb
  rw [if_pos rfl] at hb
  exact hb
theorem s8Run_at (q k : Nat) (hq : q<17) (hk : k<nRank q) :
    (if q=0 then rOK (vrun (entW 0 k) 1) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k)))=true := by
  have h := s8Check_at q k hq hk
  simp only [s8Check,Bool.and_eq_true] at h
  exact h.1
theorem bge9_at (k : Nat) (hk : k<125) (he : k%2=0) : vrun (cellW 9 k) 1=some (bge9R (cellW 9 k)) := by
  have h := s8Check_at 9 k (by decide +kernel) (by unfold nRank mx; norm_num; omega)
  simp only [s8Check,Bool.and_eq_true] at h
  have h2 := h.2
  rw [if_pos (by simp [he])] at h2
  exact rOK_eq h2
/-! ### T51: guards, checksum landings and arms (Part5) -/
theorem guard6Check_at (g raw : Nat) (hg : g<9) (hr : raw<256) : guard6Check g raw=true := by
  have h : guard6All g=true := by
    interval_cases g
    exacts [guard6All_0, guard6All_1, guard6All_2, guard6All_3, guard6All_4, guard6All_5, guard6All_6, guard6All_7,
      guard6All_8]
  exact List.all_eq_true.mp h raw (List.mem_range.mpr hr)
theorem r7GuardCheck_at (k : Nat) (hk : k<126) : r7GuardCheck k=true :=
  List.all_eq_true.mp r7GuardAll_ok k (List.mem_range.mpr hk)
theorem ckGuardCheck_at (ds : Nat) (hd : ds<232) : ckGuardCheck ds=true :=
  List.all_eq_true.mp ckGuardAll_ok ds (List.mem_range.mpr hd)
theorem ckArmCheck_at (d : Nat) (hd : d<6) : ckArmCheck d=true :=
  List.all_eq_true.mp ckArmAll_ok d (List.mem_range.mpr hd)
end SigGolfCandidate.T3M.Nonbinary
end
end
