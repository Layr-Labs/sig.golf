import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecksPart11
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheckParts

section

end

section


section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- R6: chain 0 at its largest digit (`skipA`) is a non-inline r6 row; `skipA` only matters for q = 0. -/
theorem skipA_noninl (q k : Nat) (h0 : q≠0) : skipA q k=false := by
  simp [skipA,h0]
theorem vrun_zero (p : Nat) : vrun p 0=some (emptyR p) := by
  unfold vrun symRun; cases lcode p <;> rfl
theorem rOK_emptyR (p : Nat) : rOK (vrun p 0) (emptyR p)=true := by
  rw [vrun_zero]
  have hs : stBeq SymState.init SymState.init=true := by decide +kernel
  simp [rOK,resBeq,emptyR,hs,E.beq]
theorem partOK_skip (q i d p : Nat) (hd : d=mx q) : partOK q i d p true=true := by
  unfold partOK; rw [if_pos hd]; simp only [if_true]; exact rOK_emptyR p
theorem gbase_noninl (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) (hn : rowInl q (c.kOf q)=false) :
    gbase q (c.kOf q)=base q (c.dig (3*q+1)) (c.dig (3*q+2)) := by
  obtain ⟨-,k2,k3⟩ := c.kdig_kOf hd q hq
  simp only [gbase,hn,Bool.false_eq_true,if_false,k2,k3]
theorem gB_noninl (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) (h8 : 8≤q) (hn : rowInl q (c.kOf q)=false) :
    gB q (c.kOf q)=pcB q (c.dig (3*q+1)) (c.dig (3*q+2)) := by
  simp only [gB,pcB,c.gbase_noninl hd q hq hn,skipA_noninl q _ (by omega),Bool.false_eq_true,if_false,Nat.sub_zero,
    show ¬ q<8 by omega]
/-- R6 groups: chain B starts at the body's part B, or 4 words later when it is buffer-safe (its copy is skipped). -/
theorem gB_r6 (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<8) :
    gB q (c.kOf q)=pcB q (c.dig (3*q+1)) (c.dig (3*q+2))+(if skipB q (c.kOf q) then 4 else 0) := by
  have hn : rowInl q (c.kOf q)=false := by simp [rowInl,inl]; omega
  simp only [gB,pcB,c.gbase_noninl hd q (by omega) hn,hq,if_true]
theorem gC_eq (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    gC q (c.kOf q)=gB q (c.kOf q)+partLen q (c.dig (3*q+1))-(if skipB q (c.kOf q) then 4 else 0) := by
  obtain ⟨-,k2,-⟩ := c.kdig_kOf hd q hq
  simp only [gC,k2]
theorem gX_eq (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    gX q (c.kOf q)=gC q (c.kOf q)+partLen q (c.dig (3*q+2))-(if skipC q (c.kOf q) then 4 else 0) := by
  obtain ⟨-,-,k3⟩ := c.kdig_kOf hd q hq
  simp only [gX,k3]
structure GroupFacts (c : NCtx) (q : Nat) : Prop where
  copyJ : rowInl q (c.kOf q)=false → c.dig (3*q)=mx q → q≠0 →
    vrun (leadPc q (c.kOf q)) 7=some (copyN .x8 (off (3*q)) (slot (3*q)) (gB q (c.kOf q)))
  skipJ : q=0 → c.dig 0=mx 0 → vrun (leadPc 0 (c.kOf 0)) 1=some (T3M.skipJB (gB 0 (c.kOf 0)))
  headJ : rowInl q (c.kOf q)=false → c.dig (3*q)+1< mx q →
    vrun (leadPc q (c.kOf q)) 7=some (headJD .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  headJT : rowInl q (c.kOf q)=false → c.dig (3*q)+1=mx q →
    vrun (leadPc q (c.kOf q)) 7=
      some (headJDTerm .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  copyF : rowInl q (c.kOf q)=true → skipA q (c.kOf q)=false → c.dig (3*q)=mx q →
    vrun (leadPc q (c.kOf q)) 4=some (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q (c.kOf q)))
  headF : rowInl q (c.kOf q)=true → c.dig (3*q)+1< mx q →
    vrun (leadPc q (c.kOf q)) 4=some (headJDF .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  headFT : rowInl q (c.kOf q)=true → c.dig (3*q)+1=mx q →
    vrun (leadPc q (c.kOf q)) 3=
      some (headJDTermF .x8 (off (3*q)) (gbase q (c.kOf q)+2*c.dig (3*q)+1) (3*q) (c.dig (3*q)))
  tail : c.dig (3*q)< mx q →
    vrun (gbase q (c.kOf q)+2*c.dig (3*q)+1) 2=
      some (tailR (if c.dig (3*q)+1=mx q then some (slot (3*q)) else none) (gbase q (c.kOf q)+2*c.dig (3*q)+1))
  rungs : rungsOK q (c.dig (3*q)+1) (slot (3*q)) (gbase q (c.kOf q)+2*(c.dig (3*q)+1))=true
  partB : partOK q (3*q+1) (c.dig (3*q+1)) (gB q (c.kOf q)) (skipB q (c.kOf q))=true
  partC : partOK q (3*q+2) (c.dig (3*q+2)) (gC q (c.kOf q)) (skipC q (c.kOf q))=true
  disp : q<17 → vrun (gX q (c.kOf q)) 5=some (nextDispR q)
  s8 : s8Check q (c.kOf q)=true
theorem mx_bounds' (q : Nat) : 3≤ mx q ∧ mx q≤7 := by unfold mx;split_ifs <;> omega
theorem rungsOK_mono (q d0 d1 sl b : Nat) (h : d0 ≤ d1) (hk : rungsOK q d0 sl (b+2*d0)=true) :
    rungsOK q d1 sl (b+2*d1)=true := by
  unfold rungsOK at hk ⊢
  rw [List.all_eq_true] at hk ⊢
  intro m hm
  rw [List.mem_range'_1] at hm
  have := hk m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
  rwa [show b+2*d0+2*(m-d0)=b+2*d1+2*(m-d1) by omega] at this
theorem groupFacts (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) : c.GroupFacts q := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q (by omega)
  have hk := c.kOf_lt hds q (by omega)
  have hA := c.dig_group_le hds q 0 (by omega) (by decide +kernel)
  simp only [Nat.add_zero] at hA
  have hB := c.dig_group_le hds q 1 (by omega) (by decide +kernel)
  have hC := c.dig_group_le hds q 2 (by omega) (by decide +kernel)
  have hm := mx_bounds' q
  cases hn : rowInl q (c.kOf q)
  · have hs := static_false_of_row_false q (c.kOf q) hn
    have he := entCheck_at q (c.kOf q) hq hs hk
    have hb := blockCheck_at q _ _ hq hs hB hC
    simp only [entCheck,hn,Bool.false_eq_true,if_false,k1] at he
    simp only [blockCheck,dispatchOK,Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨htails,hrungs⟩,hpB⟩,hpC⟩,hdisp⟩ := hb
    have eb := c.gbase_noninl hds q (by omega) hn
    have hsC : skipC q (c.kOf q)=skipBody q (c.dig (3*q+1)) (c.dig (3*q+2)) := by
      simp only [skipC,skipBody,hn,k2,k3,Bool.false_or]
      by_cases h8 : q<8 <;> simp [h8]
    have eC : gC q (c.kOf q)=pcC q (c.dig (3*q+1)) (c.dig (3*q+2)) := by
      rw [c.gC_eq hds q (by omega)]
      by_cases h8 : q<8
      · rw [c.gB_r6 hds q h8]; simp only [pcC]; split_ifs <;> omega
      · have hs0 : skipB q (c.kOf q)=false := by simp [skipB,hn,h8]
        rw [c.gB_noninl hds q (by omega) (by omega) hn, hs0]; simp [pcC]
    have eX : gX q (c.kOf q)=pcX q (c.dig (3*q+1)) (c.dig (3*q+2)) := by
      rw [c.gX_eq hds q (by omega),eC,hsC]; rfl
    refine ⟨fun _ hd h0 => ?_,fun h0 hd => ?_,fun _ hd => ?_,fun _ hd => ?_,fun h => by simp [hn] at h,
      fun h => by simp [hn] at h,fun h => by simp [hn] at h,fun hd => ?_,?_,?_,?_,?_,s8Check_at q _ hq hk⟩
    · rw [if_pos hd,if_neg h0] at he; exact rOK_eq he
    · have hd' : c.dig (3*q)=mx q := by rw [h0]; simpa using hd
      rw [if_pos hd',if_pos h0] at he; subst h0; exact rOK_eq he
    · rw [if_neg (by omega),if_neg (by omega)] at he; exact rOK_eq he
    · rw [if_neg (by omega),if_pos hd] at he; exact rOK_eq he
    · have h := List.all_eq_true.mp htails (c.dig (3*q)) (List.mem_range.mpr hd)
      rw [eb]; simpa only [Nat.add_assoc] using rOK_eq h
    · rw [eb]
      have h0 : rungsOK q 0 (slot (3*q)) (base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*0)=true := by simpa using hrungs
      exact rungsOK_mono q 0 _ _ _ (by omega) h0
    · by_cases h8 : q<8
      · rw [c.gB_r6 hds q h8]
        by_cases hsk : skipB q (c.kOf q)=true
        · have hm' := hsk
          simp only [skipB,hn,k1,k2,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] at hm'
          rw [hsk]; exact partOK_skip _ _ _ _ hm'.2.2
        · have hs0 : skipB q (c.kOf q)=false := by simpa using hsk
          rw [hs0]; simpa using hpB
      · have hs0 : skipB q (c.kOf q)=false := by simp [skipB,hn,h8]
        rw [c.gB_noninl hds q (by omega) (by omega) hn,hs0]; exact hpB
    · rw [eC,hsC]; exact hpC
    · intro hq17; rw [eX]; rw [if_pos hq17] at hdisp; exact rOK_eq hdisp
  · have hm4 := mx_rowInl q (c.kOf q) hn
    rw [hm4] at hk
    have he := inlineCheck_at q (c.kOf q) hn (by norm_num at hk; omega)
    simp only [inlineCheck,k1,k2,k3] at he
    by_cases hd : c.dig (3*q)=mx q
    · rw [if_pos hd] at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨⟨⟨⟨hs8,hcopy⟩,hpB⟩,hpC⟩,hdisp⟩ := he
      refine ⟨fun h => by simp [hn] at h,fun h0 _ => absurd h0 (by have := rowInl_ge q _ hn; omega),
        fun h => by simp [hn] at h,fun h => by simp [hn] at h,
        (fun _ hs _ => by simp only [hs,Bool.false_eq_true,if_false] at hcopy; exact rOK_eq hcopy),fun _ h => absurd h (by omega),fun _ h => absurd h (by omega),
        fun h => absurd h (by omega),?_,hpB,hpC,fun _ => rOK_eq hdisp,hs8⟩
      unfold rungsOK; rw [List.all_eq_true]; intro m hm'; rw [List.mem_range'_1] at hm'; omega
    · rw [if_neg hd] at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨⟨⟨⟨hs8,⟨⟨hhead,htail⟩,hrungs⟩⟩,hpB⟩,hpC⟩,hdisp⟩ := he
      refine ⟨fun h => by simp [hn] at h,fun h0 _ => absurd h0 (by have := rowInl_ge q _ hn; omega),
        fun h => by simp [hn] at h,fun h => by simp [hn] at h,
        fun _ _ h => absurd h hd,fun _ h => ?_,fun _ h => ?_,fun _ => rOK_eq htail,hrungs,hpB,hpC,
        fun _ => rOK_eq hdisp,hs8⟩
      · rw [if_neg (by omega)] at hhead; simpa only [if_neg (show ¬ c.dig (3*q)+1=mx q by omega)] using rOK_eq hhead
      · rw [if_pos h] at hhead; simpa only [if_pos h] using rOK_eq hhead
theorem kOf_eq_lead (c : NCtx) (i : Nat) (h0 : i%3=0) : 3*(i/3)=i := by omega
theorem chk_headJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (h51 : i<51) (hn : rowInl (i/3) (c.kOf (i/3))=false) (hd : c.dig i< last i) :
    vrun (c.startPc i) 7=some (headJD .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).headJ hn (by simpa only [last,topMax,eq] using (show c.dig (3*q)+1<topMax (3*q) by unfold last at hd; omega))
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq,show 3*q<51 by omega]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq,show 3*q<51 by omega]
  rw [hs,hr]; exact hf
theorem chk_headJTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (h51 : i<51) (hn : rowInl (i/3) (c.kOf (i/3))=false) (hd : c.dig i=last i) :
    vrun (c.startPc i) 7=some (headJDTerm .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hm := topMax_bounds (3*q)
  have hf := (c.groupFacts hds q (by omega)).headJT hn (by simp only [last,topMax,eq] at hd hm; omega)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq,show 3*q<51 by omega]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq,show 3*q<51 by omega]
  rw [hs,hr]; exact hf
theorem chk_copyJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (h51 : i<51) (hn : rowInl (i/3) (c.kOf (i/3))=false) (hd : c.dig i=topMax i) (hiz : i≠0) :
    vrun (c.startPc i) 7=some (copyN .x8 (off i) (slot i) (c.endPc i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).copyJ hn (by simpa only [topMax,eq] using hd) (by omega)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq,show 3*q<51 by omega]
  have he : c.endPc (3*q)=gB q (c.kOf q) := by simp [endPc,qB,eq,show 3*q<51 by omega]
  rw [hs,he]; exact hf
/-- R6 chain 0 at its largest digit (buffer-safe): the cell's lead is a single `jal` to chain B. -/
theorem chk_skipJ (c : NCtx) (hds : c.DigitsOk) (hd : c.dig 0=topMax 0) :
    vrun (c.startPc 0) 1=some (T3M.skipJB (c.endPc 0)) := by
  have hf := (c.groupFacts hds 0 (by omega)).skipJ rfl (by simpa only [topMax] using hd)
  have hs : c.startPc 0=leadPc 0 (c.kOf 0) := by simp [startPc]
  have he : c.endPc 0=gB 0 (c.kOf 0) := by simp [endPc,qB]
  rw [hs,he]; exact hf
theorem chk_headJF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (h51 : i<51) (hn : rowInl (i/3) (c.kOf (i/3))=true) (hd : c.dig i< last i) :
    vrun (c.startPc i) 4=some (headJDF .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).headF hn (by simpa only [last,topMax,eq] using (show c.dig (3*q)+1<topMax (3*q) by unfold last at hd; omega))
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq,show 3*q<51 by omega]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq,show 3*q<51 by omega]
  rw [hs,hr]; exact hf
theorem chk_headJTermF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (h51 : i<51) (hn : rowInl (i/3) (c.kOf (i/3))=true) (hd : c.dig i=last i) :
    vrun (c.startPc i) 3=some (headJDTermF .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hm := topMax_bounds (3*q)
  have hf := (c.groupFacts hds q (by omega)).headFT hn (by simp only [last,topMax,eq] at hd hm; omega)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq,show 3*q<51 by omega]
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq,show 3*q<51 by omega]
  rw [hs,hr]; exact hf
theorem chk_copyFL (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (h51 : i<51) (hn : rowInl (i/3) (c.kOf (i/3))=true) (hd : c.dig i=topMax i) (hskip : skipA (i/3) (c.kOf (i/3))=false) :
    vrun (c.startPc i) 4=some (copyFH .x8 (off i) (slot i) (c.startPc i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  rw [eq] at hn
  have hf := (c.groupFacts hds q (by omega)).copyF hn (by simpa only [eq] using hskip) (by simpa only [topMax,eq] using hd)
  have hs : c.startPc (3*q)=leadPc q (c.kOf q) := by simp [startPc,eq,show 3*q<51 by omega]
  rw [hs]; exact hf
theorem skipB_eq (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    skipB q (c.kOf q)=decide (c.bufferSafe (3*q+1)) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q (by omega)
  have he : c.bufferSafe (3*q+1) ↔ c.dig (3*q+1)=mx q ∧ c.dig (3*q)=mx q := by
    simp [bufferSafe,topMax,show (3*q+1)/3=q by omega,show (3*q)/3=q by omega,
      show (3*q+1)%3=1 by omega,show 3*q+1≠0 by omega]
  by_cases ha : c.dig (3*q)=mx q
  · by_cases hb : c.dig (3*q+1)=mx q
    · have hr : (rowInl q (c.kOf q) || decide (q<8))=true := by
        by_cases h8 : q<8
        · simp [h8]
        · have hm := mx_bounds' q
          have hw : 3≤kss q (c.kOf q) := by unfold kss; rw [k1,k2,k3,ha]; omega
          simp [rowInl,hw,hq,show 8≤q by omega]
      unfold skipB; rw [hr,k1,k2]; simp [he,ha,hb]
    · simp [skipB,k1,k2,he,hb]
  · simp [skipB,k1,k2,he,ha]
theorem skipC_eq (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    skipC q (c.kOf q)=decide (c.bufferSafe (3*q+2)) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q (by omega)
  have he : c.bufferSafe (3*q+2) ↔ c.dig (3*q+2)=mx q ∧ c.dig (3*q+1)=mx q := by
    simp [bufferSafe,topMax,show (3*q+2)/3=q by omega,show (3*q+1)/3=q by omega,
      show (3*q+2)%3=2 by omega,show 3*q+2≠0 by omega]
  by_cases hb : c.dig (3*q+1)=mx q
  · by_cases hc : c.dig (3*q+2)=mx q
    · have hr : (rowInl q (c.kOf q) || decide (q<8))=true := by
        by_cases h8 : q<8
        · simp [h8]
        · have hm := mx_bounds' q
          have hw : 3≤kss q (c.kOf q) := by unfold kss; rw [k1,k2,k3,hb]; omega
          simp [rowInl,hw,hq,show 8≤q by omega]
      unfold skipC; rw [hr,k2,k3]; simp [he,hb,hc]
    · simp [skipC,k2,k3,he,hc]
  · simp [skipC,k2,k3,he,hb]
theorem bufferSafe_51 (c : NCtx) : ¬ c.bufferSafe 51 := by simp [bufferSafe]
theorem part_at (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : ¬ (i%3=0 ∧ i<51)) :
    partOK (i/3) i (c.dig i) (c.startPc i) (decide (c.bufferSafe i))=true := by
  obtain ⟨q,r,rfl,hr⟩ : ∃q r,i=3*q+r ∧ r<3 := ⟨i/3,i%3,by omega,by omega⟩
  have eq : (3*q+r)/3=q := by omega
  have hf := c.groupFacts hds q (by omega)
  unfold startPc qB qC
  rw [if_pos hi,if_neg (by omega),eq]
  rcases (show r=1 ∨ r=2 by omega) with rfl|rfl
  · rw [if_pos (by omega)]; simpa only [c.skipB_eq hds q (by omega)] using hf.partB
  · rw [if_neg (by omega)]; simpa only [c.skipC_eq hds q (by omega)] using hf.partC
theorem chk_headR (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51)
    (h0 : ¬ (i%3=0 ∧ i<51)) (hd : c.dig i< last i) :
    vrun (c.startPc i) 8=some (headRH .x8 (off i) (c.dig i) none (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i< mx (i/3)-1 := hd
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_neg (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_headRTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51)
    (h0 : ¬ (i%3=0 ∧ i<51)) (hd : c.dig i=last i) :
    vrun (c.startPc i) 8=some (headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i=mx (i/3)-1 := hd
  have hm : 3≤ mx (i/3) := (topMax_bounds i).1
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_pos (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_copyF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51)
    (h0 : ¬ (i%3=0 ∧ i<51)) (hd : c.dig i=topMax i) (hn : ¬ c.bufferSafe i) :
    vrun (c.startPc i) 4=some (copyFH .x8 (off i) (slot i) (c.startPc i)) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  change c.dig i=mx (i/3) at hd
  rw [if_pos hd] at hp
  simp only [hn,decide_false,Bool.false_eq_true,if_false] at hp
  exact rOK_eq hp
theorem chk_rung (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<51)
    (hm : c.dig i< m) (hm2 : m ≤ last i) :
    vrun (c.rungPc i m) 3=some (rungR m (if m=last i then some (slot i) else none) (c.rungPc i m)) := by
  have hmx := topMax_bounds i
  by_cases h0 : i%3=0 ∧ i<51
  · obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
    have eq : 3*q/3=q := by omega
    have hf := c.groupFacts hds q (by omega)
    have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
    have hh := List.all_eq_true.mp hf.rungs m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc (3*q) m=gbase q (c.kOf q)+2*(c.dig (3*q)+1)+2*(m-(c.dig (3*q)+1)) := by
      simp [rungPc,qb,eq,show 3*q<51 by omega]; omega
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
theorem chk_tail (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) (h0 : i%3=0) (h51 : i<51) (hd : c.dig i<topMax i) :
    vrun (c.rungPc i (c.dig i)+1) 2=
      some (tailR (if c.dig i=last i then some (slot i) else none) (c.rungPc i (c.dig i)+1)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have hf := c.groupFacts hds q (by omega)
  have hmx := mx_bounds' q
  have hr : c.rungPc (3*q) (c.dig (3*q))=gbase q (c.kOf q)+2*c.dig (3*q) := by simp [rungPc,qb,eq,show 3*q<51 by omega]
  have ht : (c.dig (3*q)+1=mx q) ↔ c.dig (3*q)=last (3*q) := by unfold last topMax;rw [eq];omega
  have h := hf.tail (by simpa only [topMax,eq] using hd)
  rw [hr]
  simpa only [ht] using h
end SigGolfCandidate.T3M.Nonbinary.NCtx
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
/-! ### R6 checksum chain 51 (layout level): its code for digit `d` sits at `ckArm d` (main's chain-part shape with
largest digit 7: head + rungs, terminal head, or copy), followed by the final tail at `ckTail d`. -/
theorem ck_headR (d : Nat) (hd : d+1<7) :
    vrun (ckArm d) 8=some (headRH .x8 (off 51) d none (ckArm d) 51) := by
  have hp := ckArmCheck_at d (by omega)
  unfold ckArmCheck partOK at hp
  rw [if_neg (show d≠mx 17 by simp [mx]; omega),Bool.and_eq_true,if_neg (show ¬ d+1=mx 17 by simp [mx]; omega)] at hp
  exact rOK_eq hp.1
theorem ck_headRTerm :
    vrun (ckArm 6) 8=some (headRHT .x8 (off 51) 6 (slot 51) (ckArm 6) 51) := by
  have hp := ckArmCheck_at 6 (by omega)
  unfold ckArmCheck partOK at hp
  rw [if_neg (show (6:Nat)≠mx 17 by simp [mx]),Bool.and_eq_true,if_pos (show 6+1=mx 17 by simp [mx])] at hp
  exact rOK_eq hp.1
theorem ck_copyF :
    vrun (ckArm 7) 4=some (copyFH .x8 (off 51) (slot 51) (ckArm 7)) := by
  have hp := ckArmCheck_at 7 (by omega)
  unfold ckArmCheck partOK at hp
  rw [if_pos (show (7:Nat)=mx 17 by simp [mx])] at hp
  simp only [Bool.false_eq_true,if_false] at hp
  exact rOK_eq hp
theorem ck_rung (d m : Nat) (hm : d < m) (hm2 : m ≤ 6) :
    vrun (ckArm d+5+2*(m-(d+1))) 3=
      some (rungR m (if m=6 then some (slot 51) else none) (ckArm d+5+2*(m-(d+1)))) := by
  have hp := ckArmCheck_at d (by omega)
  unfold ckArmCheck partOK at hp
  rw [if_neg (show d≠mx 17 by simp [mx]; omega),Bool.and_eq_true] at hp
  have hh := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega,by simp [mx]; omega⟩)
  have ht : (m+1=mx 17) ↔ m=6 := by simp [mx]
  simpa only [ht] using rOK_eq hh
end SigGolfCandidate.T3M.Nonbinary
end
end
