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
