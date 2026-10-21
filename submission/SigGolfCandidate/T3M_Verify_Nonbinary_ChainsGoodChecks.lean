import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecksPart11
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsSem
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsCheckParts

section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-! ### T51 group facts at a rank (NCtx-free)
`GroupFactsK q k` collects, for top group `q` and rank `k` (digits `kdig q k 0/1/2` = chains A/B/C), every code
piece the top run executes: the cell (s8 word, chain A's head / copy / skip jump), chain A's rung ladder (its terminal
step targets `termSlot (3q)`), chains B and C (the r7 pair, q = 16, has no chain C) and the next dispatch.  Proved
for every group `q < 17` and rank `k < nRank q` from the generated checks (Part0..11); NCtx-level users instantiate
`k := c.kOf q`. -/
theorem vrun_zero (p : Nat) : vrun p 0=some (emptyR p) := by
  unfold vrun symRun; cases lcode p <;> rfl
theorem rOK_emptyR (p : Nat) : rOK (vrun p 0) (emptyR p)=true := by
  rw [vrun_zero]
  have hs : stBeq SymState.init SymState.init=true := by decide +kernel
  simp [rOK,resBeq,emptyR,hs,E.beq]
theorem partOK_skip (q i d p : Nat) (hd : d=mx q) : partOK q i d p true=true := by
  unfold partOK; rw [if_pos hd]; simp only [if_true]; exact rOK_emptyR p
theorem kdig_le_mx (q k j : Nat) : kdig q k j ≤ mx q := by
  unfold kdig; have := Nat.mod_lt (k/(mx q+1)^j) (show 0 < mx q+1 by omega); omega
theorem mx_bounds' (q : Nat) : 4 ≤ mx q ∧ mx q ≤ 6 := by unfold mx; split_ifs <;> omega
theorem rungsOK_mono (q d0 d1 sl b : Nat) (h : d0 ≤ d1) (hk : rungsOK q d0 sl (b+2*d0)=true) :
    rungsOK q d1 sl (b+2*d1)=true := by
  unfold rungsOK at hk ⊢
  rw [List.all_eq_true] at hk ⊢
  intro m hm
  rw [List.mem_range'_1] at hm
  have := hk m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
  rwa [show b+2*d0+2*(m-d0)=b+2*d1+2*(m-d1) by omega] at this
structure GroupFactsK (q k : Nat) : Prop where
  copyJ : rowInl q k=false → kdig q k 0=mx q → q≠0 →
    vrun (leadPc q k) 7=some (copyN .x8 (off (3*q)) (slot (3*q)) (gB q k) (topG (3*q)))
  skipJ : q=0 → kdig 0 k 0=mx 0 → vrun (leadPc 0 k) 1=some (T3M.skipJB (gB 0 k))
  headJ : rowInl q k=false → kdig q k 0+1 < mx q →
    vrun (leadPc q k) 7=some (headJD .x8 (off (3*q)) (gbase q k+2*kdig q k 0+1) (3*q) (kdig q k 0) (topG (3*q)))
  headJT : rowInl q k=false → kdig q k 0+1=mx q →
    vrun (leadPc q k) 7=some (headJDTerm .x8 (off (3*q)) (gbase q k+2*kdig q k 0+1) (3*q) (kdig q k 0))
  copyF : rowInl q k=true → skipA q k=false → kdig q k 0=mx q →
    vrun (leadPc q k) 4=some (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q k) (topG (3*q)))
  headF : rowInl q k=true → kdig q k 0+1 < mx q →
    vrun (leadPc q k) 4=some (headJDF .x8 (off (3*q)) (gbase q k+2*kdig q k 0+1) (3*q) (kdig q k 0) (topG (3*q)))
  headFT : rowInl q k=true → kdig q k 0+1=mx q →
    vrun (leadPc q k) 3=some (headJDTermF .x8 (off (3*q)) (gbase q k+2*kdig q k 0+1) (3*q) (kdig q k 0))
  tail : kdig q k 0 < mx q →
    vrun (gbase q k+2*kdig q k 0+1) 2=
      some (tailR (if kdig q k 0+1=mx q then some (termSlot (3*q)) else none) (gbase q k+2*kdig q k 0+1))
  rungs : rungsOK q (kdig q k 0+1) (termSlot (3*q)) (gbase q k+2*(kdig q k 0+1))=true
  partB : partOK q (3*q+1) (kdig q k 1) (gB q k) (skipB q k)=true
  partC : q≠16 → partOK q (3*q+2) (kdig q k 2) (gC q k) (skipC q k)=true
  disp : vrun (gX q k) 5=some (nextDispR q)
  s8 : s8Check q k=true
theorem kdig16_two (k : Nat) (hk : k<49) : kdig 16 k 2=0 := by
  unfold kdig mx; simp; omega
theorem groupFactsK (q k : Nat) (hq : q<17) (hk : k<nRank q) : GroupFactsK q k := by
  have hA := kdig_le_mx q k 0
  have hB := kdig_le_mx q k 1
  have hC := kdig_le_mx q k 2
  have hm := mx_bounds' q
  cases hn : rowInl q k
  · have hs := static_false_of_row_false q k hn
    have he := entCheck_at q k hq hs hk
    -- the shared body (block) of this rank
    have hb : blockCheck q (kdig q k 1) (kdig q k 2)=true := by
      by_cases h16 : q=16
      · subst h16
        have hk49 : k<49 := by simpa [nRank] using hk
        rw [kdig16_two k hk49]; exact pairBlockCheck_at _ (by simpa [mx] using hB)
      · refine blockCheck_at q _ _ (by omega) hs hB hC ?_
        by_cases h9 : q<9
        · exact Or.inl h9
        · right
          have hk3 : ¬ (3 ≤ kss q k) := by
            intro h3; simp [rowInl, show 9 ≤ q by omega, show q<16 by omega, h3] at hn
          unfold kss at hk3; omega
    simp only [entCheck,hn,Bool.false_eq_true,if_false] at he
    simp only [blockCheck,dispatchOK,if_pos hq,Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨htails,hrungs⟩,hpB⟩,hpC⟩,hdisp⟩ := hb
    have eb : gbase q k=base q (kdig q k 1) (kdig q k 2) := by simp [gbase,hn]
    have hsA : q≠0 → skipA q k=false := by intro h0; simp [skipA,h0]
    have eB : gB q k=pcB q (kdig q k 1) (kdig q k 2)+(if skipB q k then 4 else 0) := by
      unfold gB pcB
      by_cases hsh : sharedG q=true
      · rw [if_pos hsh, eb]
      · have h0 : q≠0 := by intro h0; subst h0; simp [sharedG] at hsh
        have hsB : skipB q k=false := by simp [skipB,hn,hsh]
        rw [if_neg hsh, eb, hsA h0, hsB]; simp
    have eC : gC q k=pcC q (kdig q k 1) (kdig q k 2) := by
      unfold gC; rw [eB]; unfold pcC; split_ifs <;> omega
    have hsC : skipC q k=skipBody q (kdig q k 1) (kdig q k 2) := by
      simp only [skipC,skipBody,hn,Bool.false_or]
      by_cases h9 : q<9 <;> simp [h9]
    have eX : gX q k=pcX q (kdig q k 1) (kdig q k 2) := by
      unfold gX pcX; rw [eC, hsC]
    refine ⟨fun _ hd h0 => ?_,fun h0 hd => ?_,fun _ hd => ?_,fun _ hd => ?_,fun h => by simp [hn] at h,
      fun h => by simp [hn] at h,fun h => by simp [hn] at h,fun hd => ?_,?_,?_,fun h16 => ?_,?_,
      s8Check_at q k hq hk⟩
    · rw [if_pos hd,if_neg h0] at he; exact rOK_eq he
    · subst h0; rw [if_pos hd,if_pos rfl] at he; exact rOK_eq he
    · rw [if_neg (by omega),if_neg (by omega)] at he; exact rOK_eq he
    · rw [if_neg (by omega),if_pos hd] at he; exact rOK_eq he
    · have h := List.all_eq_true.mp htails (kdig q k 0) (List.mem_range.mpr hd)
      rw [eb]; simpa only [Nat.add_assoc] using rOK_eq h
    · rw [eb]
      have h0 : rungsOK q 0 (termSlot (3*q)) (base q (kdig q k 1) (kdig q k 2)+2*0)=true := by simpa using hrungs
      exact rungsOK_mono q 0 _ _ _ (by omega) h0
    · rw [eB]
      cases hsk : skipB q k
      · simpa using hpB
      · have hm' := hsk
        simp only [skipB,Bool.and_eq_true,decide_eq_true_eq] at hm'
        exact partOK_skip _ _ _ _ hm'.2.2
    · rw [eC,hsC]; simpa [h16] using hpC
    · rw [eX]; exact rOK_eq hdisp
  · have hm4 := mx_rowInl q k hn
    have hk125 : k<125 := by rw [nRank_rowInl q k hn] at hk; exact hk
    have he := inlineCheck_at q k hn hk125
    have hq9 := rowInl_ge q k hn
    simp only [inlineCheck] at he
    by_cases hd : kdig q k 0=mx q
    · rw [if_pos hd] at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨⟨⟨⟨hs8,hcopy⟩,hpB⟩,hpC⟩,hdisp⟩ := he
      refine ⟨fun h => by simp [hn] at h,fun h0 _ => absurd h0 (by omega),
        fun h => by simp [hn] at h,fun h => by simp [hn] at h,
        (fun _ hs _ => by simp only [hs,Bool.false_eq_true,if_false] at hcopy; exact rOK_eq hcopy),
        fun _ h => absurd h (by omega),fun _ h => absurd h (by omega),
        fun h => absurd h (by omega),?_,hpB,fun _ => hpC,rOK_eq hdisp,hs8⟩
      unfold rungsOK; rw [List.all_eq_true]; intro m hm'; rw [List.mem_range'_1] at hm'; omega
    · rw [if_neg hd] at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨⟨⟨⟨hs8,⟨⟨hhead,htail⟩,hrungs⟩⟩,hpB⟩,hpC⟩,hdisp⟩ := he
      refine ⟨fun h => by simp [hn] at h,fun h0 _ => absurd h0 (by omega),
        fun h => by simp [hn] at h,fun h => by simp [hn] at h,
        fun _ _ h => absurd h hd,fun _ h => ?_,fun _ h => ?_,fun _ => rOK_eq htail,hrungs,hpB,fun _ => hpC,
        rOK_eq hdisp,hs8⟩
      · rw [if_neg (by omega)] at hhead; simpa only [if_neg (show ¬ kdig q k 0+1=mx q by omega)] using rOK_eq hhead
      · rw [if_pos h] at hhead; simpa only [if_pos h] using rOK_eq hhead
end SigGolfCandidate.T3M.Nonbinary
end

section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-! ### T51 chain facts at NCtx level
Lead chains `i % 3 = 0, i < 50` (chain A of group `i / 3`: the r6 triples, #938's r5 triples, the r7 pair's chain 48)
run their cell lead and the group body's rung ladder; the other chains `i < 51` run a `partOK` piece: chain B / C of a
triple, chain 49 = the r7 pair's chain B, and the checksum chain 50 at its arm `ckArm d50` (group 17). -/
/-- Group of chain `i` (`i / 3` for `i < 50`, 17 for the checksum chain 50): `topMax i = mx (grpOf i)`. -/
def grpOf (i : Nat) : Nat := if i < 50 then i / 3 else 17
theorem topMax_grpOf (i : Nat) : topMax i = mx (grpOf i) := by
  unfold topMax grpOf; split_ifs <;> rfl
theorem kOf_lt_nRank (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) : c.kOf q < nRank q := by
  by_cases h16 : q=16
  · subst h16; unfold nRank; rw [if_pos rfl]; exact c.kOf16_lt hds
  · unfold nRank; rw [if_neg h16]; exact c.kOf_lt hds q (by omega)
/-- Digits A, B (and C, triples only) of group `q`'s rank. -/
theorem kdig_kOf' (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    kdig q (c.kOf q) 0=c.dig (3*q) ∧ kdig q (c.kOf q) 1=c.dig (3*q+1) ∧
      (q≠16 → kdig q (c.kOf q) 2=c.dig (3*q+2)) := by
  by_cases h16 : q=16
  · subst h16; obtain ⟨k1,k2,-⟩ := c.kdig_kOf16 hds; exact ⟨k1,k2,fun h => absurd rfl h⟩
  · obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q (by omega); exact ⟨k1,k2,fun _ => k3⟩
/-- The T51 group facts of group `q` at its rank `c.kOf q`. -/
def GroupFacts (c : NCtx) (q : Nat) : Prop := GroupFactsK q (c.kOf q)
theorem groupFacts (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) : c.GroupFacts q :=
  groupFactsK q _ hq (c.kOf_lt_nRank hds q hq)
theorem lead_q (i : Nat) (h0 : i%3=0) : 3*(i/3)=i := by omega
theorem startPc_lead (c : NCtx) (i : Nat) (hi : i<50) (h0 : i%3=0) : c.startPc i=leadPc (i/3) (c.kOf (i/3)) := by
  unfold startPc; rw [if_pos hi, if_pos h0]
theorem rungPc_lead (c : NCtx) (i m : Nat) (hi : i<50) (h0 : i%3=0) : c.rungPc i m=gbase (i/3) (c.kOf (i/3))+2*m := by
  unfold rungPc qb; rw [if_pos ⟨h0,hi⟩]
theorem endPc_lead (c : NCtx) (i : Nat) (hi : i<50) (h0 : i%3=0) : c.endPc i=gB (i/3) (c.kOf (i/3)) := by
  unfold endPc qB; rw [if_pos hi, if_pos h0]
theorem dig_lead (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0) :
    kdig (i/3) (c.kOf (i/3)) 0=c.dig i := by
  have := (c.kdig_kOf' hds (i/3) (by omega)).1; rwa [lead_q i h0] at this
theorem mx_lead (i : Nat) (hi : i<50) : mx (i/3)=topMax i := (topMax_mx i hi).symm
theorem chk_headJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0)
    (hn : rowInl (i/3) (c.kOf (i/3))=false) (hd : c.dig i < last i) :
    vrun (c.startPc i) 7=some (headJD .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i) (topG i)) := by
  have hf := (c.groupFacts hds (i/3) (by omega)).headJ hn
    (by rw [dig_lead c hds i hi h0, mx_lead i hi]; unfold last at hd; omega)
  rw [dig_lead c hds i hi h0, lead_q i h0] at hf
  rw [c.startPc_lead i hi h0, c.rungPc_lead i _ hi h0]; exact hf
theorem chk_headJTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0)
    (hn : rowInl (i/3) (c.kOf (i/3))=false) (hd : c.dig i=last i) :
    vrun (c.startPc i) 7=some (headJDTerm .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  have hm := topMax_bounds i
  have hf := (c.groupFacts hds (i/3) (by omega)).headJT hn
    (by rw [dig_lead c hds i hi h0, mx_lead i hi]; unfold last at hd; omega)
  rw [dig_lead c hds i hi h0, lead_q i h0] at hf
  rw [c.startPc_lead i hi h0, c.rungPc_lead i _ hi h0]; exact hf
theorem chk_copyJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0) (hi0 : i≠0)
    (hn : rowInl (i/3) (c.kOf (i/3))=false) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 7=some (copyN .x8 (off i) (slot i) (c.endPc i) (topG i)) := by
  have hf := (c.groupFacts hds (i/3) (by omega)).copyJ hn
    (by rw [dig_lead c hds i hi h0, mx_lead i hi]; exact hd) (by omega)
  rw [lead_q i h0] at hf
  rw [c.startPc_lead i hi h0, c.endPc_lead i hi h0]; exact hf
/-- T51: chain 0 at its largest digit is buffer-safe; its cell holds only `jal` to chain B. -/
theorem chk_skipJ (c : NCtx) (hds : c.DigitsOk) (hd : c.dig 0=topMax 0) :
    vrun (c.startPc 0) 1=some (T3M.skipJB (c.endPc 0)) := by
  have hf := (c.groupFacts hds 0 (by omega)).skipJ rfl (by rw [dig_lead c hds 0 (by omega) rfl]; exact hd)
  rw [c.startPc_lead 0 (by omega) rfl, c.endPc_lead 0 (by omega) rfl]; exact hf
theorem chk_headJF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0)
    (hn : rowInl (i/3) (c.kOf (i/3))=true) (hd : c.dig i < last i) :
    vrun (c.startPc i) 4=some (headJDF .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i) (topG i)) := by
  have hf := (c.groupFacts hds (i/3) (by omega)).headF hn
    (by rw [dig_lead c hds i hi h0, mx_lead i hi]; unfold last at hd; omega)
  rw [dig_lead c hds i hi h0, lead_q i h0] at hf
  rw [c.startPc_lead i hi h0, c.rungPc_lead i _ hi h0]; exact hf
theorem chk_headJTermF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0)
    (hn : rowInl (i/3) (c.kOf (i/3))=true) (hd : c.dig i=last i) :
    vrun (c.startPc i) 3=some (headJDTermF .x8 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  have hm := topMax_bounds i
  have hf := (c.groupFacts hds (i/3) (by omega)).headFT hn
    (by rw [dig_lead c hds i hi h0, mx_lead i hi]; unfold last at hd; omega)
  rw [dig_lead c hds i hi h0, lead_q i h0] at hf
  rw [c.startPc_lead i hi h0, c.rungPc_lead i _ hi h0]; exact hf
theorem chk_copyFL (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0)
    (hn : rowInl (i/3) (c.kOf (i/3))=true) (hd : c.dig i=topMax i) (hskip : skipA (i/3) (c.kOf (i/3))=false) :
    vrun (c.startPc i) 4=some (copyFH .x8 (off i) (slot i) (c.startPc i) (topG i)) := by
  have hf := (c.groupFacts hds (i/3) (by omega)).copyF hn hskip
    (by rw [dig_lead c hds i hi h0, mx_lead i hi]; exact hd)
  rw [lead_q i h0] at hf
  rw [c.startPc_lead i hi h0]; exact hf
theorem chk_tail (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) (h0 : i%3=0) (hd : c.dig i < topMax i) :
    vrun (c.rungPc i (c.dig i)+1) 2=
      some (tailR (if c.dig i=last i then some (termSlot i) else none) (c.rungPc i (c.dig i)+1)) := by
  have hm := topMax_bounds i
  have hf := (c.groupFacts hds (i/3) (by omega)).tail (by rw [dig_lead c hds i hi h0, mx_lead i hi]; exact hd)
  rw [dig_lead c hds i hi h0, lead_q i h0, mx_lead i hi] at hf
  have ht : (c.dig i+1=topMax i) ↔ c.dig i=last i := by unfold last; omega
  rw [c.rungPc_lead i _ hi h0]
  simpa only [ht, Nat.add_assoc] using hf
/-- Chain B of group `q` is skipped (buffer-safe) iff chains A and B both hold their largest digit. -/
theorem skipB_eq (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    skipB q (c.kOf q)=decide (c.bufferSafe (3*q+1)) := by
  obtain ⟨k1,k2,-⟩ := c.kdig_kOf' hds q hq
  have he : c.bufferSafe (3*q+1) ↔ c.dig (3*q+1)=mx q ∧ c.dig (3*q)=mx q := by
    simp [bufferSafe,topMax_mx (3*q+1) (by omega),topMax_mx (3*q) (by omega),show (3*q+1)/3=q by omega,
      show (3*q)/3=q by omega,show (3*q+1)%3=1 by omega,show 3*q+1≠0 by omega,show 3*q+1≠50 by omega]
  by_cases ha : c.dig (3*q)=mx q
  · by_cases hb : c.dig (3*q+1)=mx q
    · have hr : (rowInl q (c.kOf q) || sharedG q)=true := by
        by_cases hs : q<9 ∨ q=16
        · simp [sharedG, hs]
        · have hm := mx_bounds' q
          have hk3 : 3 ≤ kss q (c.kOf q) := by unfold kss; rw [k1,k2,ha,hb]; omega
          simp [rowInl, show 9 ≤ q by omega, show q<16 by omega, hk3]
      simp only [skipB,hr,Bool.true_and,k1,k2,ha,hb,he]
    · simp [skipB,k1,k2,he,hb]
  · simp [skipB,k1,k2,he,ha]
/-- Chain C of a triple `q < 16` is skipped (buffer-safe) iff chains B and C both hold their largest digit. -/
theorem skipC_eq (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<16) :
    skipC q (c.kOf q)=decide (c.bufferSafe (3*q+2)) := by
  obtain ⟨-,k2,k3⟩ := c.kdig_kOf' hds q (by omega)
  have k3 := k3 (by omega)
  have he : c.bufferSafe (3*q+2) ↔ c.dig (3*q+2)=mx q ∧ c.dig (3*q+1)=mx q := by
    simp [bufferSafe,topMax_mx (3*q+2) (by omega),topMax_mx (3*q+1) (by omega),show (3*q+2)/3=q by omega,
      show (3*q+1)/3=q by omega,show (3*q+2)%3=2 by omega,show 3*q+2≠0 by omega,show 3*q+2≠50 by omega]
  by_cases hb : c.dig (3*q+1)=mx q
  · by_cases hc : c.dig (3*q+2)=mx q
    · have hr : (rowInl q (c.kOf q) || decide (q<9))=true := by
        by_cases hs : q<9
        · simp [hs]
        · have hm := mx_bounds' q
          have hk3 : 3 ≤ kss q (c.kOf q) := by unfold kss; rw [k2,k3,hb,hc]; omega
          simp [rowInl, show 9 ≤ q by omega, show q<16 by omega, hk3]
      simp only [skipC,hr,Bool.true_and,k2,k3,hb,hc,he]
    · simp [skipC,k2,k3,he,hc]
  · simp [skipC,k2,k3,he,hb]
theorem bufferSafe_50 (c : NCtx) : ¬ c.bufferSafe 50 := by simp [bufferSafe]
/-- The non-lead chains run a `partOK` piece of group `grpOf i` at `startPc i` (skipped when buffer-safe). -/
theorem part_at (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : ¬ (i%3=0 ∧ i<50)) :
    partOK (grpOf i) i (c.dig i) (c.startPc i) (decide (c.bufferSafe i))=true := by
  by_cases h50 : i<50
  · obtain ⟨q,r,rfl,hr⟩ : ∃q r,i=3*q+r ∧ r<3 := ⟨i/3,i%3,by omega,by omega⟩
    have eq : (3*q+r)/3=q := by omega
    have hf := c.groupFacts hds q (by omega)
    obtain ⟨-,k2,k3⟩ := c.kdig_kOf' hds q (by omega)
    have hg : grpOf (3*q+r)=q := by unfold grpOf; rw [if_pos h50, eq]
    unfold startPc qB qC
    rw [hg, if_pos h50, if_neg (by omega), eq]
    rcases (show r=1 ∨ r=2 by omega) with rfl|rfl
    · rw [if_pos (by omega)]
      have h := hf.partB; rw [k2] at h
      simpa only [c.skipB_eq hds q (by omega)] using h
    · rw [if_neg (by omega)]
      have h := hf.partC (by omega); rw [k3 (by omega)] at h
      simpa only [c.skipC_eq hds q (by omega)] using h
  · have h50' : i=50 := by omega
    subst h50'
    have hd := hds 50 (by omega)
    rw [topMax_50] at hd
    have h := ckArmCheck_at (c.dig 50) (by omega)
    unfold ckArmCheck at h
    have hs : startPc c 50=ckArm (c.dig 50) := by unfold startPc; rw [if_neg (by omega)]
    rw [hs, show grpOf 50=17 from rfl]
    simpa [c.bufferSafe_50] using h
theorem chk_headR (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51)
    (h0 : ¬ (i%3=0 ∧ i<50)) (hd : c.dig i < last i) :
    vrun (c.startPc i) 8=some (headRH .x8 (off i) (c.dig i) none (c.startPc i) i (topG i)) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i < mx (grpOf i)-1 := by rw [← topMax_grpOf]; exact hd
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_neg (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_headRTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51)
    (h0 : ¬ (i%3=0 ∧ i<50)) (hd : c.dig i=last i) :
    vrun (c.startPc i) 8=some (headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i=mx (grpOf i)-1 := by rw [← topMax_grpOf]; exact hd
  have hm : 3 ≤ mx (grpOf i) := by rw [← topMax_grpOf]; exact (topMax_bounds i).1
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_pos (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_copyF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51)
    (h0 : ¬ (i%3=0 ∧ i<50)) (hd : c.dig i=topMax i) (hn : ¬ c.bufferSafe i) :
    vrun (c.startPc i) 4=some (copyFH .x8 (off i) (slot i) (c.startPc i) (topG i)) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  rw [topMax_grpOf] at hd
  rw [if_pos hd] at hp
  simp only [hn,decide_false,Bool.false_eq_true,if_false] at hp
  exact rOK_eq hp
theorem chk_rung (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<51)
    (hm : c.dig i < m) (hm2 : m ≤ last i) :
    vrun (c.rungPc i m) 3=some (rungR m (if m=last i then some (termSlot i) else none) (c.rungPc i m)) := by
  have hmx := topMax_bounds i
  by_cases h0 : i%3=0 ∧ i<50
  · have hf := c.groupFacts hds (i/3) (by omega)
    have hn : m < topMax i := by unfold last at hm2; omega
    have hd := dig_lead c hds i h0.2 h0.1
    have hh := List.all_eq_true.mp hf.rungs m
      (List.mem_range'_1.mpr ⟨by rw [hd]; omega,by rw [hd, mx_lead i h0.2]; omega⟩)
    rw [lead_q i h0.1, mx_lead i h0.2, hd] at hh
    have hr : c.rungPc i m=gbase (i/3) (c.kOf (i/3))+2*(c.dig i+1)+2*(m-(c.dig i+1)) := by
      rw [c.rungPc_lead i m h0.2 h0.1]; omega
    have ht : (m+1=topMax i) ↔ m=last i := by unfold last; omega
    simpa only [hr,ht] using rOK_eq hh
  · have hp := c.part_at hds i hi h0
    have hT : topMax i=mx (grpOf i) := topMax_grpOf i
    have hn : c.dig i < mx (grpOf i) := by rw [← hT]; unfold last at hm2; omega
    unfold partOK at hp
    rw [if_neg (by omega),Bool.and_eq_true] at hp
    have hh := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega,by rw [← hT]; unfold last at hm2; omega⟩)
    have hr : c.rungPc i m=c.startPc i+5+2*(m-(c.dig i+1)) := by
      unfold rungPc
      rw [if_neg h0,if_neg (by omega)]
      omega
    have ht : (m+1=mx (grpOf i)) ↔ m=last i := by rw [← hT]; unfold last; omega
    have hts : termSlot i=slot i := by
      unfold termSlot; rw [if_neg (by omega)]
    simpa only [hr,ht,hts] using rOK_eq hh
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
