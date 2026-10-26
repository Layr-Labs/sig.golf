import SigGolfCandidate.Merge044
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge075

-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecks ====
section

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
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodOne ====
section

set_option maxRecDepth 20000
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
theorem map_slot_ite (P : Prop) [Decidable P] (a : Nat) :
    (if P then some a else none).map slotOffset = (if P then some (slotOffset a) else none) := by
  split <;> rfl
theorem rungR_keeps (d : Nat) (sl : Option Nat) (p : Nat) : Keeps (rungR d sl p) [.x12] :=
  T3M.rungRB_keeps d (sl.map slotOffset) p
theorem copyN_keeps (rb : Reg) (o : Word) (sl tgt : Nat) (g : Bool := false) : Keeps (copyN rb o sl tgt g) [.x3,.x14] :=
  T3M.copyNB_keeps rb o (slotOffset sl) tgt g
theorem copyFH_keeps (rb : Reg) (o : Word) (sl p : Nat) (g : Bool := false) : Keeps (copyFH rb o sl p g) [.x3,.x14] :=
  T3M.copyFHB_keeps rb o (slotOffset sl) p g
theorem headRH_keeps (rb : Reg) (o : Word) (d : Nat) (sl : Option Nat) (p i : Nat) (g : Bool := false) :
    Keeps (headRH rb o d sl p i g) [.x10,.x12,.x25] :=
  T3M.headRHB_keeps rb o d (sl.map slotOffset) p i g
def copyMem (rb : Reg) (o : Word) (sl : Nat) (g : Bool := false) : SymMem := T3M.copyMemB rb o (slotOffset sl) g
theorem tailR_keeps (slot : Option Nat) (p : Nat) : Keeps (tailR slot p) [.x12] := by
  intro x hx
  simp only [tailR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem bufferAdd_eval {s : MachineState} (h4 : s.getReg .x4=24704) (i : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 (slotOffset (slot i)))).eval s = BitVec.ofNat 64 (slot i) := by
  rw [addC_eval]; simp only [E.eval,h4]
  rw [show (24704 : Word)=BitVec.ofNat 64 24704 from rfl,ofNat_add_ofNat]
  rw [show 24704+slotOffset (slot i)=slot i by unfold slotOffset slot; split <;> omega]
/-- T51: the terminal step's destination `termSlot i` (chain 0: `slot 0 - 16`). -/
theorem termAdd_eval {s : MachineState} (h4 : s.getReg .x4=24704) (i : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 (slotOffset (termSlot i)))).eval s = BitVec.ofNat 64 (termSlot i) := by
  rw [addC_eval]; simp only [E.eval,h4]
  rw [show (24704 : Word)=BitVec.ofNat 64 24704 from rfl,ofNat_add_ofNat]
  rw [show 24704+slotOffset (termSlot i)=termSlot i by unfold slotOffset termSlot slot; split_ifs <;> omega]
theorem bufferAddr_eval {s : MachineState} (h4 : s.getReg .x4=24704) (i k : Nat) :
    (⟨some (.reg .x4),BitVec.ofNat 64 (slotOffset (slot i)+k)⟩ : Addr).eval s = BitVec.ofNat 64 (slot i+k) := by
  simp only [Addr.eval,E.eval,h4]
  rw [show (24704 : Word)=BitVec.ofNat 64 24704 from rfl,ofNat_add_ofNat]
  congr 1; unfold slotOffset slot; split <;> omega
theorem prehash_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : i < 51) (hm : m ≤ last i) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputL 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i)) ∧
      ∀ a : BitVec 256,
        (m < last i → c.StepInv s0 i acc (m + 1) (Verify.vHalf (topHigh i m) a) (writeHash t a)) ∧
        (m = last i → c.EndInv s0 i (acc ++ [Verify.vHalf (topHigh i m) a]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi
  have ho := c.oAt_props hc i hi
  have hva := c.vAt_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide +kernel)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide +kernel)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · have hts := termSlot_props i hi
    apply hashArgs_const t (c.blk i) 64 (if m = last i then termSlot i else c.oAt i) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm2 => ?_, fun hm2 => ?_⟩
    · have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.oAt i) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; exact h)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.oAt i ≤ A ∧ A < c.oAt i + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      have hhdr : c.oAt i + 32 ≤ c.blk i + 16 ∨ c.blk i + 32 ≤ c.oAt i := by unfold oAt; omega
      have hnew : DigAt (writeHash t a) (c.vAt i) (Verify.vHalf (topHigh i m) a) := by
        have hth : topHigh i m = topG i := by unfold topHigh; simp [show m + 1 < topMax i by omega]
        rw [hth]
        cases hg : topG i
        · rw [(c.oAt_F hc i hi hg).symm, Verify.vHalf_false]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
        · rw [(c.oAt_G hc i hi hg).symm, Verify.vHalf_true]
          exact DigAt.writeHash_hi t a _ d12 (by omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        ⟨?_, ?_, ?_⟩, hnew,
        by rw [getReg_writeHash]; exact h10, fun _ => by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slot_props j (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16]
        exact (c.w0_low i m hi (by omega)).1
      · rw [fget _ (by omega) (by omega), h16]
        exact (c.w0_low i m hi (by omega)).2
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    · subst hm2
      have hts := termSlot_props i hi
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (termSlot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        rcases h with h | h
        · exact c.WrIn_next hc i A hi h
        · exact c.Wr_hash i A (by omega) h.1 h.2)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen], ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slot_props j (by omega)
          have hi0 : 0 < i := by omega
          have hmono : slot j + 16 ≤ termSlot i := by
            rw [hts.2.2.2.2 hi0]; unfold slot; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
          by_cases hi0 : i = 0
          · subst hi0
            have hth : topHigh 0 (last 0) = true := by unfold topHigh; simp [topG]
            rw [hth, Verify.vHalf_true, ← hts.2.2.2.1 rfl]
            exact DigAt.writeHash_hi t a _ d12 (by omega)
          · have hth : topHigh i (last i) = false := by
              unfold topHigh; simp [show ¬ (last i + 1 < topMax i) by omega, hi0]
            rw [hth, Verify.vHalf_false, ← hts.2.2.2.2 (by omega)]
            exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd3 : c.dig i < topMax i := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end hds i hi hd3, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
theorem rung_piece (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i < 51) (hm : m ≤ last i) (hp : p < 257181)
    (hrun : vrun p 3 = some (rungR m (if m = last i then some (termSlot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (termSlot i)) ∧ (m < last i → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = last i then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have h4 : s.getReg .x4 = 24704 := (hR _ (by decide +kernel)).trans (hk (.x4,24704) (by simp [known]))
  set r := rungR m (if m = last i then some (termSlot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 17⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (17 : Word) = BitVec.ofNat 64 17 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB])
  have hn : r.steps = (if m = last i then 2 else 1) ∧ r.cycles = (if m = last i then 2 else 1) := by
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = last i then some (termSlot i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 1 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR i m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide +kernel)]; exact termAdd_eval h4 i
  · rw [Result.toState_getReg]
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB, if_neg (show m ≠ last i by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have hp := c.prefix_props
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1
    unfold w0
    omega
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB]
    by_cases h2 : m = last i <;> simp [h2, E.eval]
theorem tail_piece (i m p : Nat) (hp : p < 257181)
    (hrun : vrun p 2 = some (tailR (if m = last i then some (termSlot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (h4 : s.getReg .x4=24704) :
    ∃ t, Steps vimage s (if m = last i then 1 else 0) (if m = last i then 1 else 0) t ∧
      fetch vimage t = some (.base .ECALL) ∧ (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (termSlot i)) ∧ (m ≠ last i → t.getReg .x12 = s.getReg .x12) ∧
      Frame s t (fun _ => False) ∧ t.pc = pcOf (p + (if m = last i then 1 else 0)) := by
  set r := tailR (if m = last i then some (termSlot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by simp [hr, tailR]
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, tailR])
  have hn : r.steps = (if m = last i then 1 else 0) ∧ r.cycles = (if m = last i then 1 else 0) := by
    simp only [hr, tailR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := tailR_keeps (if m = last i then some (termSlot i) else none) p
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_,
    fun A hA _ => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide +kernel)]; exact termAdd_eval h4 i
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_neg h2]
    rw [RegFile.init_get_eval]
  · rw [Result.toState_getMem]; simp [hr, tailR, memEval]
  · rw [Result.toState_pc]; simp only [hr, tailR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]
theorem rung_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : i < 51) (hm : m ≤ last i) (hp : c.rungPc i m < 257181)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = last i then some (termSlot i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hva := c.vAt_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi hm hp hrun s hpc hR h10 hH
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide +kernel)]; exact h10
  · by_cases h2 : m = last i
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), h12 (by omega), if_neg h2]
  · rw [hpc']
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem kAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 51) (k : Nat) (hk : k ≤ 80) : (kAt .x8 (off i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h19]
  exact c.base_off hc i hi k hk
theorem lAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 51) (k : Nat) (hk : k ≤ 80) :
    (lAt .x8 (off i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h19]
  rw [c.base_off hc i hi k hk]
theorem header_load (c : NCtx) {s : MachineState} (i d : Nat)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (c.prefix + 385)) :
    (hLoad i d).eval s = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * d) := by
  simp only [hLoad, addC_eval, E.eval, h28]
  have e : BitVec.ofNat 64 (c.prefix + 385) = BitVec.ofNat 64 c.prefix + BitVec.ofNat 64 385 := by
    rw [ofNat_add_ofNat]
  rw [e, show ∀ x y z : Word, x + z + (y - z) = x + y from fun x y z => by bv_omega, ofNat_add_ofNat]
  congr 1
  unfold w0
  omega
theorem padHeader_at {c : NCtx} {s0 s : MachineState} (hc : c.ok) (h0 : c.Orig0 s0)
    {i : Nat} (hi : i < 51) (hF : Frame s0 s (c.Wr i)) :
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i := by
  have hb := c.blk_props hc i hi
  have ho := orig_frame hF h0 hc hi (k := 3) (by omega) (c.notWr_block hc hi (by omega) (by omega))
  change s.getMem (BitVec.ofNat 64 (c.blk i + 24)) =
    c.w.extractLsb' (8 * (c.blk i + 24 - Verify.WIT)) 64 at ho
  rw [ho, padHeader, wdig_hi]
  rw [show c.blk i + 24 - Verify.WIT = c.blk i - Verify.WIT + 16 + 8 by omega]
theorem vAt_gVal (c : NCtx) (i : Nat) (hi : i < 51) : c.vAt i = c.blk i + gVal (topG i) := by
  rw [topG_lt i hi]; unfold vAt gVal; by_cases h : i % 2 = 0 <;> simp [h] <;> omega
theorem copy_mem (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (h4 : s.getReg .x4=24704) (i : Nat)
    (hi : i < 51) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x8 (off i) (slot i) (topG i)) (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slot_props i hi
  have hg : gVal (topG i) ≤ 48 := by unfold gVal; split <;> omega
  unfold copyMem T3M.copyMemB
  rw [memEval_two s _ _ _ _ (slot i + 8) (slot i) A (bufferAddr_eval h4 i 8) (by simpa using bufferAddr_eval h4 i 0) (by omega) (by omega) hA,
    c.lAt_eval hc h19 i hi (gVal (topG i) + 8) (by omega), c.lAt_eval hc h19 i hi (gVal (topG i)) (by omega),
    c.vAt_gVal i hi,
    show c.blk i + gVal (topG i) + 8 = c.blk i + (gVal (topG i) + 8) by ring]
theorem copy_obl (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3)
    (h4 : s.getReg .x4=24704) (i : Nat) (hi : i < 51) :
    ∀ o ∈ T3M.copyOblB .x8 (off i) (slotOffset (slot i)) (topG i), o.holds s := by
  have hb := c.blk_props hc i hi
  have hs := slot_props i hi
  have hva := c.vAt_props hc i hi
  have ev := c.vAt_gVal i hi
  have hg : gVal (topG i) ≤ 48 := by unfold gVal; split <;> omega
  simp only [T3M.copyOblB,T3M.copyObl,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro o (rfl | rfl | rfl | rfl)
  · show accessValid _ 8=true
    rw [bufferAddr_eval h4 i 8]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid _ 8=true
    have he := bufferAddr_eval h4 i 0
    simp only [Nat.add_zero] at he
    rw [he]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x8 (off i) (gVal (topG i) + 8)).eval s) 8=true
    rw [c.kAt_eval hc h19 i hi (gVal (topG i) + 8) (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x8 (off i) (gVal (topG i))).eval s) 8=true
    rw [c.kAt_eval hc h19 i hi (gVal (topG i)) (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
theorem copy_post (c : NCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : i < 51) (acc : List Digest) (hlen : acc.length = i) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
    (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (h4 : s.getReg .x4=24704)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      memEval s (copyMem .x8 (off i) (slot i) (topG i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slot j) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi
  have hs := slot_props i hi
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h19 h4 i hi A hA)
  have hfr : Frame s t (fun A => A = slot i + 8 ∨ A = slot i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    rcases h with h | h
    · exact c.Wr_mono i A h
    · exact c.Wr_copy i A (by omega) (by omega)
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slot_props j (by omega)
      have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2
theorem copyN_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51)
    (hp0 : c.startPc i < 257181)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x8 (off i) (slot i) (c.endPc i) (topG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyN .x8 (off i) (slot i) (c.endPc i) (topG i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyN, T3M.copyNB] using c.copy_obl hc h19 h4 i hi)
  have hkeep := copyN_keeps .x8 (off i) (slot i) (c.endPc i) (topG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19 h4
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; rfl
theorem copyFH_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hp0 : c.startPc i < 257181)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x8 (off i) (slot i) (c.startPc i) (topG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyFH .x8 (off i) (slot i) (c.startPc i) (topG i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyFH, T3M.copyFHB] using c.copy_obl hc h19 h4 i hi)
  have hkeep := copyFH_keeps .x8 (off i) (slot i) (c.startPc i) (topG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19 h4
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, T3M.copyFHB, E.eval]; rw [hend]
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
theorem headJD_keeps (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) :
    Keeps (headJD rb o tgt i d g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJD]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headJDTerm_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJDTerm rb o tgt i d) [.x10, .x25] := by
  intro x hx
  simp only [headJDTerm]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem headJ_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 257181) (hp1 : c.rungPc i (c.dig i) + 1 < 257181)
    {f n : Nat} {st : Stop}
    (hrun1 : vrun (c.startPc i) f =
      some {headJD .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) (topG i) with stop := st, steps := n, cycles := n})
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (termSlot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s n n t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := {headJD .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) (topG i) with stop := st, steps := n, cycles := n}
    with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJD, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJD_keeps .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) (topG i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.oAt i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel), addC_eval, a0e]
    exact c.oAt_eval hc i hi _ rfl
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJD]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, -, h12b, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1 ((hR1 _ (by decide +kernel)).trans (hk (.x4,24704) (by simp [known])))
  have hsteps : r.steps = n ∧ r.cycles = n := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hn : c.dig i ≠ last i := by omega
  rw [if_neg hn] at hst2
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega)]
    exact padHeader_at hc h0 hi hF
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide +kernel)]; exact t10
  · rw [h12b hn, t12, if_neg hn]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)
theorem headJTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 257181) (hp1 : c.rungPc i (c.dig i) + 1 < 257181)
    {f n : Nat} {st : Stop}
    (hrun1 : vrun (c.startPc i) f =
      some {headJDTerm .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with stop := st, steps := n, cycles := n})
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (termSlot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (n + 1) (n + 1) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := {headJDTerm .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with stop := st, steps := n, cycles := n}
    with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJDTerm, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJDTerm_keeps .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJDTerm]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel), a0e]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJDTerm]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, -, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1 ((hR1 _ (by decide +kernel)).trans (hk (.x4,24704) (by simp [known])))
  have hsteps : r.steps = n ∧ r.cycles = n := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  rw [if_pos hd] at hst2
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega)]
    exact padHeader_at hc h0 hi hF
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide +kernel)]; exact t10
  · rw [h12a hd, if_pos hd]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
theorem headRHT_keeps (rb : Reg) (o : Word) (d sl p i : Nat) :
    Keeps (headRHT rb o d sl p i) [.x10, .x12, .x25] :=
  headRH_keeps rb o d (some sl) p i
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem headR_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 257181) (hrp : c.rungPc i (c.dig i) = c.startPc i + 3)
    (hrun : vrun (c.startPc i) 8 = some (headRH .x8 (off i) (c.dig i) none (c.startPc i) i (topG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := headRH .x8 (off i) (c.dig i) none (c.startPc i) i (topG i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, Option.map_none, T3M.headRHB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRH, Option.map_none, T3M.headRHB])
  have hn : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x8 (off i) (c.dig i) none (c.startPc i) i (topG i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else if A = c.blk i + 24 then c.padHeader i else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH, Option.map_none, T3M.headRHB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
    have hpad := padHeader_at hc h0 hi hF
    split_ifs <;> simp_all
  have hpad0 := padHeader_at hc h0 hi hF
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
    split_ifs with h24
    · rw [h24]; exact hpad0.symm
    · rfl
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRH, Option.map_none, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_getReg]; simp only [hr, headRH, Option.map_none, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    simp only [h2, if_false]
    rw [addC_eval, a0e]
    exact c.oAt_eval hc i hi _ rfl
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_pc]; simp only [hr, headRH, Option.map_none, T3M.headRHB, hrp]
    simp [h2, E.eval]
theorem headRTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 257181) (hrp : c.rungPc i (c.dig i) = c.startPc i + 2)
    (hrun : vrun (c.startPc i) 8 =
      some (headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i)) (hi0 : i ≠ 0)
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hts : termSlot i = slot i := by unfold termSlot; rw [if_neg hi0]
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRHT, headRH, Option.map_some, T3M.headRHB])
  have hn : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRHT_keeps .x8 (off i) (c.dig i) (slot i) (c.startPc i) i
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else if A = c.blk i + 24 then c.padHeader i else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
    have hpad := padHeader_at hc h0 hi hF
    split_ifs <;> simp_all
  have hpad0 := padHeader_at hc h0 hi hF
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
    split_ifs with h24
    · rw [h24]; exact hpad0.symm
    · rfl
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    simpa only [hd,if_true,hts] using bufferAdd_eval h4 i
  · rw [Result.toState_pc]; simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB, hrp]
    simp [hd, E.eval]
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 800000
theorem baseTab_all : (baseTab.all fun x => decide (x<256000))=true := by decide +kernel
theorem body6Tab_all : (body6Tab.all fun x => decide (x<256000))=true := by decide +kernel
theorem body7Tab_all : (body7Tab.all fun x => decide (x<256000))=true := by decide +kernel
theorem getD_lt256 (l : List Nat) (n : Nat) (h : (l.all fun x => decide (x<256000))=true) : l.getD n 0<256000 := by
  rw [List.getD_eq_getElem?_getD]
  cases hn : l[n]? with
  | none => simp
  | some x => simpa using List.all_eq_true.mp h x (List.mem_of_getElem? hn)
theorem base_lt (q dB dC : Nat) : base q dB dC<256000 := by
  unfold base body6
  split_ifs
  · exact getD_lt256 _ _ body6Tab_all
  · exact getD_lt256 _ _ baseTab_all
  · exact getD_lt256 _ _ body7Tab_all
  · exact getD_lt256 _ _ baseTab_all
theorem mx_bounds (q : Nat) : 3≤ mx q ∧ mx q≤7 := by unfold mx; split_ifs <;> omega
theorem partLen_ge (q d : Nat) : 4 ≤ partLen q d := by
  have hm := mx_bounds q
  unfold partLen
  split_ifs <;> omega
theorem partLen_rung (q d : Nat) (hd : d < mx q) : 2*(mx q-d)+3 ≤ partLen q d := by
  unfold partLen
  split_ifs <;> omega
theorem partLen_le (q d : Nat) : partLen q d≤18 := by
  have hm := mx_bounds q
  unfold partLen
  split_ifs <;> omega
theorem kdig_le (q k j : Nat) : kdig q k j ≤ mx q := by
  have := mx_bounds q
  unfold kdig; have := Nat.mod_lt (k/(mx q+1)^j) (show 0 < mx q+1 by omega); omega
theorem inl_q (q k : Nat) (h : rowInl q k=true) : q<16 := rowInl_lt q k h
/-- Inline rows are #938's r5 rows (groups 9..15). -/
theorem leadPc_top_bounds (q k : Nat) (h9 : 9 ≤ q) (hq : q<16) (hk : k<125) :
    leadPc q k ≤ 129600 ∧ 64 ≤ leadPc q k := by
  have hu := entOff_le q (by omega)
  have hl := entOff_ge q
  unfold leadPc leadOff entW cellW
  rw [if_neg (by omega), if_pos hq]
  split_ifs <;> omega
/-- T51: every group cell (r6 rank < 216, r5 rank < 125, r7 rank < 49) sits below word 226812 (the checksum chain 50
starts at its arm `ckArm`, not at a group cell). -/
theorem leadPc_le (q k : Nat) (hq : q<17) (hk : k<nRank q) : leadPc q k ≤ 226811 := by
  by_cases h9 : q<9
  · have hk6 : k<216 := by unfold nRank mx at hk; rw [if_neg (by omega), if_pos h9] at hk; norm_num at hk; exact hk
    unfold leadPc leadOff entW cellW cell6 rawOf6 r6Off r6B
    rw [if_pos h9]
    split_ifs <;> omega
  · by_cases h16 : q=16
    · subst h16
      have hk7 : k<49 := by unfold nRank at hk; simpa using hk
      unfold leadPc leadOff entW cellW entOff
      simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]
      split_ifs <;> omega
    · have hk5 : k<125 := by
        unfold nRank mx at hk; rw [if_neg h16, if_neg h9, if_pos (by omega)] at hk; norm_num at hk; exact hk
      have := leadPc_top_bounds q k (by omega) (by omega) hk5; omega
theorem group_bounds (q k : Nat) (hq : q<17) (hk : k<nRank q) :
    gbase q k+2*mx q+2<257181 ∧ gX q k+4<257181 ∧ leadPc q k<257181 ∧
      (rowInl q k=true → gbase q k+5 ≤ leadPc q k+8) := by
  have hm := mx_bounds q
  have h1 := partLen_le q (kdig q k 1)
  have h2 := partLen_le q (kdig q k 2)
  have hk0 := kdig_le q k 0
  have hl := leadPc_le q k hq hk
  unfold gX gC gB
  cases hn : rowInl q k
  · have hb := base_lt q (kdig q k 1) (kdig q k 2)
    simp only [gbase,hn,Bool.false_eq_true,if_false]
    refine ⟨by omega,by split_ifs <;> omega,by omega,fun h => absurd h (by simp)⟩
  · have hq' := inl_q q k hn
    have h9 := rowInl_ge q k hn
    have hk5 : k<125 := by rw [nRank_rowInl q k hn] at hk; exact hk
    have hl2 := leadPc_top_bounds q k h9 hq' hk5
    simp only [gbase,hn,if_true]
    refine ⟨?_,?_,by omega,fun _ => ?_⟩ <;> split_ifs <;> omega
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem kOf_bounds (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) : c.kOf q<nRank q :=
  c.kOf_lt_nRank hds q hq
theorem qX_lt (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) : c.qX i+4<257181 :=
  (group_bounds _ _ (by omega) (c.kOf_bounds hds (i/3) (by omega))).2.1
theorem ckArm_room (d : Nat) (hd : d ≤ 7) : ckArm d+partLen 17 d+5<257181 := by
  have := partLen_le 17 d
  unfold ckArm; omega
theorem startPc_50 (c : NCtx) : c.startPc 50=ckArm (c.dig 50) := by simp [startPc]
theorem ck_end_lt (c : NCtx) (hds : c.DigitsOk) : c.startPc 50+partLen 17 (c.dig 50)+5<257181 := by
  have h5 := hds 50 (by omega)
  rw [topMax_50] at h5
  rw [c.startPc_50]; exact ckArm_room (c.dig 50) (by omega)
theorem startPc_room (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) : c.startPc i<256150 := by
  have h1 := c.kOf_bounds hds (i/3) (by omega)
  have hl := leadPc_le (i/3) (c.kOf (i/3)) (by omega) h1
  have hb := base_lt (i/3) (kdig (i/3) (c.kOf (i/3)) 1) (kdig (i/3) (c.kOf (i/3)) 2)
  have hm := mx_bounds (i/3)
  have hp := partLen_le (i/3) (kdig (i/3) (c.kOf (i/3)) 1)
  have hbase : gbase (i/3) (c.kOf (i/3))<256050 := by unfold gbase; split_ifs <;> omega
  unfold startPc qB qC gC gB
  rw [if_pos hi]
  split_ifs <;> omega
theorem startPc_lt (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) : c.startPc i<257181 := by
  by_cases h50 : i<50
  · have := c.startPc_room hds i h50; omega
  · have := c.ck_end_lt hds
    rw [show i=50 by omega]; omega
theorem last_50 : last 50=4 := by unfold last; rw [topMax_50]
theorem rungPc_lt (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<51) (hm : m≤ last i) :
    c.rungPc i m+2<257181 := by
  by_cases h50 : 50 ≤ i
  · obtain rfl : i=50 := by omega
    have he := c.ck_end_lt hds
    have hd := hds 50 (by omega)
    rw [topMax_50] at hd
    rw [last_50] at hm
    have hr : c.rungPc 50 m=c.startPc 50+(if c.dig 50=last 50 then 2 else 3)+2*(m-c.dig 50) := by
      unfold rungPc; simp
    rw [hr, last_50]
    unfold partLen mx at he
    simp only [show ¬ (17:Nat)<9 by decide, show ¬ (17:Nat)<16 by decide, show ¬ (17:Nat)=16 by decide,
      if_false] at he
    split_ifs at he ⊢ <;> omega
  have hs := c.startPc_room hds i (by omega)
  have h1 := c.kOf_bounds hds (i/3) (by omega)
  obtain ⟨b1,-,-,-⟩ := group_bounds _ _ (by omega) h1
  have hl := last_bounds i
  have hmx := mx_bounds (i/3)
  have hlm : last i+1=mx (i/3) := by unfold last; rw [topMax_mx i (by omega)]; omega
  unfold rungPc qb
  split_ifs <;> omega
theorem inline_rungPc (c : NCtx) (i : Nat) (h0 : ¬ (i%3=0 ∧ i<50)) :
    c.rungPc i (c.dig i)=c.startPc i+(if c.dig i=last i then 2 else 3) := by
  simp [rungPc,h0]
theorem skipA_eq (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    skipA q (c.kOf q)=decide (c.bufferSafe (3*q)) := by
  obtain ⟨k1,-,-⟩ := c.kdig_kOf' hds q hq
  by_cases h0 : q=0
  · subst h0
    simp [skipA,k1,bufferSafe,topMax,and_comm]
  · simp [skipA,h0,bufferSafe,show 3*q≠0 by omega]
theorem inline_max_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : ¬ (i%3=0 ∧ i<50))
    (hd : c.dig i=topMax i) : c.startPc i+4-(if c.bufferSafe i then 4 else 0)=c.endPc i := by
  by_cases h50 : i<50
  · have hn0 : i%3≠0 := fun h => h0 ⟨h,h50⟩
    obtain ⟨-,k2,k3⟩ := c.kdig_kOf' hds (i/3) (by omega)
    have hdm : c.dig i=mx (i/3) := by rw [hd, topMax_mx i h50]
    by_cases h1 : i%3=1
    · have ei : 3*(i/3)+1=i := by omega
      have he := c.skipB_eq hds (i/3) (by omega)
      rw [ei] at he k2
      simp only [startPc,endPc,h50,hn0,h1,if_true,if_false,qB,qC,gC,k2,he,decide_eq_true_eq]
      simp [partLen,hdm]
    · have ei : 3*(i/3)+2=i := by omega
      have h16 : i/3≠16 := by omega
      have he := c.skipC_eq hds (i/3) (by omega)
      have k3 := k3 h16
      rw [ei] at he k3
      simp only [startPc,endPc,h50,hn0,h1,if_true,if_false,qC,qX,gX,k3,he,decide_eq_true_eq,h16]
      simp [partLen,hdm]
  · obtain rfl : i=50 := by omega
    have hd5 : c.dig 50=5 := hd.trans topMax_50
    simp [startPc,endPc,ckTail,partLen,hd5,mx,bufferSafe]
theorem inline_copy_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : ¬ (i%3=0 ∧ i<50))
    (hd : c.dig i=topMax i) (hn : ¬ c.bufferSafe i) : c.startPc i+4=c.endPc i := by
  simpa [hn] using c.inline_max_end hds i hi h0 hd
theorem lead_max_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : i%3=0) (h50 : i<50)
    (hn : rowInl (i/3) (c.kOf (i/3))=true)
    (hd : c.dig i=topMax i) : c.startPc i+4-(if c.bufferSafe i then 4 else 0)=c.endPc i := by
  obtain ⟨k1,-,-⟩ := c.kdig_kOf' hds (i/3) (by omega)
  have ei : 3*(i/3)=i := by omega
  have e0 : c.dig (3*(i/3))=c.dig i := by rw [ei]
  have hm := mx_bounds (i/3)
  have h9 := rowInl_ge (i/3) (c.kOf (i/3)) hn
  have h16 := rowInl_lt (i/3) (c.kOf (i/3)) hn
  have hk := c.kOf_bounds hds (i/3) (by omega)
  have hk5 : c.kOf (i/3)<125 := by rw [nRank_rowInl _ _ hn] at hk; exact hk
  have hs : c.startPc i=leadPc (i/3) (c.kOf (i/3)) := by simp [startPc,h0,h50]
  have he : c.endPc i=gB (i/3) (c.kOf (i/3)) := by simp [endPc,qB,h0,h50]
  have hdm : kdig (i/3) (c.kOf (i/3)) 0=mx (i/3) := by rw [k1,e0,hd,topMax_mx i h50]
  have hg : gbase (i/3) (c.kOf (i/3))=leadPc (i/3) (c.kOf (i/3))+3-2*mx (i/3) := by simp [gbase,hn,hdm]
  have hlo : 64 ≤ leadPc (i/3) (c.kOf (i/3)) := (leadPc_top_bounds _ _ h9 h16 hk5).2
  have hskip := c.skipA_eq hds (i/3) (by omega)
  rw [ei] at hskip
  have hsh : sharedG (i/3)=false := by simp [sharedG]; omega
  rw [hs,he]
  simp only [gB,hg,hskip,decide_eq_true_eq,hsh,Bool.false_eq_true,if_false]
  omega
theorem lead_copy_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : i%3=0) (h50 : i<50)
    (hr : rowInl (i/3) (c.kOf (i/3))=true)
    (hd : c.dig i=topMax i) (hn : ¬ c.bufferSafe i) : c.startPc i+4=c.endPc i := by
  simpa [hn] using c.lead_max_end hds i hi h0 h50 hr hd
/-- T51 (as R6): a buffer-safe chain other than chain 0 is skipped in place (chain 0 is the g0 cell's `jal`). -/
theorem bufferSafe_pc (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (hs : c.bufferSafe i) (hiz : i≠0) :
    c.startPc i=c.endPc i := by
  have ht : ¬ (i%3=0 ∧ i<50) := by
    rintro ⟨h0,-⟩; rcases hs.2 with hz | hz; exact hiz hz; exact hz.2.1 h0
  simpa [hs] using c.inline_max_end hds i hi ht hs.1
/-- The buffer-safe end-state bookkeeping (registers, frame, slots) before any pc update. -/
theorem buffer_skip_base (c : NCtx) (hc : c.ok) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (i : Nat) (hi : i<51) (hz : c.bufferSafe i) (acc : List T3.Digest) (hB : c.ChainIn s0 i acc s) :
    c.Base s0 (c.Wr (i+1)) (acc++[c.bufferVal i]) s ∧ (acc++[c.bufferVal i]).length=i+1 ∧ True := by
  obtain ⟨⟨hR,hF,hA⟩,hlen,hpc⟩ := hB
  have hb := c.blk_props hc 0 (by decide +kernel)
  refine ⟨⟨hR,hF.mono (fun A _ h => c.Wr_mono i A h),?_⟩,by simp [hlen],trivial⟩
  intro j hj
  rw [List.length_append,List.length_singleton] at hj
  by_cases hl : j<acc.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hl,← List.getD_eq_getElem?_getD]
    exact hA j hl
  · have hj' : j=acc.length := by omega
    subst hj'
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl _),Nat.sub_self,hlen]
    exact bufferVal_at h0.1.2 hi hz (by rw [slot0]; unfold blk at hb; omega) hF
theorem buffer_skip (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (i : Nat) (hi : i<51) (hz : c.bufferSafe i) (hiz : i≠0) (acc : List T3.Digest) (hB : c.ChainIn s0 i acc s) :
    Steps vimage s 0 0 s ∧ c.EndInv s0 i (acc++[c.bufferVal i]) s := by
  obtain ⟨hb1,hb2,-⟩ := c.buffer_skip_base hc s0 s h0 i hi hz acc hB
  obtain ⟨-,-,hpc⟩ := hB
  refine ⟨Steps.refl _, hb1, hb2, ?_⟩
  rw [hpc,c.bufferSafe_pc hds i hi hz hiz]
/-- T51 (as R6): chain 0 at its largest digit (always buffer-safe) is the g0 cell's single `jal` to chain B. -/
theorem skip0_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (hz : c.bufferSafe 0) (acc : List T3.Digest) (hB : c.ChainIn s0 0 acc s) :
    ∃ t, Steps vimage s 1 1 t ∧ c.EndInv s0 0 (acc++[c.bufferVal 0]) t := by
  have hsk := c.buffer_skip_base hc s0 s h0 0 (by omega) hz acc hB
  obtain ⟨⟨hR,hF,hA⟩,hlen,hpc⟩ := hB
  have hrun := c.chk_skipJ hds hz.1
  have hp0 := c.startPc_lt hds 0 (by omega)
  have hst := piece_steps45 hrun hp0 s hpc (by simp [T3M.skipJB, SymState.init])
  have hreg : ∀ x, ((T3M.skipJB (c.endPc 0)).toState s).getReg x = s.getReg x := by
    intro x
    rw [Result.toState_getReg]
    change (RegFile.get RegFile.init x).eval s = _
    rw [RegFile.init_get_eval]
  have hmem : ∀ a, ((T3M.skipJB (c.endPc 0)).toState s).getMem a = s.getMem a := by
    intro a; simp [T3M.skipJB, SymState.init, Result.toState_getMem, memEval]
  have hfr : Frame s ((T3M.skipJB (c.endPc 0)).toState s) (fun _ => False) := fun A _ _ => hmem _
  obtain ⟨⟨hR',hF',hA'⟩,hlen',-⟩ := hsk
  refine ⟨_, hst, ⟨⟨fun x hx => (hreg x).trans (hR' x hx), (hF'.trans hfr).mono (fun A _ h => by
    rcases h with h|h; exact h; exact h.elim), fun j hj => ?_⟩, hlen', ?_⟩⟩
  · exact ⟨(hmem _).trans (hA' j hj).1, (hmem _).trans (hA' j hj).2⟩
  · rw [Result.toState_pc]; rfl
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem chainInputL_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) :
    pad64 (chainInputL lay tree leaf i step p0 p1 headerPad v g) = chainInputL lay tree leaf i step p0 p1 headerPad v g :=
  pad64_of_aligned _ (by rw [chainInputL_length])
theorem chainInputL_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : (toQ (chainInputL lay tree leaf i step p0 p1 headerPad v g)).blocks = 1 := by
  rw [blocks_toQ ⟨by rw [chainInputL_length]; omega, by rw [chainInputL_length]⟩, chainInputL_length]
/-- The image's chain run from step `m` (G chains keep the high half of their interior steps, `topHigh`). -/
def rest (c : NCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (topMax i-m)).foldlM
    (fun v step => Verify.vHash (topHigh i step)
      (chainInputL 0 c.tree c.leaf i step (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i))) v
theorem rest_succ (c : NCtx) (i m : Nat) (h : m ≤ last i) (v : Digest) :
    c.rest i m v=Verify.vHash (topHigh i m)
      (chainInputL 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i)) >>= c.rest i (m+1) := by
  have hm := topMax_bounds i
  unfold last at h
  unfold rest
  rw [show topMax i-m=(topMax i-(m+1))+1 by omega,List.range'_succ,List.foldlM_cons]
theorem rest_max (c : NCtx) (i : Nat) (v : Digest) : c.rest i (topMax i) v=pure v := by
  simp [rest]
/-- The image's projected hash is the spec's `WCT9.halfHash`. -/
theorem topVHash_eq (high : Bool) (input : List UInt8) :
    Verify.vHash high input = ClaudeWCT.WCT9.halfHash high input := by
  rw [ClaudeWCT.WCT9.halfHash_eq]; unfold Verify.vHash; cases high <;> rfl
/-- The image's top chain run is the spec's `chainPW 0` (G/F pairing, `WCT9.chainHigh 0`). -/
theorem chainPW_rest (c : NCtx) (i d : Nat) (v : Digest) :
    ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i d (topMax i-d) (c.pad0 i) (c.pad1 i) (c.padHeader i) v=c.rest i d v := by
  unfold rest ClaudeWCT.W9.T3M.chainPW
  congr 1
  funext v step
  rw [topVHash_eq, chainInputL_top, topHigh_eq]
def preCost (i m : Nat) : Nat := 8+9*(last i-m)+(if m< last i then 1 else 0)
theorem steps_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<51)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → Verify.GoodQP P t N C Q A (K (acc++[v]))) :
    ∀k m,m+k=last i → c.dig i ≤ m → ∀v s,c.PreHash s0 i acc m v s →
      Verify.GoodQP P s (N+3*(topMax i-m)+5) (C+preCost i m) Q (A+preCost i m)
        (Verify.ccM (c.rest i m v) (fun v => K (acc++[v]))) := by
  have hmax := topMax_bounds i
  have hlast := last_bounds i
  have hlastEq : last i+1=topMax i := by unfold last;omega
  intro k
  induction k with
  | zero =>
      intro m hm hd v s hs
      obtain rfl : m=last i := by omega
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc hds s0 hk h0 i (last i) hi (le_refl _) hd acc v s hs
      rw [rest_succ c i (last i) (le_refl _)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Verify.GoodQP P (writeHash s a) N C Q A
          (Verify.ccM (c.rest i (last i+1) (Verify.vHalf (topHigh i (last i)) a)) (fun v => K (acc++[v]))) := by
        intro a
        rw [hlastEq,rest_max,Verify.ccM_pure]
        exact hK _ _ ((hpost a).2 rfl)
      have h3 := Verify.GoodQP.vHash_bind (topHigh i (last i)) (f:=c.rest i (last i+1)) (K:=fun v => K (acc++[v]))
        hf h5 hv (by rw [chainInputL_pad];exact hin) H
      rw [chainInputL_pad,chainInputL_blocks] at h3
      exact h3.mono (by omega) (by simp [preCost]) (fun hq => ⟨hq,by simp [preCost]⟩)
  | succ k ih =>
      intro m hm hd v s hs
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc hds s0 hk h0 i m hi (by omega) hd acc v s hs
      rw [rest_succ c i m (by omega)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Verify.GoodQP P (writeHash s a) (N+3*(topMax i-(m+1))+5+2)
          (C+preCost i (m+1)+(if m+1=last i then 2 else 1)) Q
          (A+preCost i (m+1)+(if m+1=last i then 2 else 1))
          (Verify.ccM (c.rest i (m+1) (Verify.vHalf (topHigh i m) a)) (fun v => K (acc++[v]))) := by
        intro a
        have hrun := c.chk_rung hds i (m+1) hi (by omega) (by omega)
        obtain ⟨u,hu,hp⟩ := c.rung_step hc hk i (m+1) hi (by omega)
          (by have := c.rungPc_lt hds i (m+1) hi (by omega); omega) hrun acc _ _
          ((hpost a).1 (by omega))
        have ht := ih (m+1) (by omega) (by omega) _ _ hp
        exact Verify.GoodQP.stepsQ hu ht (by split <;> omega) (by omega) (fun hq => ⟨hq,by omega⟩)
      have h3 := Verify.GoodQP.vHash_bind (topHigh i m) (f:=c.rest i (m+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputL_pad];exact hin) H
      rw [chainInputL_pad,chainInputL_blocks] at h3
      refine h3.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem chainCost_positive (c : NCtx) (i d : Nat) (hd : d< topMax i) :
    c.chainCost i d=4+c.tableJump i+preCost i d := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost preCost
  rw [if_neg (by omega)]
  split_ifs <;> omega
theorem positive_head (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<51)
    (hd : c.dig i< topMax i) (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃t,Steps vimage s (4+c.tableJump i) (4+c.tableJump i) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hl : last i+1=topMax i := by have := topMax_bounds i;unfold last;omega
  have hsp := c.startPc_lt hds i hi
  by_cases htab : i%3=0 ∧ i<50
  · have hrun2 := c.chk_tail hds i htab.2 htab.1 hd
    have hrp : c.rungPc i (c.dig i)+1<257181 := by have := c.rungPc_lt hds i (c.dig i) hi (by omega); omega
    cases hn : rowInl (i/3) (c.kOf (i/3))
    · have hj : c.tableJump i=1 := by simp [tableJump,htab,hn]
      by_cases ht : c.dig i=last i
      · have hrun1 := c.chk_headJTerm hds i htab.2 htab.1 hn ht
        obtain ⟨t,hst,htp⟩ := c.headJTerm_step hc hk h0 i hi ht hsp hrp (st := .jump) (n := 4) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
      · have hrun1 := c.chk_headJ hds i htab.2 htab.1 hn (by omega)
        obtain ⟨t,hst,htp⟩ := c.headJ_step hc hk h0 i hi (by omega) hsp hrp (st := .jump) (n := 5) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
    · have hj : c.tableJump i=0 := by simp [tableJump,htab,hn]
      by_cases ht : c.dig i=last i
      · have hrun1 := c.chk_headJTermF hds i htab.2 htab.1 hn ht
        obtain ⟨t,hst,htp⟩ := c.headJTerm_step hc hk h0 i hi ht hsp hrp (st := .fuel) (n := 3) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
      · have hrun1 := c.chk_headJF hds i htab.2 htab.1 hn (by omega)
        obtain ⟨t,hst,htp⟩ := c.headJ_step hc hk h0 i hi (by omega) hsp hrp (st := .fuel) (n := 4) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
  · have hj : c.tableJump i=0 := by simp [tableJump,htab]
    have hiz : i≠0 := fun h => htab ⟨by omega, by omega⟩
    by_cases ht : c.dig i=last i
    · have hrun := c.chk_headRTerm hds i hi htab ht
      have hr : c.rungPc i (c.dig i)=c.startPc i+2 := by rw [inline_rungPc c i htab,if_pos ht]
      obtain ⟨t,hst,htp⟩ := c.headRTerm_step hc hk h0 i hi ht hsp hr hrun hiz acc s hs
      exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
    · have hrun := c.chk_headR hds i hi htab (by omega)
      have hr : c.rungPc i (c.dig i)=c.startPc i+3 := by rw [inline_rungPc c i htab,if_neg ht]
      obtain ⟨t,hst,htp⟩ := c.headR_step hc hk h0 i hi (by omega) hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
theorem tableJump_zero (c : NCtx) : c.tableJump 0=1 := by
  simp [tableJump, rowInl, inl]
theorem chain_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<51)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → Verify.GoodQP P t N C Q A (K (acc++[v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    Verify.GoodQP P s (N+40) (C+c.chainCost i (c.dig i)) Q (A+c.chainCost i (c.dig i))
      (Verify.ccM (ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i)
        (c.padHeader i) (c.bufferVal i)) (fun v => K (acc++[v]))) := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  have hd := hds i hi
  have hsp := c.startPc_lt hds i hi
  by_cases hmax : c.dig i=topMax i
  · rw [hmax,Nat.sub_self]
    have hp : ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (topMax i) 0 (c.pad0 i) (c.pad1 i) (c.padHeader i)
        (c.bufferVal i)=pure (c.bufferVal i) := rfl
    rw [hp,Verify.ccM_pure]
    by_cases hz : c.bufferSafe i
    · by_cases hiz : i=0
      · subst hiz
        obtain ⟨t,hst,ht⟩ := c.skip0_step hc hds s0 s h0 hz acc hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,c.tableJump_zero])
          (fun hq => ⟨hq,by simp [chainCost,hz,c.tableJump_zero]⟩)
      · have hj : c.tableJump i=0 := by
          have : i%3≠0 := by rcases hz.2 with h|h; exact absurd h hiz; exact h.2.1
          simp [tableJump,this]
        obtain ⟨hst,ht⟩ := c.buffer_skip hc hds s0 s h0 i hi hz hiz acc hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,hj])
          (fun hq => ⟨hq,by simp [chainCost,hz,hj]⟩)
    rw [bufferVal,if_neg hz]
    by_cases htab : i%3=0 ∧ i<50
    · cases hn : rowInl (i/3) (c.kOf (i/3))
      · have hiz : i≠0 := fun h => hz (by subst h; exact ⟨hmax, Or.inl rfl⟩)
        obtain ⟨t,hst,ht⟩ := c.copyN_step hc hk h0 i hi hsp
          (c.chk_copyJ hds i htab.2 htab.1 hiz hn hmax) acc s hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,tableJump,htab,hn])
          (fun hq => ⟨hq,by simp [chainCost,hz,tableJump,htab,hn]⟩)
      · have hsA : skipA (i/3) (c.kOf (i/3))=false := by
          rw [c.skipA_eq hds _ (by omega),show 3*(i/3)=i by omega]; simp [hz]
        obtain ⟨t,hst,ht⟩ := c.copyFH_step hc hk h0 i hi hsp
          (c.lead_copy_end hds i hi htab.1 htab.2 hn hmax hz) (c.chk_copyFL hds i htab.2 htab.1 hn hmax hsA) acc s hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,tableJump,htab,hn])
          (fun hq => ⟨hq,by simp [chainCost,hz,tableJump,htab,hn]⟩)
    · obtain ⟨t,hst,ht⟩ := c.copyFH_step hc hk h0 i hi hsp
        (c.inline_copy_end hds i hi htab hmax hz) (c.chk_copyF hds i hi htab hmax hz) acc s hs
      exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,hz,tableJump,htab]⟩)
  · have hd' : c.dig i< topMax i := by omega
    rw [c.bufferVal_nonmax i hmax,chainPW_rest]
    have H := c.steps_good hc hds hk h0 i hi acc K N C A Q hK (last i-c.dig i) (c.dig i) (by omega) (le_refl _)
    obtain ⟨t,hst,ht⟩ := c.positive_head hc hds hk h0 i hi hd' acc s hs
    have hj : c.tableJump i≤1 := by unfold tableJump;split <;> omega
    have he := c.chainCost_positive i (c.dig i) hd'
    exact Verify.GoodQP.stepsQ hst (H _ _ ht) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsDispatchCtx ====
section

section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def sourceWord (v : Digest) (q : Nat) : Word := if q<9 then v.extractLsb' 0 64 else v.extractLsb' 64 64
def sourceBit (q : Nat) : Nat := if q<9 then 7*q else 7*q-64
theorem extract_field (v : Digest) (a b : Nat) (h : b+7≤64) :
    (v.extractLsb' a 64).toNat/2^b%128=v.toNat/2^(a+b)%128 := by
  have hr := Search.ext_shr_mask v a b 7 h
  have hl : (v.extractLsb' a 64 >>> b) &&& 127#64=
      BitVec.ofNat 64 ((v.extractLsb' a 64).toNat/2^b%128) := by
    have he : v.extractLsb' a 64=BitVec.ofNat 64 (v.extractLsb' a 64).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    conv_lhs => rw [he]
    rw [ofNat_shr _ _ (v.extractLsb' a 64).isLt,Search.ofNat_and127]
  have hh := hl.symm.trans hr
  exact (ofNat_inj (by omega) (by omega)).mp hh
theorem source_field (v : Digest) (q : Nat) (hq : q<17) (h9 : q≠9) :
    (sourceWord v q).toNat/2^(sourceBit q)%128=Search.topRank v q := by
  unfold sourceWord sourceBit Search.topRank
  split_ifs with h
  · simpa using extract_field v 0 (7*q) (by omega)
  · rw [extract_field v 64 (7*q-64) (by omega),show 64+(7*q-64)=7*q by omega]
theorem sourceBit_lt (q : Nat) (hq : q<17) (h9 : q≠9) : sourceBit q+7 ≤ 64 := by
  unfold sourceBit; split_ifs <;> omega
def hiMask : Word := BitVec.ofNat 64 (2 ^ 64 - 2 ^ 55)
theorem field_xor_hiMask (X : Word) (b : Nat) (hb : b + 7 ≤ 55) :
    (X ^^^ hiMask).toNat / 2 ^ b % 128 = X.toNat / 2 ^ b % 128 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [show (128 : Nat) = 2 ^ 7 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, BitVec.toNat_xor, Nat.testBit_xor]
  by_cases hj : j < 7
  · have hm : hiMask.toNat.testBit (j + b) = false := by
      unfold hiMask
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num),
        show (2 : Nat) ^ 64 - 2 ^ 55 = 2 ^ 55 * (2 ^ 9 - 1) by norm_num, Nat.testBit_two_pow_mul]
      simp; omega
    simp [hj, hm]
  · simp [hj]
theorem mod64_xor_hiMask (X : Word) : (X ^^^ hiMask).toNat % 64 = X.toNat % 64 := by
  have h := field_xor_hiMask X 0 (by decide +kernel)
  simp only [pow_zero, Nat.div_one] at h
  rw [← Nat.mod_mod_of_dvd (X ^^^ hiMask).toNat (show 64 ∣ 128 by decide +kernel), h,
    Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
theorem dispatch_step {p q : Nat} (hq : q<17) (h9 : q≠9) (hp : p<257181)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64))
    (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask) (h6 : s.getReg .x6=520192#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧
      t.pc=BitVec.ofNat 64 (4096*(127-Search.topRank v q)+2^64+4*entOff q-4096) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)= ~~~(sourceWord v q) ^^^ (if q<9 then 0 else hiMask) := by
    unfold sourceWord
    split_ifs
    · rw [h16]; exact BitVec.xor_zero.symm
    · exact h17
  have hb := sourceBit_lt q hq h9
  have hf : (~~~(sourceWord v q) ^^^ (if q<9 then 0 else hiMask)).toNat/2^(sourceBit q)%128 =
      (~~~(sourceWord v q)).toNat/2^(sourceBit q)%128 := by
    split_ifs with h
    · rw [show (~~~(sourceWord v q) ^^^ (0 : Word)) = ~~~(sourceWord v q) from BitVec.xor_zero]
    · apply field_xor_hiMask
      unfold sourceBit; rw [if_neg h]; omega
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift12 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x6)+
      BitVec.ofNat 64 (2^64+4*entOff q-4096)) &&& ~~~1#64=_
    rw [h6,shift12_eval s _ _ hW _ (by omega),dispatch_value _ _ q (by omega) hq,hf,not_field _ _ hb,
      source_field v q hq h9]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]
theorem dispatch9_step {p : Nat} (hp : p<257181)
    (hrun : vrun p 5=some dispatch9R) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask) (h6 : s.getReg .x6=520192#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧
      t.pc=BitVec.ofNat 64 (8192*(63-v.toNat/2^64%64)+256) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨dispatch9R.toState s,piece_steps45 hrun hp s hpc (by simp [dispatch9R]),?_,?_,?_⟩
  · change (((s.getReg .x17 <<< (BitVec.ofNat 64 13).toNat) &&& s.getReg .x6)+256#64) &&& ~~~1#64=_
    rw [h6,h17,g9_value,mod64_xor_hiMask]
    congr 2
    have := not_field (v.extractLsb' 64 64) 0 (by decide +kernel)
    have e1 : (~~~(v.extractLsb' 64 64)).toNat%64=((~~~(v.extractLsb' 64 64)).toNat/2^0%128)%64 := by
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
    have e2 : v.toNat/2^64%64=((v.extractLsb' 64 64).toNat/2^0%128)%64 := by
      rw [extract_field v 64 0 (by decide +kernel)]
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
    rw [e1,e2,this]
    have hlt : (v.extractLsb' 64 64).toNat/2^0%128 < 128 := Nat.mod_lt _ (by decide +kernel)
    omega
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatch9R]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatch9R,rv_simp]
theorem bge9_step (k : Nat) (hk : k<125) (he : k%2=0) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf (cellW 9 k)) (h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64)) :
    ∃t, Steps Images.verifyImage s 1 1 t ∧
      t.pc=(if v.toNat/2^63%2=1 then BitVec.ofNat 64 (0x1000+4*cellW 9 k-4096) else pcOf (cellW 9 k+1)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := bge9_at k hk he
  have hp : cellW 9 k<257181 := by unfold cellW entOff; simp; omega
  refine ⟨(bge9R (cellW 9 k)).toState s,piece_steps45 hrun hp s hpc (by simp [bge9R,SymState.init]),?_,?_,?_⟩
  · rw [Result.toState_pc]
    simp only [bge9R,E.eval,h16]
    have hb : v.getLsbD 63=decide (v.toNat/2^63%2=1) := by
      rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    have hsign : CmpOp.eval .ge (~~~(v.extractLsb' 0 64)) 0=decide (v.toNat/2^63%2=1) := by
      have hz : (0 : BitVec 64)=0#64 := rfl
      simp only [CmpOp.eval]
      rw [hz, BitVec.slt_zero_eq_msb, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', hb]
      simp
    rw [hsign]
    by_cases hb' : v.toNat/2^63%2=1 <;> simp [hb']
  · intro r _; rw [Result.toState_getReg]; simp [bge9R,SymState.init,RegFile.init_get_eval]
  · intro A _ _
    simp [bge9R,rv_simp,SymState.init]
/-- T51: r5 groups 9..15 (#938's column) fault on rank 125 (word `entOff q` is zero). -/
theorem fault_top_fetch (q : Nat) (hq : q<16) (h9 : 9≤q) (s : MachineState)
    (hpc : s.pc=pcOf (entOff q)) : fetch vimage s=none := by
  have hw := fault_top_word q hq h9
  have hc := lcodeAt (entOff q) (by have := entOff_le q (by omega); omega)
  cases he : lcode (entOff q) with
  | nil => simp [he] at hw
  | cons w ws =>
    simp only [he, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [he] at hc
    exact hc.fetch s hpc
theorem fault_top126_fetch (q : Nat) (hq : q<16) (h9 : 9≤q) (he : 1024≤entOff q) (s : MachineState)
    (hpc : s.pc=pcOf (entOff q-1024)) : fetch vimage s=none := by
  have hw := fault_top126_word q hq h9 he
  have hc := lcodeAt (entOff q-1024) (by have := entOff_le q (by omega); omega)
  cases hx : lcode (entOff q-1024) with
  | nil => simp [hx] at hw
  | cons w ws =>
    simp only [hx, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [hx] at hc
    exact hc.fetch s hpc
/-! ### T51 dispatch landings (VERA2; R6 VER-A's template)
Machine-level facts for the T51 top region: zero-word guards fault; the dispatch into r6 group `h` (1..8) lands on
`cell6 h raw` (a cell for raw < 216, a guard otherwise); the prologue's g0 dispatch lands on the g0 column; group 0's
5-word dispatch also loads the r6 mask (t4 = 0xFF00) and the table base (s2 = 856064); q15's dispatch (#938's into
group 8) lands on the r7 pair's cells (rank < 49) or guards; the checksum dispatch lands on an arm or a guard. -/
theorem fetch_zero_word {p : Nat} (hp : p < 257214) (hz : zeroAt p = true) (s : MachineState)
    (hpc : s.pc = pcOf p) : fetch vimage s = none := by
  have hw : (lcode p).head? = some 0#32 := by simpa [zeroAt] using hz
  have hc := lcodeAt p hp
  cases he : lcode p with
  | nil => simp [he] at hw
  | cons w ws =>
    simp only [he, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [he] at hc
    exact hc.fetch s hpc
theorem fetch_below (s : MachineState) (h : s.pc.toNat < 0x1000) : fetch vimage s = none := by
  unfold fetch; simp [h]
theorem fetch_above (s : MachineState) (h : 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s = none := by
  have hl : vimage.code.length ≤ 257280 := verifyCode_length_le
  have hn : vimage.code[(s.pc.toNat-0x1000)/4]? = none :=
    List.getElem?_eq_none_iff.mpr (by omega)
  unfold fetch
  split
  · rfl
  · rw [hn]; rfl
theorem fetch_outside' (s : MachineState)
    (h : s.pc.toNat<0x1000 ∨ 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := by
  rcases h with h|h
  · exact fetch_below s h
  · exact fetch_above s h
theorem cell6_lt (g raw : Nat) (hg : g < 9) (hr : raw < 256) : cell6 g raw < 257214 := by
  unfold cell6 r6Off; split_ifs <;> omega
/-- r6 group `g`, field value `raw`: a valid raw lands on the cell of rank `raw - 40` (g = 0) or `raw`. -/
theorem cell6_valid (g raw : Nat) (hg : g < 9) (hv : raw6Valid g raw = true) :
    cell6 g raw = cellW g (if g = 0 then raw - 40 else raw) := by
  unfold cellW rawOf6
  rw [if_pos hg]
  by_cases h0 : g = 0
  · subst h0
    simp only [raw6Valid, if_true, decide_eq_true_eq] at hv
    simp only [if_true]; congr 1; omega
  · simp [h0]
theorem mod64_field (X b : Nat) (hb : b + 8 ≤ 64) : X % 2^64 / 2^b % 256 = X / 2^b % 256 := by
  rw [show (2:Nat)^64 = 2^b * 2^(64-b) by rw [← pow_add]; congr 1; omega, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (show 256 ∣ 2^(64-b) from ⟨2^(64-b-8), by rw [show (256:Nat) = 2^8 by norm_num, ← pow_add]; congr 1; omega⟩)]
theorem lo_field (V : Digest) (b : Nat) (hb : b + 8 ≤ 64) :
    (V.extractLsb' 0 64).toNat / 2^b % 256 = V.toNat / 2^b % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, mod64_field _ _ hb]
theorem hi_field (V : Digest) (b : Nat) (hb : b + 8 ≤ 64) :
    (V.extractLsb' 64 64).toNat / 2^b % 256 = V.toNat / 2^(64+b) % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, mod64_field _ _ hb, Nat.div_div_eq_div_mul, ← pow_add]
theorem r6Src_mid (h : Nat) (h2 : 2 ≤ h) (h6 : h ≤ 6) (s : MachineState) :
    (r6Src h).eval s = s.getReg .x16 >>> (8*h-8) := by
  unfold r6Src; rw [if_neg (by omega), if_pos (by omega)]
  show s.getReg .x16 >>> ((BitVec.ofNat 64 (8*h-8)).toNat % 64) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8*h-8 < 2^64 by omega), Nat.mod_eq_of_lt (show 8*h-8 < 64 by omega)]
/-- The masked field of the dispatch into r6 group `h` (1..8): `256 raw`. -/
theorem r6Src_eval (h : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64) :
    (r6Src h).eval s &&& 65280#64 = BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256)) := by
  by_cases e1 : h = 1
  · subst e1
    simp only [r6Src, if_true, E.eval, h16]; rw [word_ff00, lo_field V 8 (by omega)]; rfl
  by_cases e7 : h = 7
  · subst e7
    have hs : (r6Src 7).eval s = s.getReg .x17 >>> 40 := by
      unfold r6Src; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]; rfl
    rw [hs, h17, field_ff00, hi_field V 48 (by omega)]; rfl
  by_cases e8 : h = 8
  · subst e8
    have hs : (r6Src 8).eval s = s.getReg .x17 >>> 48 := by
      unfold r6Src; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; rfl
    rw [hs, h17, field_ff00, hi_field V 56 (by omega)]; rfl
  · rw [r6Src_mid h (by omega) (by omega) s, h16, field_ff00, lo_field V _ (by omega)]
    unfold r6Pos; rw [if_neg e7, if_neg e8, show 8*h-8+8 = 8*h by omega]
theorem guard6_fault (g raw : Nat) (hg : g < 9) (hr : raw < 256) (hv : raw6Valid g raw = false)
    (h3 : g = 0 → 3 ≤ raw) (s : MachineState) (hpc : s.pc = pcOf (cell6 g raw)) : fetch vimage s = none := by
  have hc := guard6Check_at g raw hg hr
  unfold guard6Check at hc
  rw [hv, Bool.false_or] at hc
  have hz : zeroAt (cell6 g raw) = true := by
    by_cases h0 : g = 0
    · have := h3 h0; subst h0; simpa [show ¬ raw < 3 by omega] using hc
    · simpa [h0] using hc
  exact fetch_zero_word (cell6_lt g raw hg hr) hz s hpc
/-- `a4` of the dispatch into r6 group `h` (2..8; group 1 is entered by group 0's `g0DispR`). -/
theorem r6A_eval (h : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    (r6A h).eval s = if r6B h then 856064#64 - BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256))
      else BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256)) + 856064#64 := by
  have hf := r6Src_eval h h1 h8 V s h16 h17
  unfold r6A
  split_ifs
  · show s.getReg .x18 - ((r6Src h).eval s &&& s.getReg .x29) = _
    rw [h18, h29, hf]
  · show ((r6Src h).eval s &&& s.getReg .x29) + s.getReg .x18 = _
    rw [h18, h29, hf]
/-- Dispatch into r6 group `h` (1..8): pc at the cell of the field value. -/
theorem r6_dispatch_pc (h : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    (r6DispR h).pc.eval s = pcOf (cell6 h (V.toNat / 2^(r6Pos h) % 256)) := by
  have ha := r6A_eval h h1 h8 V s h16 h17 h29 h18
  have hr : V.toNat / 2^(r6Pos h) % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have ho := r6Off_lt h
  show ((r6A h).eval s + r6Imm h) &&& ~~~1#64 = _
  rw [ha, cell6_tab h _ h1 h8]
  unfold r6Imm
  split_ifs with hh
  · exact tabB_target _ _ hr ho
  · exact tabA_target _ _ hr ho
theorem r6_dispatch_step {p h : Nat} (h1 : 1 ≤ h) (h8 : h ≤ 8) (hp : p < 257181)
    (hrun : vrun p 5 = some (r6DispR h)) (s : MachineState) (V : Digest) (hpc : s.pc = pcOf p)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    ∃ t, Steps Images.verifyImage s (r6DispR h).steps (r6DispR h).cycles t ∧
      t.pc = pcOf (cell6 h (V.toNat / 2^(r6Pos h) % 256)) ∧ RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨(r6DispR h).toState s, piece_steps45 hrun hp s hpc (by simp [r6DispR]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]; exact r6_dispatch_pc h h1 h8 V s h16 h17 h29 h18
  · intro r hr
    rw [Result.toState_getReg]
    simp only [r6DispR]
    rw [RegFile.get_set_ne _ _ (show r ≠ .x14 by simpa using hr), RegFile.init_get_eval]
  · intro A _ _
    simp [r6DispR, rv_simp]
/-- Group 0's 5-word dispatch into group 1: loads t4 = 0xFF00 (verify data word 16 at `s1 - 288`) and s2 = 856064,
then jumps to group 1's cell of the field `a6 bits 8..15`. -/
theorem g0_dispatch_step {p : Nat} (hp : p < 257181) (hrun : vrun p 5 = some g0DispR) (s : MachineState)
    (V : Digest) (hpc : s.pc = pcOf p) (h16 : s.getReg .x16 = V.extractLsb' 0 64)
    (h9 : s.getReg .x2 = 0xffbde0#64) (hmask : s.getMem 0xffbdf0#64 = 65280#64) :
    ∃ t, Steps Images.verifyImage s 5 5 t ∧ t.pc = pcOf (cell6 1 (V.toNat / 2^8 % 256)) ∧
      t.getReg .x29 = 65280#64 ∧ t.getReg .x18 = 856064#64 ∧ RegsExcept s t [.x29, .x18, .x14] ∧
      Frame s t (fun _ => False) := by
  have hobl : ∀ o ∈ g0DispR.st.obl, o.holds s := by
    intro o ho
    simp [g0DispR] at ho
    subst ho
    simp [Oblig.holds, rv_simp, accessValid_iff, MEMORY_BYTES, h9]
  have hm : maskE.eval s = 65280#64 := by
    change s.getMem (s.getReg .x2 + BitVec.ofNat 64 16) = _
    rw [h9, show (0xffbde0#64 : Word) + BitVec.ofNat 64 16 = 0xffbdf0#64 from rfl]; exact hmask
  refine ⟨g0DispR.toState s, piece_steps45 hrun hp s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    show ((g0A.eval s) + BitVec.ofNat 64 (2^64-72)) &&& ~~~1#64 = _
    have hg : g0A.eval s = 856064#64 - BitVec.ofNat 64 (256 * (V.toNat / 2^8 % 256)) := by
      show 856064#64 - (s.getReg .x16 &&& maskE.eval s) = _
      rw [hm, h16, word_ff00, lo_field V 8 (by omega)]
    have hr : V.toNat / 2^8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [hg, cell6_tab 1 _ (by omega) (by omega)]
    simp only [r6B, show (1:Nat) < 4 by decide, true_or, decide_true, if_true]
    have := tabB_target _ (r6Off 1) hr (r6Off_lt 1)
    rwa [show BitVec.ofNat 64 (2^64+4*r6Off 1-256) = BitVec.ofNat 64 (2^64-72) by unfold r6Off; rfl] at this
  · rw [Result.toState_getReg]; simp only [g0DispR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    exact hm
  · rw [Result.toState_getReg]; simp only [g0DispR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]; rfl
  · intro r hr
    rw [Result.toState_getReg]
    simp only [g0DispR]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegFile.get_set_ne _ _ hr.2.2, RegFile.get_set_ne _ _ hr.2.1, RegFile.get_set_ne _ _ hr.1,
      RegFile.init_get_eval]
  · intro A _ _
    simp [g0DispR, rv_simp]
/-- The checksum dispatch (end of the r7 pair): pc at `ckWord ds` for `s8 = T - ds`, `ds <= 231`. -/
theorem ck_dispatch_step {p : Nat} (hp : p < 257181) (hrun : vrun p 5 = some ckDispR) (s : MachineState)
    (ds : Nat) (hd : ds ≤ 231) (hpc : s.pc = pcOf p)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) :
    ∃ t, Steps Images.verifyImage s 3 3 t ∧ t.pc = pcOf (ckWord ds) ∧ RegsExcept s t [.x14] ∧
      Frame s t (fun _ => False) := by
  refine ⟨ckDispR.toState s, piece_steps45 hrun hp s hpc (by simp [ckDispR]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    show ((((s.getReg .x24 + 89#64) <<< ((11#64).toNat % 64))) + 1168#64) &&& ~~~1#64 = _
    rw [h24]; exact ck_target ds hd
  · intro r hr
    rw [Result.toState_getReg]
    simp only [ckDispR]
    rw [RegFile.get_set_ne _ _ (show r ≠ .x14 by simpa using hr), RegFile.init_get_eval]
  · intro A _ _
    simp [ckDispR, rv_simp]
theorem ckWord_lt (ds : Nat) : ckWord ds < 257214 := by unfold ckWord topT; omega
/-- Checksum landing: an arm when `T - 5 <= ds <= T` (checksum digit 0..5), otherwise a zero word. -/
theorem ck_landing (ds : Nat) (hd : ds < 232) :
    (topT - 5 ≤ ds ∧ ds ≤ topT ∧ ckWord ds = ckArm (topT - ds)) ∨
      (∀ s : MachineState, s.pc = pcOf (ckWord ds) → fetch vimage s = none) := by
  by_cases h : topT - 5 ≤ ds ∧ ds ≤ topT
  · left; refine ⟨h.1, h.2, ?_⟩; unfold ckWord ckArm topT at *; omega
  · right; intro s hpc
    have hc := ckGuardCheck_at ds hd
    unfold ckGuardCheck at hc
    have hz : zeroAt (ckWord ds) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact absurd hc h
      · exact hc
    exact fetch_zero_word (ckWord_lt ds) hz s hpc
/-- r6 group `h >= 1` landing: rank `raw < 216` at its cell, otherwise a zero-word guard. -/
theorem r6_landing (h raw : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (hr : raw < 256) :
    (raw < 216 ∧ cell6 h raw = cellW h raw) ∨
      (∀ s : MachineState, s.pc = pcOf (cell6 h raw) → fetch vimage s = none) := by
  by_cases hv : raw < 216
  · left; refine ⟨hv, ?_⟩
    have := cell6_valid h raw (by omega) (by simp [raw6Valid, show h ≠ 0 by omega, hv])
    simpa [show h ≠ 0 by omega] using this
  · right; intro s hpc
    exact guard6_fault h raw (by omega) hr (by simp [raw6Valid, show h ≠ 0 by omega, hv]) (by omega) s hpc
/-- g0 landing (prologue dispatch on `a6`): field value `raw >= 40` at the cell of rank `raw - 40`; every other
value faults (zero-word guards for 3 <= raw < 40, below the code for raw = 1, 2, above it for raw = 0). -/
theorem g0_landing (W : Word) (s : MachineState)
    (hpc : s.pc = (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) :
    (40 ≤ W.toNat % 256 ∧ s.pc = pcOf (cellW 0 (W.toNat % 256 - 40))) ∨ fetch vimage s = none := by
  have hr : W.toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
  by_cases h0 : W.toNat % 256 = 0
  · right; apply fetch_above; rw [hpc]; exact g0_target0 W h0
  rw [g0_target W _ rfl (by omega)] at hpc
  by_cases h3 : W.toNat % 256 < 3
  · right; apply fetch_below; rw [hpc]; exact g0_low _ h3
  rw [g0_cell _ (by omega)] at hpc
  by_cases h40 : 40 ≤ W.toNat % 256
  · left; refine ⟨h40, ?_⟩
    rw [hpc, cell6_valid 0 _ (by omega) (by simp [raw6Valid, h40])]; rfl
  · right
    exact guard6_fault 0 _ (by omega) hr (by simp [raw6Valid]; omega) (fun _ => by omega) s hpc
theorem cellW16_lt (k : Nat) : cellW 16 k < 257214 := by
  have he : entOff 8 = 676 := rfl
  unfold cellW; simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]; omega
/-- r7-pair landing (q15's dispatch, #938's into group 8, on the rank `k = topRank v 8`): rank `k < 49` lands on
its cell; ranks 49..125 on zero-word guards; ranks 126, 127 outside the code. -/
theorem pair_landing (k : Nat) (hk : k < 128) (t : MachineState)
    (hpc : t.pc = BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff 8-4096)) :
    (k < 49 ∧ t.pc = pcOf (cellW 16 k)) ∨ fetch vimage t = none := by
  by_cases h49 : k < 49
  · left; exact ⟨h49, by rw [hpc, cell_value_pair k (by omega)]⟩
  right
  by_cases h125 : k ≤ 125
  · have hg := r7GuardCheck_at k (by omega)
    unfold r7GuardCheck at hg
    simp only [Bool.or_eq_true, decide_eq_true_eq, h49, false_or] at hg
    have hp : t.pc = pcOf (cellW 16 k) := by
      by_cases h4 : k ≤ 124
      · rw [hpc, cell_value_pair k h4]
      · have : k = 125 := by omega
        subst this
        rw [hpc, fault125_value 8 (by omega)]
        unfold cellW; simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]; rfl
    exact fetch_zero_word (cellW16_lt k) hg t hp
  · by_cases h126 : k = 126
    · apply fetch_below; rw [hpc, h126]; exact fault126_low 8 (by decide)
    · apply fetch_outside'; rw [hpc]; exact fault_value 8 k (by omega) (by omega) hk
end SigGolfCandidate.T3M.Nonbinary
end
/-! ### T51 top word at the machine
The selected half `V` sits in a6/a7 unflipped (`Encoded0` / `Encoded6`). The r6 groups read `T3.r6Raw V g` directly
(the T51 `topMask` flip only touches bits 56..111); the r5 groups 9..15 and the r7 pair run #938's dispatch code,
which sees the word `r5V V = V ^^^ (2^119 - 1)` in #938's convention (x16 = ~lo, x17 = ~hi ^ hiMask), whose
`Search.topRank` is `T3.r5Rank V` (q = 9..15) and `T3.r7Rank V` (q = 8, bits 56..62). -/
section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- The r5 groups' view of the selected half (#938's `Encoded` word). -/
def r5V (V : Digest) : Digest := V ^^^ BitVec.ofNat 128 (2^119-1)
theorem r5V_lo (V : Digest) : ~~~((r5V V).extractLsb' 0 64) = V.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [r5V, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hj, Nat.zero_add]
  have h1 : j < 128 := by omega
  have h2 : j < 119 := by omega
  simp [h1, h2]
theorem hiMask_bit (j : Nat) (hj : j < 64) : hiMask.getLsbD j = decide (55 ≤ j) := by
  unfold hiMask
  rw [BitVec.getLsbD_ofNat, show (2:Nat)^64-2^55=2^55*(2^9-1) by norm_num, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 55 ≤ j
  · simp [h, hj]; omega
  · simp [h]
theorem r5V_hi (V : Digest) : ~~~((r5V V).extractLsb' 64 64) ^^^ hiMask = V.extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_xor, hiMask_bit j hj, r5V, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hj]
  have h1 : 64 + j < 128 := by omega
  by_cases h : 55 ≤ j
  · have h2 : ¬ 64 + j < 119 := by omega
    simp [h, h1, h2]
  · have h2 : 64 + j < 119 := by omega
    simp [h, h1, h2]
theorem nat_field_eq (X Y b : Nat) (n : Nat) (h : ∀ j, j < n → X.testBit (j+b) = Y.testBit (j+b)) :
    X / 2^b % 2^n = Y / 2^b % 2^n := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < n
  · simp [hj, h j hj]
  · simp [hj]
theorem topMask_eq : T3.topMask = 2^56*(2^56-1) := by unfold T3.topMask; norm_num
/-- The 7-bit field `q` (8 <= q < 16: bits 7q..7q+6 inside 56..111) under #938's word is the spec's flipped field. -/
theorem topRank_r5V (V : Digest) (q : Nat) (h8 : 8 ≤ q) (hq : q < 16) :
    Search.topRank (r5V V) q = T3.r5Rank V q := by
  unfold Search.topRank T3.r5Rank T3.topCode T3.topFlip r5V
  have e := nat_field_eq (V ^^^ BitVec.ofNat 128 (2^119-1)).toNat (V ^^^ BitVec.ofNat 128 T3.topMask).toNat (7*q) 7
    (by
      intro j hj
      rw [BitVec.toNat_xor, BitVec.toNat_xor, Nat.testBit_xor, Nat.testBit_xor]
      have e1 : (BitVec.ofNat 128 (2^119-1)).toNat.testBit (j + 7*q) = true := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.testBit_two_pow_sub_one]; simp; omega
      have e2 : (BitVec.ofNat 128 T3.topMask).toNat.testBit (j + 7*q) = true := by
        rw [topMask_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.testBit_two_pow_mul,
          Nat.testBit_two_pow_sub_one]
        simp; omega
      rw [e1, e2])
  simpa using e
theorem cellW9 (k : Nat) : cellW 9 k = 1024*(125-k)+64 := by
  unfold cellW; simp only [show ¬ (9:Nat)<9 by omega, show (9:Nat)<16 by omega, if_false, if_true]; rfl
theorem r7Rank_eq (V : Digest) : T3.r7Rank V = T3.r5Rank V 8 := rfl
theorem topRank_r5V_pair (V : Digest) : Search.topRank (r5V V) 8 = T3.r7Rank V := by
  rw [topRank_r5V V 8 (by omega) (by omega)]; rfl
/-- Bits outside 56..111 of the spec word `topCode V` are the bits of `V`. -/
theorem topCode_field (V : Digest) (b n : Nat) (h : b + n ≤ 56 ∨ 112 ≤ b) :
    T3.topCode V / 2^b % 2^n = V.toNat / 2^b % 2^n := by
  unfold T3.topCode T3.topFlip
  apply nat_field_eq
  intro j hj
  rw [BitVec.toNat_xor, Nat.testBit_xor]
  have e : (BitVec.ofNat 128 T3.topMask).toNat.testBit (j + b) = false := by
    rw [topMask_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow_sub_one]
    simp; omega
  rw [e]; simp
theorem r6Shift_eq (g : Nat) (hg : g < 9) : T3.r6Shift g = r6Pos g := by
  unfold T3.r6Shift r6Pos; split_ifs <;> omega
/-- The 8-bit field of r6 group `g` is read from `V` itself (no flip). -/
theorem r6Raw_eq (V : Digest) (g : Nat) (hg : g < 9) : T3.r6Raw V g = V.toNat / 2^(r6Pos g) % 256 := by
  unfold T3.r6Raw
  rw [r6Shift_eq g hg, show (256:Nat) = 2^8 by norm_num]
  apply topCode_field
  unfold r6Pos; split_ifs <;> omega
/-- g0's field (the low byte of a6). -/
theorem g0_raw (V : Digest) : (V.extractLsb' 0 64).toNat % 256 = T3.r6Raw V 0 := by
  rw [r6Raw_eq V 0 (by omega)]
  have := lo_field V 0 (by omega)
  simpa [r6Pos] using this
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- Inside a group: chain A -> B, B -> C (T51: chains < 50; the r7 pair's chain 49 ends at the checksum dispatch). -/
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<50) (h2 : i%3≠2) (h49 : i≠49)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  rw [if_pos hi, if_pos (show i+1<50 by omega)]
  have e : (i+1)/3=i/3 := by omega
  by_cases h0 : i%3=0
  · rw [if_pos h0,if_neg (show (i+1)%3≠0 by omega),if_pos (show (i+1)%3=1 by omega)]
    unfold qB;rw [e]
  · rw [if_neg h0,if_pos (show i%3=1 by omega),if_neg (show (i+1)%3≠0 by omega),
      if_neg (show (i+1)%3≠1 by omega)]
    unfold qC;rw [e]
def chainF (c : NCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i)
    (c.padHeader i) (c.bufferVal i)
  pure (ends++[v])
/-- Chains of top group `q`: 3 (q < 16), the r7 pair (q = 16) 2. -/
def nCh (q : Nat) : Nat := if q = 16 then 2 else 3
theorem nCh_cases (q : Nat) : (q = 16 ∧ nCh q = 2) ∨ (q ≠ 16 ∧ nCh q = 3) := by
  unfold nCh; by_cases h : q = 16 <;> simp [h]
/-- Top group `q < 17` (chains `3q .. 3q + nCh q - 1`) from any of its chains to its last chain's end. -/
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<17) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+nCh q-1) ends t → Verify.GoodQP P t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+nCh q → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQP P s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  have hn := nCh_cases q
  intro k
  induction k with
  | zero => intro i _ _ h;omega
  | succ k ih =>
    intro i hi hik _ acc s hs
    rw [List.range'_succ,List.foldlM_cons]
    simp only [chainF,bind_assoc,pure_bind,Verify.ccM_bind]
    have H := c.chain_good hc hds hk h0 i (by omega) acc
      (fun ends => Verify.ccM ((List.range' (i+1) k).foldlM c.chainF ends) K)
      (N+40*k) (C+c.chainsCost (i+1) k) (A+c.chainsCost (i+1) k) Q
      (fun v t ht => by
        by_cases hk0 : k=0
        · subst hk0
          have he : i=3*q+nCh q-1 := by omega
          rw [he] at ht
          simpa [chainsCost] using hK _ t ht
        · have ht' : c.ChainIn s0 (i+1) (acc++[v]) t :=
            c.next_inline s0 i (by omega) (by omega) (by omega) (acc++[v]) t ht
          exact ih (i+1) (by omega) (by omega) (by omega) (acc++[v]) t ht') s hs
    refine H.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
def GroupIn (c : NCtx) (s0 : MachineState) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (3*q)) acc s ∧ acc.length=3*q ∧ s.pc=pcOf (c.entPc q)
theorem fetch_fault (s : MachineState) (h : s.pc.toNat<0x1000) : fetch vimage s=none := fetch_below s h
theorem fetch_high (s : MachineState) (h : 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := fetch_above s h
theorem fetch_outside (s : MachineState)
    (h : s.pc.toNat<0x1000 ∨ 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := fetch_outside' s h
theorem topRank_lt (v : Digest) (q : Nat) : Search.topRank v q<128 := by
  unfold Search.topRank; omega
theorem topRank9 (v : Digest) : Search.topRank v 9=v.toNat/2^63%2+2*(v.toNat/2^64%64) := by
  unfold Search.topRank
  rw [show 7*9=63 from rfl]
  have h : v.toNat/2^64=v.toNat/2^63/2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [h]; omega
/-- Reverse checksum `topT - (digits of the chains of groups 0..q)` (q = 16: chains 0..49). -/
def s8v (c : NCtx) (q : Nat) : Word :=
  BitVec.ofNat 64 topT-BitVec.ofNat 64 (((List.range (3*q+nCh q)).map c.dig).sum)
def set24 (b : MachineState) (x : Word) : MachineState := b.setReg .x24 x
theorem set24_regs (b : MachineState) (x : Word) (r : Reg) (hr : r≠.x24) : (set24 b x).getReg r=b.getReg r := by
  unfold set24
  rw [setReg_of_ne b _ (by decide +kernel)]
  cases r <;> simp_all [MachineState.getReg]
theorem set24_24 (b : MachineState) (x : Word) : (set24 b x).getReg .x24=x := by
  unfold set24
  rw [setReg_of_ne b _ (by decide +kernel)]
  rfl
theorem set24_mem (b : MachineState) (x : Word) (a : Word) : (set24 b x).getMem a=b.getMem a := rfl
theorem set24_known (c : NCtx) {b : MachineState} (x : Word) (hk : ∀p∈c.known,b.getReg p.1=p.2) :
    ∀p∈c.known,(set24 b x).getReg p.1=p.2 := by
  intro p hp
  have hn : ∀ p ∈ c.known, p.1 ≠ .x24 := by simp [known]
  rw [set24_regs _ _ _ (hn p hp)]
  exact hk p hp
theorem set24_orig (c : NCtx) {b : MachineState} (x : Word) (h0 : c.Orig0 b) : c.Orig0 (set24 b x) :=
  ⟨⟨fun i hi k hk => h0.1.1 i hi k hk,fun i hi k hk => h0.1.2 i hi k hk⟩, h0.2.congr (fun A _ _ => set24_mem b x _)⟩
/-- T51: group 0's dispatch loads t4 = 0xFF00 and s2 = 856064; the later groups run on this base. -/
def setTab (b : MachineState) : MachineState := (b.setReg .x29 65280#64).setReg .x18 856064#64
theorem setTab_regs (b : MachineState) (r : Reg) (h29 : r≠.x29) (h18 : r≠.x18) :
    (setTab b).getReg r=b.getReg r := by
  unfold setTab
  rw [setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel)]
  cases r <;> simp_all [MachineState.getReg]
theorem setTab_29 (b : MachineState) : (setTab b).getReg .x29=65280#64 := by
  unfold setTab
  rw [setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel)]
  rfl
theorem setTab_18 (b : MachineState) : (setTab b).getReg .x18=856064#64 := by
  unfold setTab
  rw [setReg_of_ne _ _ (by decide +kernel)]
  rfl
theorem setTab_mem (b : MachineState) (a : Word) : (setTab b).getMem a=b.getMem a := rfl
theorem setTab_known (c : NCtx) {b : MachineState} (hk : ∀p∈c.known,b.getReg p.1=p.2) :
    ∀p∈c.known,(setTab b).getReg p.1=p.2 := by
  intro p hp
  have h29 : ∀ p ∈ c.known, p.1 ≠ .x29 := by simp [known]
  have h18 : ∀ p ∈ c.known, p.1 ≠ .x18 := by simp [known]
  rw [setTab_regs _ _ (h29 p hp) (h18 p hp)]
  exact hk p hp
theorem setTab_orig (c : NCtx) {b : MachineState} (h0 : c.Orig0 b) : c.Orig0 (setTab b) :=
  ⟨⟨fun i hi k hk => h0.1.1 i hi k hk,fun i hi k hk => h0.1.2 i hi k hk⟩, h0.2.congr (fun A _ _ => setTab_mem b _)⟩
theorem setTab_24 (b : MachineState) : (setTab b).getReg .x24=b.getReg .x24 :=
  setTab_regs b .x24 (by decide) (by decide)
theorem sum_range_three (f : Nat → Nat) (n : Nat) :
    ((List.range (n+3)).map f).sum=((List.range n).map f).sum+(f n+f (n+1)+f (n+2)) := by
  simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega
theorem kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<16) :
    kss q (c.kOf q)=c.dig (3*q)+c.dig (3*q+1)+c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q hq
  simp only [kss,k1,k2,k3]
theorem kss_kOf16 (c : NCtx) (hds : c.DigitsOk) : kss 16 (c.kOf 16)=c.dig 48+c.dig 49 := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf16 hds
  simp only [kss,k1,k2,k3,Nat.add_zero]
/-- The digit sum of group `q` (its cell's s8 word subtracts `kss q (kOf q)`). -/
theorem kss_group (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    ((List.range (3*q+nCh q)).map c.dig).sum = ((List.range (3*q)).map c.dig).sum + kss q (c.kOf q) := by
  rcases nCh_cases q with ⟨rfl, h2⟩ | ⟨h16, h3⟩
  · rw [h2, c.kss_kOf16 hds, show 3*16+2 = (48+1)+1 from rfl, List.range_succ, List.range_succ,
      show 3*16 = 48 from rfl]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.reduceAdd]
    omega
  · rw [h3, c.kss_kOf hds q (by omega), sum_range_three]
theorem s8v_succ (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.s8v q+(-BitVec.ofNat 64 (kss (q+1) (c.kOf (q+1))))=c.s8v (q+1) := by
  have hS : ((List.range (3*(q+1)+nCh (q+1))).map c.dig).sum =
      ((List.range (3*q+nCh q)).map c.dig).sum+kss (q+1) (c.kOf (q+1)) := by
    rw [c.kss_group hds (q+1) (by omega)]
    have hn : nCh q = 3 := by unfold nCh; rw [if_neg (by omega)]
    rw [hn, show 3*(q+1) = 3*q+3 by ring]
  unfold s8v
  rw [hS,BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg,BitVec.neg_add]
  ac_rfl
theorem s8v0 (c : NCtx) (hds : c.DigitsOk) :
    c.s8v 0 = BitVec.ofNat 64 topT-BitVec.ofNat 64 (kss 0 (c.kOf 0)) := by
  have h : ((List.range (3*0+nCh 0)).map c.dig).sum = kss 0 (c.kOf 0) := by
    rw [c.kss_kOf hds 0 (by omega)]
    show ((List.range 3).map c.dig).sum = c.dig 0 + c.dig 1 + c.dig 2
    simp [List.range_succ]; try omega
  unfold s8v; rw [h]
/-- Entry words (and the lead after them) of every top group lie in the code. -/
theorem entW_all : (List.range 17).all (fun q => (List.range (nRank q)).all (fun k => decide (entW q k + 1 < 257181)))
    = true := by decide +kernel
theorem entW_lt (q k : Nat) (hq : q < 17) (hk : k < nRank q) : entW q k + 1 < 257181 := by
  have h1 := List.all_eq_true.mp entW_all q (List.mem_range.mpr hq)
  have := List.all_eq_true.mp h1 k (List.mem_range.mpr hk)
  simpa using this
theorem kOf_nRank (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q < 17) : c.kOf q < nRank q := by
  by_cases h16 : q = 16
  · subst h16; exact c.kOf16_lt hds
  · have := c.kOf_lt hds q (by omega); unfold nRank; rw [if_neg h16]; exact this
theorem entry_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {b : MachineState} (q : Nat) (hq : q<16)
    (h24 : b.getReg .x24=c.s8v q) (acc : List Digest) (s : MachineState) (hs : c.GroupIn b (q+1) acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v (q+1))) (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hkq := c.kOf_nRank hds (q+1) (by omega)
  have hchk := s8Run_at (q+1) (c.kOf (q+1)) (by omega) hkq
  rw [if_neg (show q+1≠0 by omega)] at hchk
  have hrun := rOK_eq hchk
  have hp : entW (q+1) (c.kOf (q+1))<257181 := by
    have := entW_lt (q+1) (c.kOf (q+1)) (by omega) hkq; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [s8R])
  set r := s8R (kss (q+1) (c.kOf (q+1))) (entW (q+1) (c.kOf (q+1))) with hr
  have h24s : s.getReg .x24=c.s8v q := (hR .x24 (by decide +kernel)).trans h24
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,s8R]
      rw [RegFile.get_set_self _ _ (by decide +kernel),addC_eval,set24_24]
      simp only [E.eval,h24s]
      exact c.s8v_succ hds q hq
    · simp only [hr,s8R]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [Result.toState_getMem,set24_mem]
    simp only [hr,s8R]
    rw [memEval_nil]
    exact hF A hA hn
  · have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
      rw [Result.toState_getMem]; simp [hr,s8R,memEval_nil]
    exact (hS j hj).frame hfr (by unfold slot; split <;> omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,s8R,E.eval]
    unfold startPc leadPc leadOff
    simp only [show 3*(q+1)<50 by omega,show 3*(q+1)%3=0 by omega,if_true,show 3*(q+1)/3=q+1 by omega]
def s8w (c : NCtx) (n : Nat) : Word := BitVec.ofNat 64 topT-BitVec.ofNat 64 (((List.range n).map c.dig).sum)
theorem s8v_eq (c : NCtx) (q : Nat) : c.s8v q=c.s8w (3*q+nCh q) := rfl
theorem sum_range_add (f : Nat → Nat) (n k : Nat) :
    ((List.range (n+k)).map f).sum = ((List.range n).map f).sum + ((List.range' n k).map f).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append, ih, List.range'_concat]
    simp; omega
theorem s8w_add (c : NCtx) (n k : Nat) :
    c.s8w n+(-BitVec.ofNat 64 (((List.range' n k).map c.dig).sum))=c.s8w (n+k) := by
  unfold s8w
  rw [sum_range_add, BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg,BitVec.neg_add]
  ac_rfl
/-! ### T51 group transitions -/
/-- T51 register invariants at the top start (prologue done): the selected half `V` in a6/a7 (unflipped) and the r5
mask t1 = 0x7F000. -/
structure Encoded0 (V : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16 = V.extractLsb' 0 64
  hi : s.getReg .x17 = V.extractLsb' 64 64
  mask5 : s.getReg .x6 = 520192#64
/-- ... and after group 0's dispatch: the r6 mask t4 = 0xFF00 and the table base s2 = 856064 (`setTab`). -/
structure Encoded6 (V : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16 = V.extractLsb' 0 64
  hi : s.getReg .x17 = V.extractLsb' 64 64
  mask6 : s.getReg .x29 = 65280#64
  base6 : s.getReg .x18 = 856064#64
  mask5 : s.getReg .x6 = 520192#64
theorem setTab_encoded {V : Digest} {b : MachineState} (he : Encoded0 V b) : Encoded6 V (setTab b) :=
  ⟨(setTab_regs _ _ (by decide) (by decide)).trans he.lo, (setTab_regs _ _ (by decide) (by decide)).trans he.hi,
    setTab_29 b, setTab_18 b, (setTab_regs _ _ (by decide) (by decide)).trans he.mask5⟩
theorem set24_encoded0 {V : Digest} {b : MachineState} (x : Word) (he : Encoded0 V b) : Encoded0 V (set24 b x) :=
  ⟨(set24_regs _ _ _ (by decide +kernel)).trans he.lo,(set24_regs _ _ _ (by decide +kernel)).trans he.hi,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask5⟩
theorem set24_encoded6 {V : Digest} {b : MachineState} (x : Word) (he : Encoded6 V b) : Encoded6 V (set24 b x) :=
  ⟨(set24_regs _ _ _ (by decide +kernel)).trans he.lo,(set24_regs _ _ _ (by decide +kernel)).trans he.hi,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask6,(set24_regs _ _ _ (by decide +kernel)).trans he.base6,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask5⟩
/-- The 8-bit field of r6 group `h` (1..8) in the selected half. -/
def raw6Of (V : Digest) (h : Nat) : Nat := V.toNat / 2^(r6Pos h) % 256
theorem gX_all : (List.range 17).all (fun q => (List.range (nRank q)).all (fun k => decide (gX q k < 257181)))
    = true := by decide +kernel
theorem gX_lt (q k : Nat) (hq : q < 17) (hk : k < nRank q) : gX q k < 257181 := by
  have h1 := List.all_eq_true.mp gX_all q (List.mem_range.mpr hq)
  have := List.all_eq_true.mp h1 k (List.mem_range.mpr hk)
  simpa using this
/-- A dispatch (only x14 written, no memory written) keeps the chain-loop base invariant. -/
theorem base_disp (c : NCtx) {s0 s t : MachineState} {acc : List Digest} {W : Nat → Prop}
    (hl : acc.length ≤ 51) (hB : c.Base s0 W acc s) (rt : RegsExcept s t [.x14])
    (ft : Frame s t (fun _ => False)) : c.Base s0 W acc t := by
  obtain ⟨hR, hF, hS⟩ := hB
  refine ⟨fun x hx => ?_, (hF.trans ft).mono (by intro A hA h; rcases h with h|h; exact h; contradiction), fun j hj => ?_⟩
  · rw [rt.get (by intro h; simp only [List.mem_singleton] at h; subst x; exact hx (by decide +kernel))]
    exact hR x hx
  · exact (hS j hj).frame ft (by unfold slot; split <;> omega) (by simp) (by simp)
/-- The end pc of group `q`'s last chain is its dispatch word `gX q (kOf q)`. -/
theorem endPc_group (c : NCtx) (q : Nat) (hq : q < 17) : c.endPc (3*q+nCh q-1) = gX q (c.kOf q) := by
  rcases nCh_cases q with ⟨rfl, h2⟩ | ⟨h16, h3⟩
  · rw [h2]
    simp only [endPc, show 3*16+2-1 = 49 from rfl, show (49:Nat) < 50 by decide, if_true, show (49:Nat)%3 ≠ 0 by decide,
      show (49:Nat)%3 = 1 by decide, if_false, qC, show (49:Nat)/3 = 16 by decide, gX]
  · rw [h3]
    simp only [endPc, show 3*q+3-1 = 3*q+2 by omega, show 3*q+2 < 50 by omega, if_true,
      show (3*q+2)%3 ≠ 0 by omega, show (3*q+2)%3 ≠ 1 by omega, if_false, qX, show (3*q+2)/3 = q by omega]
theorem raw6Of_eq (V : Digest) (h : Nat) (hh : h < 9) : raw6Of V h = T3.r6Raw V h := (r6Raw_eq V h hh).symm
/-- Validity of top group `q < 17` (the range check its dispatch performs): r6 groups `T3.r6Valid`, r5 groups
rank < 125, the r7 pair rank < 49. -/
def gValid (V : Digest) (q : Nat) : Prop :=
  if q < 9 then T3.r6Valid V q = true else if q < 16 then T3.r5Rank V q < 125 else T3.r7Rank V < 49
instance (V : Digest) (q : Nat) : Decidable (gValid V q) := by unfold gValid; infer_instance
/-- Rank of top group `q < 17`. -/
def gRank (V : Digest) (q : Nat) : Nat :=
  if q < 9 then T3.r6Rank V q else if q < 16 then T3.r5Rank V q else T3.r7Rank V
/-- Steps from the end of group `j - 1` (its dispatch word) to the entry word of group `j`: group 0's 5-word
dispatch, the r6 dispatches (4), dispatch9 + bge9 (4), #938's r5 dispatches and the pair's (3). -/
def dspR6 (j : Nat) : Nat := if j = 1 then 5 else if j < 9 then 4 else if j = 9 then 4 else 3
theorem dspR6_le (j : Nat) : dspR6 j ≤ 5 := by unfold dspR6; split_ifs <;> omega
theorem r6DispR_steps (h : Nat) (h2 : 2 ≤ h) (h8 : h < 9) : (r6DispR h).steps = dspR6 h ∧ (r6DispR h).cycles = dspR6 h := by
  unfold r6DispR dspR6
  simp [show h ≠ 1 by omega, h8]
theorem gValid_r6 (V : Digest) (h : Nat) (h1 : 1 ≤ h) (h8 : h < 9) : gValid V h ↔ raw6Of V h < 216 := by
  unfold gValid T3.r6Valid; rw [raw6Of_eq V h h8]; simp [h8, show h ≠ 0 by omega]
theorem gRank_r6 (V : Digest) (h : Nat) (h1 : 1 ≤ h) (h8 : h < 9) : gRank V h = raw6Of V h := by
  unfold gRank T3.r6Rank; rw [raw6Of_eq V h h8]; simp [h8, show h ≠ 0 by omega]
theorem gValid_r5 (V : Digest) (q : Nat) (h9 : 9 ≤ q) (hq : q < 16) : gValid V q ↔ T3.r5Rank V q < 125 := by
  unfold gValid; simp [show ¬ q < 9 by omega, hq]
theorem gRank_r5 (V : Digest) (q : Nat) (h9 : 9 ≤ q) (hq : q < 16) : gRank V q = T3.r5Rank V q := by
  unfold gRank; simp [show ¬ q < 9 by omega, hq]
theorem gValid_pair (V : Digest) : gValid V 16 ↔ T3.r7Rank V < 49 := by unfold gValid; simp
theorem gRank_pair (V : Digest) : gRank V 16 = T3.r7Rank V := by unfold gRank; simp
theorem gValid_g0 (V : Digest) : gValid V 0 ↔ 40 ≤ T3.r6Raw V 0 := by
  unfold gValid T3.r6Valid; simp
theorem gRank_g0 (V : Digest) : gRank V 0 = T3.r6Raw V 0 - 40 := by
  unfold gRank T3.r6Rank; simp
/-- Valid T51 top words (every group in range; no spare bit) in the dispatch's terms. -/
theorem topRanksValid_iff (V : Digest) :
    T3.topRanksValid V = true ↔ ∀ q, q < 17 → gValid V q := by
  simp only [T3.topRanksValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_range'_1]
  constructor
  · rintro ⟨⟨h6, h5⟩, h7⟩ q hq
    unfold gValid; split_ifs with h9 h16
    · exact h6 q h9
    · exact h5 q ⟨by omega, by omega⟩
    · exact h7
  · intro hg
    refine ⟨⟨fun q hq => ?_, fun q hq => ?_⟩, ?_⟩
    · have := hg q (by omega); unfold gValid at this; simpa [hq] using this
    · have := hg q (by omega); unfold gValid at this; simpa [show ¬ q < 9 by omega, show q < 16 by omega] using this
    · have := hg 16 (by omega); unfold gValid at this; simpa using this
/-- End of top group `q` (1 <= q < 16): the dispatch into group `q+1` reaches its entry word (valid field) or faults. -/
def DispOutR6 (c : NCtx) (s0 : MachineState) (V : Digest) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  (gValid V (q+1) → ∃ t, Steps vimage s (dspR6 (q+1)) (dspR6 (q+1)) t ∧
      c.Base s0 (c.Wr (3*(q+1))) acc t ∧ acc.length = 3*(q+1) ∧ t.pc = pcOf (entW (q+1) (gRank V (q+1)))) ∧
  (¬ gValid V (q+1) → ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none)
theorem endInv_group (c : NCtx) {s0 s : MachineState} {acc : List Digest} (q : Nat) (hq : q < 16)
    (hs : c.EndInv s0 (3*q+2) acc s) : s.pc = pcOf (gX q (c.kOf q)) := by
  have he := c.endPc_group q (by omega)
  rw [show 3*q+nCh q-1 = 3*q+2 by unfold nCh; rw [if_neg (by omega)]; omega] at he
  rw [hs.2.2, he]
/-- T51: end of group 0 (chain 2 done). Group 0's 5-word dispatch loads t4 = 0xFF00 / s2 = 856064 (the base becomes
`setTab s0`) and lands on group 1's cell (field `raw6Of V 1 < 216`) or a zero-word guard. -/
theorem end_dispatch0 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded0 V s0) (hk : ∀p∈c.known,s0.getReg p.1=p.2) (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 2 acc s) :
    (gValid V 1 → ∃ t, Steps vimage s (dspR6 1) (dspR6 1) t ∧ c.Base (setTab s0) (c.Wr 3) acc t ∧
        acc.length = 3 ∧ t.pc = pcOf (entW 1 (gRank V 1))) ∧
    (¬ gValid V 1 → ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none) := by
  have hpc' := c.endInv_group 0 (by omega) hs
  obtain ⟨⟨hR,hF,hS⟩,hlen,-⟩ := hs
  have hr : vrun (gX 0 (c.kOf 0)) 5 = some g0DispR := by
    have := (c.groupFacts hds 0 (by omega)).disp
    simpa [nextDispR] using this
  have hbound := gX_lt 0 (c.kOf 0) (by omega) (c.kOf_nRank hds 0 (by omega))
  have h16 : s.getReg .x16 = V.extractLsb' 0 64 := (hR _ (by decide +kernel)).trans he.lo
  have h9 : s.getReg .x2 = 0xffbde0#64 :=
    (hR _ (by decide +kernel)).trans (hk (.x2, BitVec.ofNat 64 0xffbde0) (by simp [known]))
  have hnw : ¬ c.Wr 3 0xffbdf0 := by
    have hb := c.bufferEnd_bounds 3
    rw [slot_pos 3 (by omega)] at hb
    have hhi := hc.2.2.2.2.1
    unfold Wr; rw [slot0, slot1]; omega
  have hm : s.getMem 0xffbdf0#64 = 65280#64 := by
    rw [show (0xffbdf0#64 : Word) = BitVec.ofNat 64 0xffbdf0 from rfl, hF.get (by norm_num) hnw]; exact hmask
  obtain ⟨t, st, pt, t29, t18, rt, ft⟩ := g0_dispatch_step hbound hr s V hpc' h16 h9 hm
  have base_of : c.Base (setTab s0) (c.Wr 3) acc t := by
    refine ⟨fun x hx => ?_, fun A hA hn => ?_, fun j hj => ?_⟩
    · by_cases h29 : x = .x29
      · subst h29; rw [t29, setTab_29]
      · by_cases h18 : x = .x18
        · subst h18; rw [t18, setTab_18]
        · have h14 : x ≠ .x14 := fun h => hx (by subst h; decide)
          rw [rt.get (by simp [h29, h18, h14]), setTab_regs _ _ h29 h18]; exact hR x hx
    · rw [ft A hA (by simp), setTab_mem]; exact hF A hA hn
    · exact (hS j hj).frame ft (by unfold slot; split <;> omega) (by simp) (by simp)
  have hraw : V.toNat / 2^8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have e1 : raw6Of V 1 = V.toNat / 2^8 % 256 := by unfold raw6Of r6Pos; norm_num
  rw [gValid_r6 V 1 (by omega) (by omega), gRank_r6 V 1 (by omega) (by omega), e1]
  have hd : dspR6 1 = 5 := rfl
  rw [hd]
  refine ⟨fun hv => ⟨t, st, base_of, hlen, ?_⟩, fun hv => ⟨5, t, st, le_rfl, ?_⟩⟩
  · have hcell := cell6_valid 1 _ (by omega) (by simp [raw6Valid]; omega)
    rw [pt, hcell]; simp [entW]
  · exact guard6_fault 1 _ (by omega) hraw (by simp [raw6Valid]; omega) (by omega) t pt
/-- End of r6 group `q` (1 <= q < 8): the dispatch into r6 group `q+1`. -/
theorem end_dispatch6 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h1 : 1 ≤ q) (hq : q < 8) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  have hpc' := c.endInv_group q (by omega) hs
  obtain ⟨hB,hlen,-⟩ := hs
  have hR := hB.1
  have hr : vrun (gX q (c.kOf q)) 5 = some (r6DispR (q+1)) := by
    have := (c.groupFacts hds q (by omega)).disp
    simpa [nextDispR, show q ≠ 0 by omega, hq] using this
  have hbound := gX_lt q (c.kOf q) (by omega) (c.kOf_nRank hds q (by omega))
  have h16 : s.getReg .x16 = V.extractLsb' 0 64 := (hR _ (by decide +kernel)).trans he.lo
  have h17 : s.getReg .x17 = V.extractLsb' 64 64 := (hR _ (by decide +kernel)).trans he.hi
  have h29 : s.getReg .x29 = 65280#64 := (hR _ (by decide +kernel)).trans he.mask6
  have h18 : s.getReg .x18 = 856064#64 := (hR _ (by decide +kernel)).trans he.base6
  obtain ⟨t, st, pt, rt, ft⟩ := r6_dispatch_step (h := q+1) (by omega) (by omega) hbound hr s V hpc' h16 h17 h29 h18
  obtain ⟨hst, hcy⟩ := r6DispR_steps (q+1) (by omega) (by omega)
  rw [hst, hcy] at st
  have base_of : c.Base s0 (c.Wr (3*(q+1))) acc t := by
    rw [show 3*(q+1) = 3*q+2+1 by omega]; exact c.base_disp (by omega) hB rt ft
  have hraw : V.toNat / 2^(r6Pos (q+1)) % 256 < 256 := Nat.mod_lt _ (by norm_num)
  unfold DispOutR6
  rw [gValid_r6 V (q+1) (by omega) (by omega), gRank_r6 V (q+1) (by omega) (by omega)]
  refine ⟨fun hv => ⟨t, st, base_of, by omega, ?_⟩, fun hv => ⟨dspR6 (q+1), t, st, dspR6_le _, ?_⟩⟩
  · have hcell := cell6_valid (q+1) (V.toNat / 2^(r6Pos (q+1)) % 256) (by omega)
      (by simp only [raw6Valid, show q+1 ≠ 0 by omega, if_false, decide_eq_true_eq]; unfold raw6Of at hv; exact hv)
    rw [pt, hcell]; unfold entW raw6Of; simp [show q+1 ≠ 9 by omega, show q+1 ≠ 0 by omega]
  · exact guard6_fault (q+1) _ (by omega) hraw
      (by simp only [raw6Valid, show q+1 ≠ 0 by omega, if_false, decide_eq_false_iff_not]; unfold raw6Of at hv; omega)
      (by omega) t pt
/-- End of group `q` (8 <= q < 16) into group `q+1`: g8 -> q9 (#938's dispatch9 + bge9), q9..q14 -> q+1 (#938's
dispatch), q15 -> the r7 pair (#938's dispatch into group 8). -/
theorem end_dispatch5 (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h8 : 8 ≤ q) (hq : q < 16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  have hpc' := c.endInv_group q (by omega) hs
  obtain ⟨hB, hlen, -⟩ := hs
  have hR := hB.1
  have hr : vrun (gX q (c.kOf q)) 5 = some (nextDispR q) := (c.groupFacts hds q (by omega)).disp
  have hbound := gX_lt q (c.kOf q) (by omega) (c.kOf_nRank hds q (by omega))
  have h16 : s.getReg .x16 = ~~~((r5V V).extractLsb' 0 64) := by
    rw [r5V_lo]; exact (hR _ (by decide +kernel)).trans he.lo
  have h17 : s.getReg .x17 = ~~~((r5V V).extractLsb' 64 64) ^^^ hiMask := by
    rw [r5V_hi]; exact (hR _ (by decide +kernel)).trans he.hi
  have h6 : s.getReg .x6 = 520192#64 := (hR _ (by decide +kernel)).trans he.mask5
  have base_of : ∀ t, RegsExcept s t [.x14] → Frame s t (fun _ => False) →
      c.Base s0 (c.Wr (3*(q+1))) acc t := by
    intro t rt ft
    rw [show 3*(q+1) = 3*q+2+1 by omega]
    exact c.base_disp (by omega) hB rt ft
  unfold DispOutR6
  set v := r5V V with hvdef
  by_cases hq8 : q = 8
  · subst q
    rw [gValid_r5 V 9 (by omega) (by omega), gRank_r5 V 9 (by omega) (by omega), ← topRank_r5V V 9 (by omega) (by omega),
      ← hvdef]
    have hr9 : nextDispR 8 = dispatch9R := by simp [nextDispR]
    rw [hr9] at hr
    obtain ⟨t,st,pt,rt,ft⟩ := dispatch9_step hbound hr s v hpc' h17 h6
    have hr9 : Search.topRank (r5V V) (8+1)=v.toNat/2^63%2+2*(v.toNat/2^64%64) := topRank9 v
    have hd9 : dspR6 (8+1)=4 := rfl
    rw [hr9,hd9]
    have hb2 : v.toNat/2^63%2<2 := Nat.mod_lt _ (by decide +kernel)
    have hu : v.toNat/2^64%64<64 := Nat.mod_lt _ (by decide +kernel)
    by_cases hu63 : v.toNat/2^64%64=63
    · refine ⟨fun hv => by omega,fun _ => ⟨3,t,st,by omega,fetch_fault t ?_⟩⟩
      rw [pt,hu63]; exact g9_fault
    · set u := v.toNat/2^64%64 with hudef
      have hpc9 : t.pc=pcOf (cellW 9 (2*u)) := by rw [pt]; exact g9_cell u (by omega)
      have h16t : t.getReg .x16= ~~~(v.extractLsb' 0 64) := (rt.get (by decide +kernel)).trans h16
      obtain ⟨z,sz,pz,rz,fz⟩ := bge9_step (2*u) (by omega) (by omega) t v hpc9 h16t
      have rtz : RegsExcept s z [.x14] := fun x hx => (rz.get (by simp)).trans (rt x hx)
      have ftz : Frame s z (fun _ => False) := (ft.trans fz).mono (by intro A _ h; simpa using h)
      have st5 : Steps vimage s 4 4 z := st.trans sz
      by_cases hb : v.toNat/2^63%2=1
      · rw [if_pos hb] at pz
        rw [hb]
        by_cases hu62 : u=62
        · refine ⟨fun hv => by omega,fun _ => ⟨4,z,st5,by omega,fault_top_fetch 9 (by omega) (by omega) z ?_⟩⟩
          rw [pz,hu62]; decide +kernel
        · refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
          rw [pz]
          have he9 : entW (8+1) (1+2*u)=cellW 9 (1+2*u) := by
            unfold entW; rw [if_neg (by omega)]; rfl
          rw [he9, cellW9, cellW9]
          unfold pcOf
          exact congrArg (BitVec.ofNat 64) (by omega)
      · have hb0 : v.toNat/2^63%2=0 := by omega
        rw [if_neg hb] at pz
        rw [hb0]
        refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
        rw [pz]
        have he9 : entW (8+1) (0+2*u)=cellW 9 (2*u)+1 := by
          unfold entW; rw [if_pos (by omega)]; simp
        rw [he9]
  · by_cases hq15 : q = 15
    · -- q15 -> the r7 pair (#938's dispatch into group 8, bits 56..62)
      subst q
      rw [gValid_pair, gRank_pair, ← topRank_r5V_pair V, ← hvdef]
      have hr' : nextDispR 15 = dispatchR 8 := by simp [nextDispR]
      rw [hr'] at hr
      obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (q := 8) (by omega) (by omega) hbound hr s v hpc' h16 h17 h6
      have hd : dspR6 (15+1)=3 := rfl
      rw [hd]
      have hk := topRank_lt v 8
      by_cases h49 : Search.topRank v 8 < 49
      · refine ⟨fun _ => ⟨t,st,base_of t rt ft,by omega,?_⟩,fun hv => absurd h49 hv⟩
        rw [pt, cell_value_pair _ (by omega)]; unfold entW; simp
      · refine ⟨fun hv => absurd hv h49, fun _ => ⟨3,t,st,by omega,?_⟩⟩
        rcases pair_landing _ hk t pt with ⟨h, -⟩ | hf
        · exact absurd h h49
        · exact hf
    · have hr' : nextDispR q = dispatchR (q+1) := by
        simp [nextDispR, show q ≠ 0 by omega, show ¬ q < 8 by omega, hq8, show q < 15 by omega]
      rw [hr'] at hr
      rw [gValid_r5 V (q+1) (by omega) (by omega), gRank_r5 V (q+1) (by omega) (by omega),
        ← topRank_r5V V (q+1) (by omega) (by omega), ← hvdef]
      obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (q := q+1) (by omega) (by omega) hbound hr s v hpc' h16 h17 h6
      have hd : dspR6 (q+1)=3 := by
        unfold dspR6; simp only [show q+1 ≠ 1 by omega, show ¬ q+1 < 9 by omega, show q+1 ≠ 9 by omega, if_false]
      rw [hd]
      have hk := topRank_lt v (q+1)
      refine ⟨fun hv => ⟨t,st,base_of t rt ft,by omega,?_⟩,fun hv => ⟨3,t,st,by omega,?_⟩⟩
      · rw [pt,cell_value _ _ (by omega) (by omega) (by omega)]
        have e : entW (q+1) (Search.topRank v (q+1)) = cellW (q+1) (Search.topRank v (q+1)) := by
          unfold entW; rw [if_neg (fun h => hq8 (by omega))]; rfl
        rw [e]
      · by_cases h125 : Search.topRank v (q+1)=125
        · apply fault_top_fetch (q+1) (by omega) (by omega) t
          rw [pt,h125]
          exact fault125_value _ (by omega)
        · by_cases h126 : Search.topRank v (q+1)=126
          · by_cases hE : 1024≤entOff (q+1)
            · apply fault_top126_fetch (q+1) (by omega) (by omega) hE t
              rw [pt,h126]
              exact fault126_value _ (by omega) hE
            · apply fetch_fault t
              rw [pt,h126]
              exact fault126_low _ (by omega)
          · apply fetch_outside t
            rw [pt]
            exact fault_value _ _ (by omega) (by omega) hk
/-- Every T51 group transition `q -> q+1` (1 <= q < 16; group 0's is `end_dispatch0`). -/
theorem end_dispatchR6 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h1 : 1 ≤ q) (hq : q < 16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  by_cases h8 : q < 8
  · exact c.end_dispatch6 hc hds he q h1 h8 acc s hs
  · exact c.end_dispatch5 hds he q (by omega) hq acc s hs
theorem data_sum_le (c : NCtx) (hds : c.DigitsOk) : ((List.range 50).map c.dig).sum ≤ 231 := by
  have h : ∀ n, n ≤ 50 → ((List.range n).map c.dig).sum ≤ ((List.range n).map topMax).sum := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
      have h1 := hds n (by omega)
      have h2 := ih (by omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  have h2 : ((List.range 50).map topMax).sum = 231 := by decide +kernel
  exact (h 50 le_rfl).trans h2.le
/-- End of the r7 pair (chain 49 done, s8 = T - data sum): the checksum dispatch reaches chain 50's arm for digit
`T - ds` when that lies in 0..5, otherwise it faults. -/
theorem end_ck (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 49 acc s) (ds : Nat) (hdsum : ((List.range 50).map c.dig).sum = ds)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) :
    (topT - 5 ≤ ds ∧ ds ≤ topT → ∃ t, Steps vimage s 3 3 t ∧ c.Base s0 (c.Wr (49+1)) acc t ∧ acc.length = 49+1 ∧
        t.pc = pcOf (ckArm (topT - ds))) ∧
      (¬ (topT - 5 ≤ ds ∧ ds ≤ topT) → ∃ t, Steps vimage s 3 3 t ∧ fetch vimage t = none) := by
  have he49 : c.endPc 49 = gX 16 (c.kOf 16) := by
    have := c.endPc_group 16 (by omega); simpa [nCh] using this
  have hpc' : s.pc = pcOf (gX 16 (c.kOf 16)) := by rw [hs.2.2, he49]
  obtain ⟨hB, hlen, -⟩ := hs
  have hr : vrun (gX 16 (c.kOf 16)) 5 = some ckDispR := by
    have := (c.groupFacts hds 16 (by omega)).disp
    simpa [nextDispR] using this
  have hd : ds ≤ 231 := hdsum ▸ c.data_sum_le hds
  have hbound := gX_lt 16 (c.kOf 16) (by omega) (c.kOf_nRank hds 16 (by omega))
  obtain ⟨t, st, pt, rt, ft⟩ := ck_dispatch_step hbound hr s ds hd hpc' h24
  have base_of : c.Base s0 (c.Wr (49+1)) acc t := c.base_disp (by omega) hB rt ft
  refine ⟨fun hv => ⟨t, st, base_of, hlen, ?_⟩, fun hv => ⟨t, st, ?_⟩⟩
  · have hw : ckWord ds = ckArm (topT - ds) := by unfold ckWord ckArm topT at *; omega
    rw [pt, hw]
  · rcases ck_landing ds (by omega) with ⟨h1, h2, -⟩ | hf
    · exact absurd ⟨h1, h2⟩ hv
    · exact hf t pt
/-- The NCtx digits of chains 0..49 are the spec's decoded digits of the selected half `V`. -/
def Fit6 (c : NCtx) (V : Digest) : Prop := ∀ i, i < 50 → c.dig i = T3.coreDigit 0 V i
theorem coreDigit_top (V : Digest) (q k : Nat) (hq : q < 16) (hk : k < 3) :
    T3.coreDigit 0 V (3*q+k) = if q < 9 then T3.r6Rank V q / 6^k % 6 else T3.r5Rank V q / 5^k % 5 := by
  unfold T3.coreDigit
  simp only [if_true, show (3*q+k)/3 = q by omega, show (3*q+k)%3 = k by omega]
  by_cases h9 : q < 9
  · simp [h9, show 3*q+k < 27 by omega]
  · simp [h9, show ¬ 3*q+k < 27 by omega, show 3*q+k < 48 by omega]
theorem coreDigit_pair (V : Digest) (k : Nat) (hk : k < 2) :
    T3.coreDigit 0 V (48+k) = T3.r7Rank V / 7^k % 7 := by
  unfold T3.coreDigit
  simp [show ¬ 48+k < 27 by omega, show ¬ 48+k < 48 by omega, show 48+k < 50 by omega]
theorem fit6_le (c : NCtx) {V : Digest} (hf : c.Fit6 V) (i : Nat) (hi : i < 50) : c.dig i ≤ topMax i := by
  rw [topMax_mx i hi]
  by_cases h48 : i < 48
  · obtain ⟨q, k, hk, rfl⟩ : ∃ q k, k < 3 ∧ i = 3*q+k := ⟨i/3, i%3, by omega, by omega⟩
    rw [hf _ hi, coreDigit_top V q k (by omega) hk]
    unfold mx
    rw [show (3*q+k)/3 = q by omega]
    by_cases h9 : q < 9
    · simp only [h9, if_true]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    · simp only [h9, if_false, show q < 16 by omega, if_true]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 2 ∧ i = 48+k := ⟨i-48, by omega, by omega⟩
    rw [hf _ hi, coreDigit_pair V k hk, show (48+k)/3 = 16 by omega]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
theorem gRank_lt (V : Digest) (q : Nat) (hq : q < 17) (hv : gValid V q) : gRank V q < nRank q := by
  unfold gValid at hv; unfold gRank nRank
  by_cases h9 : q < 9
  · simp only [h9, if_true] at hv ⊢
    simp only [show q ≠ 16 by omega, if_false, mx, h9, if_true]
    unfold T3.r6Valid at hv; unfold T3.r6Rank
    have := Nat.mod_lt (T3.topCode V / 2 ^ T3.r6Shift q) (show 0 < 256 by norm_num)
    unfold T3.r6Raw at hv ⊢
    split_ifs at hv ⊢ <;> simp at hv <;> omega
  · by_cases h16 : q < 16
    · simp only [h9, h16, if_false, if_true] at hv ⊢
      simp only [show q ≠ 16 by omega, if_false, mx, h9, h16, if_true]; omega
    · have : q = 16 := by omega
      subst this
      simp only [h9, h16, if_false] at hv ⊢
      simpa using hv
/-- With fitting digits, the NCtx group index of a valid group is the field's rank. -/
theorem fit_rank6 (c : NCtx) {V : Digest} (hf : c.Fit6 V) (q : Nat) (hq : q < 17) (hv : gValid V q) :
    c.kOf q = gRank V q := by
  have hl := gRank_lt V q hq hv
  by_cases h16 : q = 16
  · subst h16
    unfold kOf; rw [if_pos rfl, hf 48 (by omega), hf 49 (by omega)]
    have e0 := coreDigit_pair V 0 (by omega)
    have e1 := coreDigit_pair V 1 (by omega)
    simp only [Nat.add_zero] at e0
    rw [e0, show (49:Nat) = 48+1 from rfl, e1]
    rw [gRank_pair] at hl ⊢
    unfold nRank at hl; simp at hl
    norm_num; omega
  rw [c.kOf_triple q (by omega), hf (3*q) (by omega), hf (3*q+1) (by omega), hf (3*q+2) (by omega)]
  have e0 := coreDigit_top V q 0 (by omega) (by omega)
  have e1 := coreDigit_top V q 1 (by omega) (by omega)
  have e2 := coreDigit_top V q 2 (by omega) (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2]
  unfold nRank at hl
  unfold gRank at hl ⊢
  by_cases h9 : q < 9
  · simp only [h9, if_true, mx, h16, if_false] at hl ⊢; norm_num at hl ⊢; omega
  · simp only [h9, if_false, mx, show q < 16 by omega, if_true, h16] at hl ⊢; norm_num at hl ⊢; omega
/-- Group transition into the next group's `GroupIn` (valid field), 1 <= q < 16. -/
theorem end_dispatchR6_in (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (hf : c.Fit6 V) (q : Nat) (h1 : 1 ≤ q) (hq : q < 16) (hv : gValid V (q+1))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃ t, Steps vimage s (dspR6 (q+1)) (dspR6 (q+1)) t ∧ c.GroupIn s0 (q+1) acc t := by
  obtain ⟨t, st, hB, hl, pt⟩ := (c.end_dispatchR6 hc hds he q h1 hq acc s hs).1 hv
  refine ⟨t, st, hB, hl, ?_⟩
  rw [pt]; unfold entPc; rw [c.fit_rank6 hf (q+1) (by omega) hv]
/-- Group transition into an invalid next group: the run faults within 5 steps. -/
theorem end_dispatchR6_bad (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h1 : 1 ≤ q) (hq : q < 16) (hv : ¬ gValid V (q+1))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none :=
  (c.end_dispatchR6 hc hds he q h1 hq acc s hs).2 hv
/-- Group 0's transition into group 1's `GroupIn` on the base `setTab s0` (valid field). -/
theorem end_dispatch0_in (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded0 V s0) (hk : ∀p∈c.known,s0.getReg p.1=p.2) (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (hf : c.Fit6 V) (hv : gValid V 1) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 2 acc s) :
    ∃ t, Steps vimage s (dspR6 1) (dspR6 1) t ∧ c.GroupIn (setTab s0) 1 acc t := by
  obtain ⟨t, st, hB, hl, pt⟩ := (c.end_dispatch0 hc hds he hk hmask acc s hs).1 hv
  refine ⟨t, st, hB, hl, ?_⟩
  rw [pt]; unfold entPc; rw [c.fit_rank6 hf 1 (by omega) hv]
theorem g0_valid (W : Word) (s : MachineState) (h40 : 40 ≤ W.toNat % 256)
    (hpc : s.pc = (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) :
    s.pc = pcOf (cellW 0 (W.toNat % 256 - 40)) := by
  rw [g0_target W _ rfl (by omega), g0_cell _ (by omega)] at hpc
  rw [hpc, cell6_valid 0 _ (by omega) (by simp [raw6Valid, h40])]; rfl
theorem g0_bad (W : Word) (s : MachineState) (h40 : W.toNat % 256 < 40)
    (hpc : s.pc = (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) : fetch vimage s = none := by
  rcases g0_landing W s hpc with ⟨h, -⟩ | h
  · omega
  · exact h
/-- The prologue's g0 dispatch (on a6 = the low half of `V`) at NCtx level. -/
theorem g0_group (c : NCtx) {V : Digest} (hf : c.Fit6 V) (s : MachineState)
    (hpc : s.pc = ((((V.extractLsb' 0 64) <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) :
    (gValid V 0 → s.pc = pcOf (c.entPc 0)) ∧ (¬ gValid V 0 → fetch vimage s = none) := by
  have hr := g0_raw V
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have h40 := (gValid_g0 V).mp hv
    rw [g0_valid _ s (by omega) hpc, hr]
    unfold entPc; rw [c.fit_rank6 hf 0 (by omega) hv, gRank_g0]
    unfold entW; simp
  · have h40 : ¬ 40 ≤ T3.r6Raw V 0 := fun h => hv ((gValid_g0 V).mpr h)
    exact g0_bad _ s (by omega) hpc
/-- Group 0's cell word `addi s8,zero,T-kss`: the T51 top-region entry into chain 0. -/
theorem g0_entry (c : NCtx) (hds : c.DigitsOk) {b : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.GroupIn b 0 acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v 0)) 0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hk := c.kOf_nRank hds 0 (by omega)
  have hchk := s8Run_at 0 (c.kOf 0) (by omega) hk
  rw [if_pos rfl] at hchk
  have hrun := rOK_eq hchk
  have hp : entW 0 (c.kOf 0)<257181 := by have := entW_lt 0 _ (by omega) hk; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  set r := guardR (c.kOf 0) with hr
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,guardR]
      rw [RegFile.get_set_self _ _ (by decide +kernel),set24_24]
      simp only [E.eval]
      rw [c.s8v0 hds]
    · simp only [hr,guardR]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [Result.toState_getMem,set24_mem]
    simp only [hr,guardR]
    rw [memEval_nil]
    exact hF A hA hn
  · have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
      rw [Result.toState_getMem]; simp [hr,guardR,memEval_nil]
    exact (hS j hj).frame hfr (by unfold slot; split <;> omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,guardR,E.eval]
    unfold startPc leadPc leadOff entW
    simp
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
end
-- ==== merged from T3M_Verify_Nonbinary_TopRun ====
section

section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem set24_set24 (b : MachineState) (x y : Word) : set24 (set24 b x) y=set24 b y := by
  unfold set24
  rw [setReg_of_ne _ _ (by decide +kernel),setReg_of_ne b _ (by decide +kernel),setReg_of_ne b _ (by decide +kernel)]
  simp only
  congr 1
  funext r
  by_cases h : r=.x24 <;> simp [h]
/-- `setTab` (x29, x18) and `set24` (x24) commute. -/
theorem setTab_set24 (b : MachineState) (x : Word) : setTab (set24 b x) = set24 (setTab b) x := by
  unfold setTab set24
  rw [setReg_of_ne _ _ (by decide +kernel), setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel),
    setReg_of_ne _ _ (by decide +kernel), setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel)]
  simp only
  congr 1
  funext r
  by_cases h24 : r=.x24 <;> by_cases h18 : r=.x18 <;> simp_all
theorem chainsCost_add' (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]
theorem goodQ_fault {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch vimage s=none) :
    Verify.GoodQP P s 1 0 Q A (pure (false, 0)) := by
  intro F hF
  have hF' : F=(F-1)+1 := by omega
  refine ⟨?_,fun hash => ?_⟩
  · rw [hF',execute_fetch_none (F-1) hf,map_pure]; rfl
  · have he : evalWithAnswerFn hash (Riscv.execute (F-1+1) vimage s)=⟨.failure,s,0,0,0⟩ := by
      rw [execute_fetch_none (F-1) hf]; rfl
    rw [hF',he]
    exact ⟨by simp,Nat.zero_le _,fun h _ => by simp at h⟩
/-- Dispatch overhead of groups `q+1 .. q+k-1` (entry word + dispatch per transition; T51 `dspR6`). -/
def ov : Nat → Nat → Nat
  | _, 0 => 0
  | _, 1 => 1
  | q, k+2 => 1+dspR6 (q+1)+ov (q+1) (k+1)
theorem ov_succ (q k : Nat) (hk : 1 ≤ k) : ov q (k+1)=1+dspR6 (q+1)+ov (q+1) k := by
  obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩; rfl
theorem nCh_lt (q : Nat) (hq : q < 16) : nCh q = 3 := by unfold nCh; rw [if_neg (by omega)]
/-- Base state of group `q`'s chains: group 0 runs on `s0`, the later groups on `setTab s0` (t4/s2 loaded by group 0's
dispatch); x24 holds the reverse checksum after the group's cell. -/
def bq (c : NCtx) (s0 : MachineState) (q : Nat) : MachineState :=
  if q = 0 then set24 s0 (c.s8v 0) else set24 (setTab s0) (c.s8v q)
/-- Groups `q .. n-1` (1 <= q, n <= 16: all triples) on the base `S = setTab s0`. -/
theorem groups_from (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {S : MachineState}
    (hk : ∀p∈c.known,S.getReg p.1=p.2) (h0 : c.Orig0 S) {V : Digest} (he : Encoded6 V S) (hf : c.Fit6 V)
    (n : Nat) (hn : n ≤ 16) (hval : ∀ q, q<n → gValid V q)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (set24 S (c.s8v (n-1))) (3*(n-1)+2) acc t → Verify.GoodQP P t N C Q A (K acc)) :
    ∀ k q, 1 ≤ q → q+k=n → 0<k → ∀ acc s,c.GroupIn (set24 S (c.s8v (q-1))) q acc s →
      Verify.GoodQP P s (N+126*k) (C+c.chainsCost (3*q) (3*k)+ov q k) Q (A+c.chainsCost (3*q) (3*k)+ov q k)
        (Verify.ccM ((List.range' (3*q) (3*k)).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro q _ _ h; omega
  | succ k ih =>
    intro q hq1 hqk _ acc s hs
    have hq : q<16 := by omega
    obtain ⟨q',rfl⟩ : ∃q',q=q'+1 := ⟨q-1,by omega⟩
    obtain ⟨t,hst,hin⟩ := c.entry_step hc hds q' (by omega) (set24_24 _ _) acc s (by simpa using hs)
    rw [set24_set24] at hin
    have hkB := set24_known c (c.s8v (q'+1)) hk
    have h0B := set24_orig c (c.s8v (q'+1)) h0
    have heB := set24_encoded6 (c.s8v (q'+1)) he
    have hn3 := nCh_lt (q'+1) (by omega)
    rw [show 3*(k+1)=3+3*k by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
    have ec := c.chainsCost_add' (3*(q'+1)) 3 (3*k)
    by_cases hk0 : k=0
    · subst hk0
      have hqn : q'+1=n-1 := by omega
      have H := c.group_good hc hds hkB h0B (q'+1) (by omega) K N C A Q
        (by rw [hn3, show 3*(q'+1)+3-1 = 3*(q'+1)+2 by omega]; rw [← hqn] at hK; exact hK)
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide +kernel) acc t hin
      have H' := Verify.GoodQP.steps hst H
      simp only [Nat.mul_zero,Nat.add_zero,List.range'_zero,List.foldlM_nil,bind_pure,Verify.ccM_pure] at H' ⊢
      have h1 : ov (q'+1) (0+1)=1 := rfl
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
    · have hov := ov_succ (q'+1) k (by omega)
      simp only [show q'+1+1=q'+2 from rfl] at hov
      have hd := dspR6_le (q'+2)
      have H := c.group_good hc hds hkB h0B (q'+1) (by omega)
        (fun ends => Verify.ccM ((List.range' (3*(q'+1)+3) (3*k)).foldlM c.chainF ends) K)
        (N+126*k+dspR6 (q'+2)) (C+c.chainsCost (3*(q'+1)+3) (3*k)+ov (q'+2) k+dspR6 (q'+2))
        (A+c.chainsCost (3*(q'+1)+3) (3*k)+ov (q'+2) k+dspR6 (q'+2)) Q
        (fun ends u hu => by
          rw [hn3, show 3*(q'+1)+3-1 = 3*(q'+1)+2 by omega] at hu
          obtain ⟨u',st,hu'⟩ := c.end_dispatchR6_in hc hds heB hf (q'+1) (by omega) (by omega)
            (hval (q'+2) (by omega)) ends u hu
          have e2 : dspR6 (q'+1+1)=dspR6 (q'+2) := rfl
          rw [e2] at st
          have H := ih (q'+2) (by omega) (by omega) (by omega) ends u' (by simpa using hu')
          rw [show 3*(q'+2)=3*(q'+1)+3 by omega] at H
          refine (Verify.GoodQP.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide +kernel) acc t hin
      have H' := Verify.GoodQP.steps hst H
      rw [ec]
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
/-- Groups `0 .. n-1` (1 <= n <= 16) from group 0's entry (base `s0`; group 0's dispatch switches to `setTab`). -/
theorem groups_zero (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (n : Nat) (hn : n ≤ 16) (hn1 : 1 ≤ n) (hval : ∀ q, q<n → gValid V q)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (c.bq s0 (n-1)) (3*(n-1)+2) acc t → Verify.GoodQP P t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (N+126*n) (C+c.chainsCost 0 (3*n)+ov 0 n) Q (A+c.chainsCost 0 (3*n)+ov 0 n)
      (Verify.ccM ((List.range' 0 (3*n)).foldlM c.chainF []) K) := by
  obtain ⟨t,hst,hin⟩ := c.g0_entry hds [] s hs
  have hkB := set24_known c (c.s8v 0) hk
  have h0B := set24_orig c (c.s8v 0) h0
  have heB := set24_encoded0 (c.s8v 0) he
  have hn0 := nCh_lt 0 (by omega)
  obtain ⟨m,rfl⟩ : ∃m,n=m+1 := ⟨n-1,by omega⟩
  rw [show 3*(m+1)=3+3*m by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 3 (3*m)
  by_cases hm0 : m=0
  · subst hm0
    have H := c.group_good hc hds hkB h0B 0 (by omega) K N C A Q
      (by rw [hn0]; simpa [bq] using hK)
      3 0 (le_refl _) (by rw [hn0]) (by decide) [] t (by simpa using hin)
    have H' := Verify.GoodQP.steps hst H
    simp only [Nat.mul_zero,Nat.add_zero,List.range'_zero,List.foldlM_nil,bind_pure,Verify.ccM_pure] at H' ⊢
    have h1 : ov 0 (0+1)=1 := rfl
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
  · have hov := ov_succ 0 m (by omega)
    simp only [Nat.zero_add] at hov
    have hd1 : dspR6 1=5 := rfl
    have hmB : (set24 s0 (c.s8v 0)).getMem 0xffbdf0#64 = 65280#64 := by rw [set24_mem]; exact hmask
    have hkS := setTab_known c hk
    have h0S := setTab_orig c h0
    have heS := setTab_encoded he
    have H := c.group_good hc hds hkB h0B 0 (by omega)
      (fun ends => Verify.ccM ((List.range' (0+3) (3*m)).foldlM c.chainF ends) K)
      (N+126*m+5) (C+c.chainsCost 3 (3*m)+ov 1 m+5) (A+c.chainsCost 3 (3*m)+ov 1 m+5) Q
      (fun ends u hu => by
        rw [hn0] at hu
        obtain ⟨u',st,hu'⟩ := c.end_dispatch0_in hc hds heB hkB hmB hf (hval 1 (by omega)) ends u hu
        rw [setTab_set24] at hu'
        have hK' : ∀ acc t, c.EndInv (set24 (setTab s0) (c.s8v (m+1-1))) (3*(m+1-1)+2) acc t →
            Verify.GoodQP P t N C Q A (K acc) := by
          intro acc t ht; apply hK; unfold bq; rw [if_neg (by omega)]; exact ht
        have H := c.groups_from hc hds hkS h0S heS hf (m+1) hn hval K N C A Q hK' m 1 (le_refl _) (by omega)
          (by omega) ends u' (by simpa using hu')
        simp only [Nat.mul_one] at H
        rw [hd1] at st
        refine (Verify.GoodQP.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
      3 0 (le_refl _) (by rw [hn0]) (by decide) [] t (by simpa using hin)
    have H' := Verify.GoodQP.steps hst H
    simp only [Nat.zero_add] at H' ec ⊢
    rw [ec]
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
def topP (c : NCtx) : M (List Digest) := (List.range' 0 51).foldlM c.chainF []
/-- After the 51 top chains (campaign T51): pc at the final tail `ckTail d50` of the checksum arm. Registers outside
`chainRegs`, x24 (reverse checksum) and x29/x18 (loaded by group 0's dispatch) are kept. -/
def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x24 → x ≠ .x29 → x ≠ .x18 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 51) ∧ acc.length=51 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧
  s.pc = pcOf (ckTail (c.dig 50)) ∧ s.getReg .x24=c.s8v 16 ∧ s.getReg .x29=65280#64 ∧ s.getReg .x18=856064#64
/-- The checksum digit of a context: chain 50's digit is `topT - (data digit sum)` whenever that lies in `0..5`. -/
def CkOk (c : NCtx) : Prop :=
  ∀ ds, ((List.range 50).map c.dig).sum = ds → topT-5 ≤ ds → ds ≤ topT → c.dig 50 = topT-ds
theorem s8v16_eq (c : NCtx) : c.s8v 16 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 50).map c.dig).sum) := rfl
/-- The r7 pair (entered from the end of group 15) and the checksum chain 50: q15's dispatch (3), the pair's cell
word (1), chains 48/49, the checksum dispatch (3), chain 50. -/
theorem pair_ck_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (hck : c.CkOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hv16 : gValid V 16)
    (hin : topT-5 ≤ ((List.range 50).map c.dig).sum ∧ ((List.range 50).map c.dig).sum ≤ topT)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQP P t N C Q A (K acc))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv (c.bq s0 15) 47 acc s) :
    Verify.GoodQP P s (N+130) (C+c.chainsCost 48 3+7) Q (A+c.chainsCost 48 3+7)
      (Verify.ccM ((List.range' 48 3).foldlM c.chainF acc) K) := by
  have hkS := setTab_known c hk
  have h0S := setTab_orig c h0
  have heS := setTab_encoded he
  have hb15 : c.bq s0 15 = set24 (setTab s0) (c.s8v 15) := by unfold bq; rw [if_neg (by omega)]
  rw [hb15] at hs
  have hk15 := set24_known c (c.s8v 15) hkS
  have h015 := set24_orig c (c.s8v 15) h0S
  have he15 := set24_encoded6 (c.s8v 15) heS
  -- q15 -> the pair's cell (3 steps), the cell's s8 word (1 step)
  obtain ⟨u,st1,hu⟩ := c.end_dispatchR6_in hc hds he15 hf 15 (by omega) (by omega) hv16 acc s
    (by simpa using hs)
  obtain ⟨w,st2,hw⟩ := c.entry_step hc hds 15 (by omega) (set24_24 _ _) acc u hu
  rw [set24_set24] at hw
  have hd16 : dspR6 (15+1) = 3 := rfl
  rw [hd16] at st1
  set B := set24 (setTab s0) (c.s8v 16) with hB
  have hkB : ∀p∈c.known,B.getReg p.1=p.2 := set24_known c (c.s8v 16) hkS
  have h0B : c.Orig0 B := set24_orig c (c.s8v 16) h0S
  have hn16 : nCh 16 = 2 := rfl
  rw [show (3:Nat) = 2+1 from rfl, ← List.range'_append_1, List.foldlM_append, Verify.ccM_bind,
    show (48+2:Nat) = 50 from rfl]
  have ec := c.chainsCost_add' 48 2 1
  rw [show (48+2:Nat) = 50 from rfl] at ec
  have H := c.group_good hc hds hkB h0B 16 (by omega)
    (fun ends => Verify.ccM ((List.range' 50 1).foldlM c.chainF ends) K)
    (N+46) (C+c.chainsCost 50 1+3) (A+c.chainsCost 50 1+3) Q
    (fun ends u2 hu2 => by
      rw [hn16] at hu2
      have h24 : u2.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 50).map c.dig).sum) := by
        rw [hu2.1.1 .x24 (by decide +kernel), hB, set24_24]; rfl
      obtain ⟨t3,st3,hB3,hlen3,pt3⟩ := (c.end_ck hds ends u2 (by simpa using hu2) _ rfl h24).1 hin
      have hd50 := hck _ rfl hin.1 hin.2
      have hcin : c.ChainIn B 50 ends t3 :=
        ⟨hB3, hlen3, by rw [pt3]; simp [startPc, hd50]⟩
      rw [List.range'_succ,List.foldlM_cons]
      simp only [chainF,bind_assoc,pure_bind,Verify.ccM_bind,List.range'_zero,List.foldlM_nil,Verify.ccM_pure]
      have H := c.chain_good hc hds hkB h0B 50 (by omega) ends K N C A Q
        (fun v t' ht' => hK _ t' (by
          obtain ⟨⟨hR,hF,hS⟩,hl,hp⟩ := ht'
          refine ⟨fun x hx h24 h29 h18 => ?_, ?_, hl, hS, ?_, ?_, ?_, ?_⟩
          · rw [hR x hx, hB, set24_regs _ _ _ h24, setTab_regs _ _ h29 h18]
          · intro A hA hn
            rw [hF A hA hn, hB, set24_mem, setTab_mem]
          · rw [hp]; simp [endPc]
          · rw [hR .x24 (by decide +kernel), hB, set24_24]
          · rw [hR .x29 (by decide +kernel), hB, set24_regs _ _ _ (by decide), setTab_29]
          · rw [hR .x18 (by decide +kernel), hB, set24_regs _ _ _ (by decide), setTab_18]))
        t3 hcin
      have e1 : c.chainsCost 50 1=c.chainCost 50 (c.dig 50) := by simp [chainsCost]
      have H2 := Verify.GoodQP.steps st3 H
      rw [e1]
      refine H2.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
    2 48 (le_refl _) (by omega) (by omega) acc w (by simpa using hw)
  have H' := Verify.GoodQP.steps (st1.trans st2) H
  rw [ec]
  refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem ov_16 : ov 0 16 = 71 := by decide +kernel
/-- The whole T51 top region for a valid word: 16 groups, the r7 pair, the checksum chain. -/
theorem top_full (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (hck : c.CkOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (hval : ∀ q, q<17 → gValid V q)
    (hin : topT-5 ≤ ((List.range 50).map c.dig).sum ∧ ((List.range 50).map c.dig).sum ≤ topT)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQP P t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (N+2146) (C+c.chainsCost 0 51+78) Q (A+c.chainsCost 0 51+78)
      (Verify.ccM c.topP K) := by
  unfold topP
  rw [show (51:Nat)=3*16+3 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 (3*16) 3
  have H := c.groups_zero hc hds hk h0 he hf hmask 16 (le_refl _) (by decide +kernel) (fun q hq => hval q (by omega))
    (fun ends => Verify.ccM ((List.range' (0+3*16) 3).foldlM c.chainF ends) K)
    (N+130) (C+c.chainsCost 48 3+7) (A+c.chainsCost 48 3+7) Q
    (fun acc t ht => c.pair_ck_good hc hds hck hk h0 he hf (hval 16 (by omega)) hin K N C A Q hK acc t
      (by simpa using ht))
    s hs
  simp only [Nat.zero_add] at H ec ⊢
  rw [show (3*16 : Nat)=48 from rfl] at ec H ⊢
  rw [ov_16] at H
  rw [ec]
  refine H.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem goodQ_vacuous {s : MachineState} {N C A : Nat} {X : OracleComp Legacy.HashSpec Verify.Obs}
    (h : Verify.GoodQP P s N C False A X) (Q' : Prop) (A' : Nat) : Verify.GoodQP P s N C Q' A' X := by
  intro F hF
  obtain ⟨h1,h2⟩ := h F hF
  exact ⟨h1,fun hash => ⟨(h2 hash).1,(h2 hash).2.1,fun hs hok => ((h2 hash).2.2 hs hok).1.elim⟩⟩
theorem ov_le (j : Nat) (hj : j ≤ 16) : ov 0 j ≤ 71 := by interval_cases j <;> decide +kernel
/-- Campaign T51: an invalid group `j` (1..16; 16 = the r7 pair) after valid groups faults at its dispatch. -/
theorem top_bad_group (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ 16) (hval : ∀ q, q<j → gValid V q)
    (hbad : ¬ gValid V j) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (126*j+6) (c.chainsCost 0 (3*j)+ov 0 j+5) Q A
      (Verify.ccM ((List.range' 0 (3*j)).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 (3*j)+ov 0 j) ?_ Q A
  have H := c.groups_zero hc hds hk h0 he hf hmask j (by omega) hj1 hval K 6 5 0 False
    (fun acc t ht => by
      rw [hK acc]
      have hb' : ¬ gValid V (j-1+1) := by rw [show j-1+1=j by omega]; exact hbad
      obtain ⟨k,z,stz,hk5,fz⟩ : ∃ k z, Steps vimage t k k z ∧ k ≤ 5 ∧ fetch vimage z = none := by
        by_cases hj0 : j-1 = 0
        · have ht' : c.EndInv (set24 s0 (c.s8v 0)) 2 acc t := by
            have : c.bq s0 (j-1) = set24 s0 (c.s8v 0) := by unfold bq; rw [if_pos hj0]
            rw [this, hj0] at ht; simpa using ht
          exact (c.end_dispatch0 hc hds (set24_encoded0 _ he) (set24_known c _ hk) (by rw [set24_mem]; exact hmask)
            acc t ht').2 (by rw [hj0] at hb'; simpa using hb')
        · have ht' : c.EndInv (set24 (setTab s0) (c.s8v (j-1))) (3*(j-1)+2) acc t := by
            have : c.bq s0 (j-1) = set24 (setTab s0) (c.s8v (j-1)) := by unfold bq; rw [if_neg hj0]
            rw [this] at ht; exact ht
          exact c.end_dispatchR6_bad hc hds (set24_encoded6 _ (setTab_encoded he)) (j-1) (by omega) (by omega) hb' acc t ht'
      have R := goodQ_fault (P := P) (Q := False) (A := 0) fz
      refine (Verify.GoodQP.steps stz R).mono ?_ ?_ ?_
      · omega
      · omega
      · intro h; exact h.elim)
    s hs
  exact H.mono (by omega) (by omega) (fun h => ⟨h,le_refl _⟩)
/-- Campaign T51: all 17 groups valid but the checksum digit out of range: the checksum dispatch faults. -/
theorem top_bad_ck (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (hval : ∀ q, q<17 → gValid V q)
    (hout : ¬ (topT-5 ≤ ((List.range 50).map c.dig).sum ∧ ((List.range 50).map c.dig).sum ≤ topT))
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (126*16+88) (c.chainsCost 0 50+ov 0 16+7) Q A
      (Verify.ccM ((List.range' 0 50).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 50+ov 0 16+7) ?_ Q A
  have hkS := setTab_known c hk
  have h0S := setTab_orig c h0
  have heS := setTab_encoded he
  rw [show (50:Nat)=48+2 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind,
    show (0+48:Nat)=48 from rfl]
  have ec : c.chainsCost 0 (48+2) = c.chainsCost 0 48 + c.chainsCost 48 2 := c.chainsCost_add' 0 48 2
  have H := c.groups_zero hc hds hk h0 he hf hmask 16 (le_refl _) (by decide +kernel) (fun q hq => hval q (by omega))
    (fun ends => Verify.ccM ((List.range' 48 2).foldlM c.chainF ends) K)
    (88) (c.chainsCost 48 2+7) (0+c.chainsCost 48 2+7) False
    (fun acc t ht => by
      have hb15 : c.bq s0 (16-1) = set24 (setTab s0) (c.s8v 15) := by unfold bq; rw [if_neg (by omega)]
      rw [hb15] at ht
      have he15 := set24_encoded6 (c.s8v 15) heS
      obtain ⟨u,st1,hu⟩ := c.end_dispatchR6_in hc hds he15 hf 15 (by omega) (by omega) (hval 16 (by omega)) acc t
        (by simpa using ht)
      obtain ⟨w,st2,hw⟩ := c.entry_step hc hds 15 (by omega) (set24_24 _ _) acc u hu
      rw [set24_set24] at hw
      have hd16 : dspR6 (15+1) = 3 := rfl
      rw [hd16] at st1
      set B := set24 (setTab s0) (c.s8v 16) with hB
      have hkB : ∀p∈c.known,B.getReg p.1=p.2 := set24_known c (c.s8v 16) hkS
      have h0B : c.Orig0 B := set24_orig c (c.s8v 16) h0S
      have hn16 : nCh 16 = 2 := rfl
      have H := c.group_good hc hds hkB h0B 16 (by omega) K 4 3 0 False
        (fun ends u2 hu2 => by
          rw [hn16] at hu2
          rw [hK ends]
          have h24 : u2.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 50).map c.dig).sum) := by
            rw [hu2.1.1 .x24 (by decide +kernel), hB, set24_24]; rfl
          obtain ⟨z,stz,fz⟩ := (c.end_ck hds ends u2 (by simpa using hu2) _ rfl h24).2 hout
          have R := goodQ_fault (P := P) (Q := False) (A := 0) fz
          refine (Verify.GoodQP.steps stz R).mono ?_ ?_ ?_
          · omega
          · omega
          · intro h; exact h.elim)
        2 48 (le_refl _) (by omega) (by omega) acc w (by simpa using hw)
      have H' := Verify.GoodQP.steps (st1.trans st2) H
      simp only [Nat.zero_add]
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
    s hs
  rw [show (3*16 : Nat)=48 from rfl] at H
  rw [ec]
  refine H.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
end
-- ==== merged from T3M_Verify_Nonbinary_LayerPrefix ====
section

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
/-- The `addi s0,a0,K` row-offset word of a top copy whose row address is `a` (`s0 = a0 - (a - 14128) = 14128`). -/
def rowWordOf (a : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((4096 - (a - 14128)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13)
/-! ### d6b top head, campaign T51 (verify image T51_T152_g791_c0hi): 18 words at `h+6..h+23` of every top copy
```
h+6   ld t1,536(s0); addi s0,a0,K          (dPro)
h+8   lb gp,528(tp); bge gp,zero,h+12      (dHint: hint byte at abs 25232, bit 7 clear = LOW)
h+10  lbu gp,15(a2); bgeu gp,a1,h+18       (dHead: LOW forced iff its top byte < 64, i.e. LOW < 2^126)
h+12  LOW:  ld a7,8(a2);  ld a6,0(a2);  slli a4,a6,56; srli a4,a4,45; jalr zero,-744(a4); nop
h+18  HIGH: ld a7,24(a2); ld a6,16(a2); slli a4,a6,56; srli a4,a4,45; jalr zero,-744(a4); nop
```
Selector costs (before the 5-instruction dispatch block): hint clear 4, hint set 6 (HIGH, or LOW forced). The
dispatch jumps to `g0Target V` = the g0 cell `512 (raw0 - 3) + 326` of the first r6 field `raw0 = V % 256` (for
`raw0 >= 3`; `raw0 < 3` lands below the code start). The `nop`s are never executed. -/
def dProWordsOf (a : Nat) : List (BitVec 32) := [0x21813303, rowWordOf a]
def dHint : List (BitVec 32) := [0x21020183,0x1d663]
def dHead : List (BitVec 32) := [0xf64183,0xb1fe63]
def dLow : List (BitVec 32) := [0x863883,0x63803,0x3881713,0x2d75713,0xd1870067,0x13]
def dHigh : List (BitVec 32) := [0x1863883,0x1063803,0x3881713,0x2d75713,0xd1870067,0x13]
/-- The bit of the witness choice byte (abs 25232) that requests HIGH. -/
def selHintBit : Nat := 7
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  dProWordsOf a ++ dHint ++ dHead ++ dLow ++ dHigh
def aVals : List Nat := [15336,15352,15384,15400,15432,15448,15480,15496,15528]
sym_block dProBase := symRun { noAlias := true } (dProWordsOf 15432) (BitVec.ofNat 64 (0x1000 + 4 * 1070)) 200
def dProRegs (a : Nat) : RegFile :=
  dProBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 14128)))))
def dProRes (a : Nat) (p : Word) : Result :=
  { dProBase.res with st := { dProBase.res.st with regs := dProRegs a }, pc := .c (p+4+4) }
sym_block dHintBase := symRun { noAlias := true } dHint (BitVec.ofNat 64 (0x1000 + 4*1072)) 200
sym_block dHeadBase := symRun { noAlias := true } dHead (BitVec.ofNat 64 (0x1000 + 4*1074)) 200
sym_block dLowBase := symRun { noAlias := true } dLow (BitVec.ofNat 64 (0x1000 + 4*1076)) 200
sym_block dHighBase := symRun { noAlias := true } dHigh (BitVec.ofNat 64 (0x1000 + 4*1082)) 200
def hintByte : E := .un (.ld .b 0) (.ld (.bin .add (.reg .x4) (.c 528)))
def headByte : E := .un (.ld .bu 7) (.ld (.bin .add (.reg .x12) (.c 8)))
def dHintRes (p : Word) : Result :=
  {dHintBase.res with pc := (E.ite .ge hintByte (.c 0) (.c (p+4+12)) (.c (p+4+4)))}
def dHeadRes (p : Word) : Result :=
  {dHeadBase.res with pc := (E.ite .geu headByte (.reg .x11) (.c (p+4+28)) (.c (p+4+4)))}
theorem dHint_run (p : Word) :
    symRun {noAlias := true} dHint p 200 = some (dHintRes p) := by rfl
theorem dHead_run (p : Word) :
    symRun {noAlias := true} dHead p 200 = some (dHeadRes p) := by rfl
theorem dLow_run (p : Word) :
    symRun {noAlias := true} dLow p 200 = some dLowBase.res := by rfl
theorem dHigh_run (p : Word) :
    symRun {noAlias := true} dHigh p 200 = some dHighBase.res := by rfl
theorem dPro_run (a : Nat) (ha : a ∈ aVals) (p : Word) :
    symRun { noAlias := true } (dProWordsOf a) p 200 = some (dProRes a p) := by
  simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
/-- Campaign T51: the landing of the head's dispatch (`slli a4,a6,56; srli a4,a4,45; jalr -744(a4)`) for the selected
half `V` (R6's form; `ChainsDispatchArith.g0_target` / `g0_cell` evaluate it to the g0 cell `512 (raw0 - 3) + 326`). -/
def g0Target (V : BitVec 128) : Word :=
  ((((V.extractLsb' 0 64) <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64
end SigGolfCandidate.T3M.Verify.Nonbinary
end
-- ==== merged from T3M_Verify_Nonbinary_TopAlias ====
section

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The relocated legacy table entry always takes the rejection exit. -/
def aliasRejectSpec (n : Nat) : Spec :=
  ⟨[(.x5,.c 1),(.x10,.c 1)],[],3431,true,n,[],none,n⟩

theorem alias_reject_check :
    specB [] [] [] (runAt [] [] 245834 []) (aliasRejectSpec 8) [] [] [] = true := by decide +kernel

theorem alias_reject (s : MachineState) (hp : s.pc = pcOf 245834) :
    ∃ t, Steps image s 8 8 t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  obtain ⟨t,ht⟩ := spec_run alias_reject_check s hp (by simp [KnownOK]) (by simp [aliasRejectSpec]) (by simp)
  exact ⟨t,ht.steps,ht.ecall rfl,ht.regs (.x5,.c 1) (by simp [aliasRejectSpec]),
    ht.regs (.x10,.c 1) (by simp [aliasRejectSpec])⟩

end SigGolfCandidate.T3M.Verify.Nonbinary
end
-- ==== merged from T3M_Verify_LayerRuns ====
section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def xtrTab : List (List Nat) :=[[1064,2088,3112,4136,5160,6184,7208,8232,9256,10280,11304,12328,13352,14376,15400,16424,17448,18472,19496,20520,21544,22568,23592,24616,25640,26664,27688,28712,29736,30760,31784,32808,33832,34856,35880,36904,37928,38952,39976,41000,42024,43048,44072,45096,46120,47144,48168,49192,50216,51240,52264,53288,54312,55336,56360,57384,58408,59432,60456,61480,62504,63528,64552,65576,66600,67624,68648,69672,70696,71720,72744,73768,74792,75816,76840,77864,78888,79912,80936,81960,82984,84008,85032,86056,87080,88104,89128,90152,91176,92200,93224,94248,95272,96296,97320,98344,99368,100392,101416,102440,103464,104488,105512,106536,107560,108584,109608,110632,111656,112680,113704,114728,115752,116776,117800,118824,119848,120872,121896,122920,123944,124968,125992,127016,128040,129064,130088,131112],[141987,142115,142243,142371,142499,142627,142755,142883,143011,143139,143267,143395,143523,143651,143779,143907,144035,144163,144291,144419,144547,144675,144803,144931,145059,145187,145315,145443,145571,145699,145827,145955,146083,146211,146339,146467,146595,146723,146851,146979,147107,147235,147363,147491,147619,147747,147875,148003,148131,148259,148387,148515,148643,148771,148899,149027,149155,149283,149411,149539,149667,149795,149923,150051],[133795,133923,134051,134179,134307,134435,134563,134691,134819,134947,135075,135203,135331,135459,135587,135715,135843,135971,136099,136227,136355,136483,136611,136739,136867,136995,137123,137251,137379,137507,137635,137763,137891,138019,138147,138275,138403,138531,138659,138787,138915,139043,139171,139299,139427,139555,139683,139811,139939,140067,140195,140323,140451,140579,140707,140835,140963,141091,141219,141347,141475,141603,141731,141859],[854]]
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def hL (lay : Nat) : Nat := [12,7,6,6].getD lay 0
/-- Layer head steps before the encoding ecall (stage 2): L3 5 (C3: no row high-word store; the merged singleton
leaves the right top value at `WIT + 48`, so no copy), top 5, L1/L2 7 (C2/C3, as #866). -/
def stepsA (lay : Nat) : Nat := if lay = 3 then 6 else if lay = 0 then 5 else 7
def retOff (lay : Nat) : Nat := if lay = 0 then 10 else if lay = 3 then 38 else 41
def s6v (lay : Nat) : Nat := [14128,16192,18760,21328].getD lay 0
def s3v : Nat := 14128
def tgtL (lay : Nat) : Nat := [152,201,201,201].getD lay 0
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
def rejEcall : Nat := 3431
def stabIdx (lay : Nat) : Nat := [209768,209640,209576,209512].getD lay 0
def stabMask (lay : Nat) : Nat := if lay = 1 then 508 else 252
def s7Bias (lay : Nat) : Nat := [4096,2,1117,1053].getD lay 0
def stabW (lay sh : Nat) : Nat :=
  if lay = 0 then 142032 + 128 * sh else if lay = 1 then 1028 + 1024 * sh else if lay = 2 then 141956 + 128 * sh else 133764 + 128 * sh
def M1c : Nat := 8198552921648689607
def M2c : Nat := 17311559823019733055
def M4c : Nat := 3689348814741910323
def M8c : Nat := 1085102592571150095
def mkBase (lay : Nat) : Nat := [7664,11144,13792,16360].getD lay 0
def planL1 : List (List Nat) :=[[1,4,7,10,13,21,16],[0,4,7,10,13,21,16],[1,8,12,15,18,21,4],[0,8,12,15,18,21,4],[1,4,11,15,18,21,7],[0,4,11,15,18,21,7],[1,11,8,15,18,21,4],[0,11,8,15,18,21,4],[1,4,7,14,18,21,10],[0,4,7,14,18,21,10],[1,11,15,8,18,21,4],[0,11,15,8,18,21,4],[1,4,14,11,18,21,7],[0,4,14,11,18,21,7],[1,14,11,8,18,21,4],[0,14,11,8,18,21,4],[1,4,7,10,17,21,13],[0,4,7,10,17,21,13],[1,11,15,18,8,21,4],[0,11,15,18,8,21,4],[1,4,14,18,11,21,7],[0,4,14,18,11,21,7],[1,14,11,18,8,21,4],[0,14,11,18,8,21,4],[1,4,7,17,14,21,10],[0,4,7,17,14,21,10],[1,14,18,11,8,21,4],[0,14,18,11,8,21,4],[1,4,17,14,11,21,7],[0,4,17,14,11,21,7],[1,17,14,11,8,21,4],[0,17,14,11,8,21,4],[1,4,7,10,13,20,16],[0,4,7,10,13,20,16],[1,11,15,18,21,8,4],[0,11,15,18,21,8,4],[1,4,14,18,21,11,7],[0,4,14,18,21,11,7],[1,14,11,18,21,8,4],[0,14,11,18,21,8,4],[1,4,7,17,21,14,10],[0,4,7,17,21,14,10],[1,14,18,11,21,8,4],[0,14,18,11,21,8,4],[1,4,17,14,21,11,7],[0,4,17,14,21,11,7],[1,17,14,11,21,8,4],[0,17,14,11,21,8,4],[1,4,7,10,20,17,13],[0,4,7,10,20,17,13],[1,14,18,21,11,8,4],[0,14,18,21,11,8,4],[1,4,17,21,14,11,7],[0,4,17,21,14,11,7],[1,17,14,21,11,8,4],[0,17,14,21,11,8,4],[1,4,7,20,17,14,10],[0,4,7,20,17,14,10],[1,17,21,14,11,8,4],[0,17,21,14,11,8,4],[1,4,20,17,14,11,7],[0,4,20,17,14,11,7],[1,20,17,14,11,8,4],[0,20,17,14,11,8,4],[1,4,7,10,18,21,14],[0,4,7,10,18,21,14],[1,8,12,15,18,21,5],[0,8,12,15,18,21,5],[1,4,11,15,18,21,8],[0,4,11,15,18,21,8],[1,11,8,15,18,21,5],[0,11,8,15,18,21,5],[1,4,7,14,18,21,11],[0,4,7,14,18,21,11],[1,11,15,8,18,21,5],[0,11,15,8,18,21,5],[1,4,14,11,18,21,8],[0,4,14,11,18,21,8],[1,14,11,8,18,21,5],[0,14,11,8,18,21,5],[1,4,7,10,17,21,14],[0,4,7,10,17,21,14],[1,11,15,18,8,21,5],[0,11,15,18,8,21,5],[1,4,14,18,11,21,8],[0,4,14,18,11,21,8],[1,14,11,18,8,21,5],[0,14,11,18,8,21,5],[1,4,7,17,14,21,11],[0,4,7,17,14,21,11],[1,14,18,11,8,21,5],[0,14,18,11,8,21,5],[1,4,17,14,11,21,8],[0,4,17,14,11,21,8],[1,17,14,11,8,21,5],[0,17,14,11,8,21,5],[1,4,7,10,21,17,14],[0,4,7,10,21,17,14],[1,11,15,18,21,8,5],[0,11,15,18,21,8,5],[1,4,14,18,21,11,8],[0,4,14,18,21,11,8],[1,14,11,18,21,8,5],[0,14,11,18,21,8,5],[1,4,7,17,21,14,11],[0,4,7,17,21,14,11],[1,14,18,11,21,8,5],[0,14,18,11,21,8,5],[1,4,17,14,21,11,8],[0,4,17,14,21,11,8],[1,17,14,11,21,8,5],[0,17,14,11,21,8,5],[1,4,7,10,20,17,14],[0,4,7,10,20,17,14],[1,14,18,21,11,8,5],[0,14,18,21,11,8,5],[1,4,17,21,14,11,8],[0,4,17,21,14,11,8],[1,17,14,21,11,8,5],[0,17,14,21,11,8,5],[1,4,7,20,17,14,11],[0,4,7,20,17,14,11],[1,17,21,14,11,8,5],[0,17,21,14,11,8,5],[1,4,20,17,14,11,8],[0,4,20,17,14,11,8],[1,20,17,14,11,8,5],[0,20,17,14,11,8,5]]
def planL32 : List (List Nat) :=[[1,4,7,10,13,16],[0,4,7,10,13,16],[4,0,7,10,13,16],[3,0,7,10,13,16],[4,7,0,10,13,16],[3,7,0,10,13,16],[7,3,0,10,13,16],[6,3,0,10,13,16],[4,7,10,0,13,16],[3,7,10,0,13,16],[7,3,10,0,13,16],[6,3,10,0,13,16],[7,10,3,0,13,16],[6,10,3,0,13,16],[10,6,3,0,13,16],[9,6,3,0,13,16],[4,7,10,13,0,16],[3,7,10,13,0,16],[7,3,10,13,0,16],[6,3,10,13,0,16],[7,10,3,13,0,16],[6,10,3,13,0,16],[10,6,3,13,0,16],[9,6,3,13,0,16],[7,10,13,3,0,16],[6,10,13,3,0,16],[10,6,13,3,0,16],[9,6,13,3,0,16],[10,13,6,3,0,16],[9,13,6,3,0,16],[13,9,6,3,0,16],[12,9,6,3,0,16],[4,7,10,13,16,0],[3,7,10,13,16,0],[7,3,10,13,16,0],[6,3,10,13,16,0],[7,10,3,13,16,0],[6,10,3,13,16,0],[10,6,3,13,16,0],[9,6,3,13,16,0],[7,10,13,3,16,0],[6,10,13,3,16,0],[10,6,13,3,16,0],[9,6,13,3,16,0],[10,13,6,3,16,0],[9,13,6,3,16,0],[13,9,6,3,16,0],[12,9,6,3,16,0],[7,10,13,16,3,0],[6,10,13,16,3,0],[10,6,13,16,3,0],[9,6,13,16,3,0],[10,13,6,16,3,0],[9,13,6,16,3,0],[13,9,6,16,3,0],[12,9,6,16,3,0],[10,13,16,6,3,0],[9,13,16,6,3,0],[13,9,16,6,3,0],[12,9,16,6,3,0],[13,16,9,6,3,0],[12,16,9,6,3,0],[16,12,9,6,3,0],[15,12,9,6,3,0]]
/-- C4 top window plan (machine copy of `ClaudeWCT.W9.T3M.topPlanA/B`, `topRootSlot`): line A (windows 0..5) by
`leaf % 64`, line B (windows 6..11) by `leaf / 64 % 64`; `topRootSlot` is the slot of the root answer of upper copy `k`. -/
def topPlanA : List (List Nat) :=[[26,29,32,35,38,21],[25,29,32,35,38,21],[29,25,32,35,38,21],[28,25,32,35,38,21],[29,32,25,35,38,21],[28,32,25,35,38,21],[32,28,25,35,38,21],[31,28,25,35,38,21],[29,32,35,25,38,21],[28,32,35,25,38,21],[32,28,35,25,38,21],[31,28,35,25,38,21],[32,35,28,25,38,21],[31,35,28,25,38,21],[35,31,28,25,38,21],[34,31,28,25,38,21],[29,32,35,38,25,21],[28,32,35,38,25,21],[32,28,35,38,25,21],[31,28,35,38,25,21],[32,35,28,38,25,21],[31,35,28,38,25,21],[35,31,28,38,25,21],[34,31,28,38,25,21],[32,35,38,28,25,21],[31,35,38,28,25,21],[35,31,38,28,25,21],[34,31,38,28,25,21],[35,38,31,28,25,21],[34,38,31,28,25,21],[38,34,31,28,25,21],[37,34,31,28,25,21],[25,28,31,34,37,21],[24,28,31,34,37,21],[28,24,31,34,37,21],[27,24,31,34,37,21],[28,31,24,34,37,21],[27,31,24,34,37,21],[31,27,24,34,37,21],[30,27,24,34,37,21],[28,31,34,24,37,21],[27,31,34,24,37,21],[31,27,34,24,37,21],[30,27,34,24,37,21],[31,34,27,24,37,21],[30,34,27,24,37,21],[34,30,27,24,37,21],[33,30,27,24,37,21],[28,31,34,37,24,21],[27,31,34,37,24,21],[31,27,34,37,24,21],[30,27,34,37,24,21],[31,34,27,37,24,21],[30,34,27,37,24,21],[34,30,27,37,24,21],[33,30,27,37,24,21],[31,34,37,27,24,21],[30,34,37,27,24,21],[34,30,37,27,24,21],[33,30,37,27,24,21],[34,37,30,27,24,21],[33,37,30,27,24,21],[37,33,30,27,24,21],[36,33,30,27,24,21]]
def topPlanB : List (List Nat) :=[[0,3,6,9,12,15],[0,4,7,10,13,16],[4,0,7,10,13,16],[3,0,7,10,13,16],[4,7,0,10,13,16],[3,7,0,10,13,16],[7,3,0,10,13,16],[6,3,0,10,13,16],[4,7,10,0,13,16],[3,7,10,0,13,16],[7,3,10,0,13,16],[6,3,10,0,13,16],[7,10,3,0,13,16],[6,10,3,0,13,16],[10,6,3,0,13,16],[9,6,3,0,13,16],[4,7,10,13,0,16],[3,7,10,13,0,16],[7,3,10,13,0,16],[6,3,10,13,0,16],[7,10,3,13,0,16],[6,10,3,13,0,16],[10,6,3,13,0,16],[9,6,3,13,0,16],[7,10,13,3,0,16],[6,10,13,3,0,16],[10,6,13,3,0,16],[9,6,13,3,0,16],[10,13,6,3,0,16],[9,13,6,3,0,16],[13,9,6,3,0,16],[12,9,6,3,0,16],[4,7,10,13,16,0],[3,7,10,13,16,0],[7,3,10,13,16,0],[6,3,10,13,16,0],[7,10,3,13,16,0],[6,10,3,13,16,0],[10,6,3,13,16,0],[9,6,3,13,16,0],[7,10,13,3,16,0],[6,10,13,3,16,0],[10,6,13,3,16,0],[9,6,13,3,16,0],[10,13,6,3,16,0],[9,13,6,3,16,0],[13,9,6,3,16,0],[12,9,6,3,16,0],[7,10,13,16,3,0],[6,10,13,16,3,0],[10,6,13,16,3,0],[9,6,13,16,3,0],[10,13,6,16,3,0],[9,13,6,16,3,0],[13,9,6,16,3,0],[12,9,6,16,3,0],[10,13,16,6,3,0],[9,13,16,6,3,0],[13,9,16,6,3,0],[12,9,16,6,3,0],[13,16,9,6,3,0],[12,16,9,6,3,0],[16,12,9,6,3,0],[15,12,9,6,3,0]]
def topRootSlot : List Nat :=[14,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3]
/-- Slot of the top window of level `j` for `leaf` (two lines). -/
def topPlan (leaf j : Nat) : Nat :=
  if j < 6 then (topPlanA.getD (leaf % 64) []).getD j 0 else (topPlanB.getD (leaf / 64 % 64) []).getD (j - 6) 0
def plan (lay r j : Nat) : Nat :=
  if lay = 0 then topPlan r j else ((if lay = 1 then planL1 else planL32).getD r []).getD j 0
def rowA (lay c : Nat) : Nat := 0x1020 + mkBase (lay + 1) + 16 * plan (lay + 1) c (hL (lay + 1) - 1)
def bufferBias (lay : Nat) : Nat := [24704,23728,23008,22288].getD lay 0
def bufferBase (lay : Nat) : Nat := [25216,24496,23776,23056].getD lay 0
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then [(.x5, 0)] ++ [(.x8, BitVec.ofNat 64 4208), (.x11, 64), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7),
    (.x2, BitVec.ofNat 64 0xffbde0), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)]
  else baseK ++ [(.x6, 0x10000), (.x9, 0x7fc00),
    (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x5, 0), (.x2, BitVec.ofNat 64 0xffbde0), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias (lay+1)))]
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x2, BitVec.ofNat 64 0xffbde0)] ++
    (if lay = 3 then [] else [(.x9, 0x7fc00), (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x5, 0), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias lay))])
def chainK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x9, 0x7fc00),
    (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x5, 0), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias lay))]
def bK (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, 4128)] ++
  (if lay = 1 ∨ lay = 2 then [(.x22, BitVec.ofNat 64 (s6v lay))] else [])
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x31
def leafE (lay : Nat) : E := if lay = 0 then .reg .x31 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := if lay = 0 then .bin .sll (leafE lay) (kw 32) else .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def dispatchHeap (lay leaf : Nat) : Nat := if lay = 0 then 16 * (s7Bias lay + leaf) else s7Bias lay + leaf
def s7E (lay : Nat) : E := if lay = 0 then .bin .or (.bin .sll (leafE lay) (kw 4)) (kw (16 * 2 ^ hL lay)) else .bin .add (leafE lay) (kw (s7Bias lay))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x1030 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay, kw 0x400000, d⟩
def setupPc (_lay p : Nat) : Nat := p
def setupAcceptDir (lay : Nat) : Bool := decide (lay = 3)
def hdrA (lay : Nat) : Nat := if lay = 3 then TOPLOAD + 32 else HDATA + 8 * lay
def t3E3 : E := .bin .or (.ld (kw (hdrA 3))) (.bin .sll (.reg .x22) (kw 16))
/-- The FTS leaves both roots directly in the layer-3 encoding row (left at `WIT`, right at `WIT + 48`). Entry
writes the row tweak's low word at `WIT + 16` (C3: its high word `WIT + 24` is a witness pad) and retains the final
hash destination in `a2`; for the lower layers only the tweak word. -/
def l3Writes (_lay : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 4144⟩, t3E3)]
/-- C4 (D7): the L3 block reloads `s2` from the stack word the prologue used to read (`TOPB9 - 304`, value 0xFFF). -/
def x18E3 : E := .ld (kw (TOPB9 - 304))
def specA (lay p : Nat) : Spec :=
  ⟨if lay = 3 then [(.x28, t3E3), (.x12, .reg .x12), (.x18, x18E3)] else [(.x23, s7E lay), (.x31, treeE lay), (.x28, t3E3)],
   l3Writes lay,
   p + stepsA lay, true, stepsA lay, [], none, stepsA lay⟩
def rejA (lay _p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   l3Writes lay,
   28822, true, 33, [ctrBr lay (!setupAcceptDir lay)], none, 33⟩
def a6E : E := .ld (.reg .x12)
def a7E : E := .ld (.bin .add (.reg .x12) (kw 8))
def b1E : E := .bin .sll a7E (kw 1)
def M1E (lay : Nat) : E := if lay = 3 then .ld (kw (TOPLOAD + 8)) else kw M1c
def M2E (lay : Nat) : E := if lay = 3 then .ld (kw TOPLOAD) else kw M2c
def maskE (lay : Nat) : E := if lay = 3 then .ld (kw (TOPLOAD + 24)) else kw 0x7fc00
def sw1RefE : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl a7E (kw 3)) (kw M1c))) (.bin .and a7E (kw M1c))
def swLowE (lay : Nat) : E := .bin .add (.bin .and a6E (M1E lay)) (.bin .and a7E (M1E lay))
def sw1E (lay : Nat) : E := .bin .add (swLowE lay) (.bin .srl (.bin .sub (.bin .add a6E a7E) (swLowE lay)) (kw 3))
def sumE (lay : Nat) : E := .bin .remu (.bin .and (.bin .add (sw1E lay) (.bin .srl (sw1E lay) (kw 6))) (M2E lay)) (kw 4095)
def t4E (lay : Nat) : E := .bin .add (sumE lay) (kw (2 ^ 64 - (tgtL lay - 7)))
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.ltu, kw 7, t4E lay, d⟩
def spareBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .lt else .ge, .bin .and a6E a7E, kw 0, if lay = 3 then !d else d⟩
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
def x14l (lay : Nat) : E := .bin .and (.bin .sll a6E (kw 10)) (maskE lay)
def tgtl (lay : Nat) : E := .bin .and (.bin .add (x14l lay) (kw 1992)) (.c (~~~1#64))
def a6HiE : E := .ld (.bin .add (.reg .x12) (kw 16))
def a7HiE : E := .ld (.bin .add (.reg .x12) (kw 24))
def b1HiE : E := .bin .sll a7HiE (kw 1)
def swLowHiE (lay : Nat) : E := .bin .add (.bin .and a6HiE (M1E lay)) (.bin .and a7HiE (M1E lay))
def sw1HiE (lay : Nat) : E := .bin .add (swLowHiE lay) (.bin .srl (.bin .sub (.bin .add a6HiE a7HiE) (swLowHiE lay)) (kw 3))
def sumHiE (lay : Nat) : E := .bin .remu (.bin .and (.bin .add (sw1HiE lay) (.bin .srl (sw1HiE lay) (kw 6))) (M2E lay)) (kw 4095)
def t4HiE (lay : Nat) : E := .bin .add (sumHiE lay) (kw (2 ^ 64 - (tgtL lay - 7)))
def rngHiBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7HiE (kw k), kw 0, d⟩
def ckHiBr (lay : Nat) (d : Bool) : Br := ⟨.ltu, kw 7, t4HiE lay, d⟩
def spareHiBr (_lay : Nat) (d : Bool) : Br := ⟨.lt, .bin .and a6HiE a7HiE, kw 0, !d⟩
def a7HiL : E := .bin .or b1HiE (.bin .srl a6HiE (kw 63))
def x14Hi (lay : Nat) : E := .bin .and (.bin .sll a6HiE (kw 10)) (maskE lay)
def tgtHi (lay : Nat) : E := .bin .and (.bin .add (x14Hi lay) (kw 1992)) (.c (~~~1#64))
def bSt (lay : Nat) : Nat := if lay = 3 then 30 else if lay = 1 ∨ lay = 2 then 21 else 33
def bCy (lay : Nat) : Nat := if lay = 3 then 33 else if lay = 1 ∨ lay = 2 then 24 else 36
def prefixReturn (lay p : Nat) : Nat := p + (if lay = 3 then 37 else 38)
def s7Sh (lay : Nat) : Nat := if lay = 1 then 12 else 9
def s23E (lay : Nat) : E := if lay = 3 then .bin .sll (s7E 3) (kw 9) else .bin .sll (.reg .x23) (kw (s7Sh lay))
def specBl (lay _p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7E), (.x23, s23E lay), (.x25, sumE lay), (.x29, t4E lay),
    (.x14, x14l lay)] ++ (if lay = 3 then [(.x22, .ld (kw (TOPLOAD - 8))),
      (.x24, .ld (kw TOPLOAD)), (.x1, .ld (kw (TOPLOAD + 8))), (.x9, .ld (kw (TOPLOAD + 24))),
      (.x31, treeE 3), (.x27, .bin .srl (maskE 3) (kw 1)), (.x4, .ld (kw (TOPB9+56)))] else []),
   [], 0, false, bSt lay, [ckBr lay false, spareBr lay false], some (tgtl lay), bCy lay⟩
def specBlHi (lay _p : Nat) : Spec :=
  ⟨[(.x16, a6HiE), (.x17, a7HiE), (.x23, s23E lay), (.x25, sumHiE lay), (.x29, t4HiE lay),
    (.x14, x14Hi lay)] ++ (if lay = 3 then [(.x22, .ld (kw (TOPLOAD - 8))),
      (.x24, .ld (kw TOPLOAD)), (.x1, .ld (kw (TOPLOAD + 8))), (.x9, .ld (kw (TOPLOAD + 24))),
      (.x31, treeE 3), (.x27, .bin .srl (maskE 3) (kw 1)), (.x4, .ld (kw (TOPB9+56)))] else []),
   [], 0, false, bSt lay + 4, [ckHiBr lay false, spareHiBr lay false, spareBr lay true], some (tgtHi lay), bCy lay + 4⟩
def postBl (lay _p : Nat) : List (Reg × Word) :=
  chainK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x7, 1), (.x2, BitVec.ofNat 64 0xffbde0)]
def postBlC (lay p : Nat) : List (Reg × Word) :=
  if lay = 3 then ((chainK lay).filter (fun q => q.1 != .x24 && q.1 != .x1 && q.1 != .x9 && q.1 != .x27 && q.1 != .x4)) ++ [(.x7, 1), (.x2, BitVec.ofNat 64 0xffbde0)] else postBl lay p
def rejSpare (lay : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [spareBr lay true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, if lay = 3 then 23 else 20, [ckBr lay true, spareBr lay false], none, if lay = 3 then 26 else 23⟩
def rejCkHi (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, (if lay = 3 then 23 else 20)+4,
    [ckHiBr lay true, spareHiBr lay false, spareBr lay true], none, (if lay = 3 then 26 else 23)+4⟩
def spareTrap (lay c : Nat) : Nat := ([[],[142021,142149,142277,142405,142533,142661,142789,142917,143045,143173,143301,143429,143557,143685,143813,143941,144069,144197,144330,144453,144581,144709,144837,144965,145093,145221,145349,145477,145605,145733,145861,145989,146117,146245,146373,146501,146629,146757,146885,147013,147144,147269,147397,147525,147653,147781,147909,148037,148165,148293,148421,148549,148677,148805,148933,149061,149189,149317,149445,149573,149701,149829,149958,150085],[133829,133957,134085,134213,134341,134469,134597,134725,134853,134981,135109,135237,135365,135493,135621,135749,135877,136005,136133,136261,136389,136522,136645,136773,136901,137029,137157,137285,137413,137541,137669,137797,137925,138053,138181,138309,138437,138568,138693,138821,138949,139077,139205,139333,139461,139589,139717,139845,139973,140101,140229,140357,140485,140613,140741,140869,140997,141125,141253,141382,141509,141637,141765,141893],[869]].getD lay []).getD c 0
def rejBothSpare (lay c : Nat) : Spec :=
  ⟨[], [], spareTrap lay c, false, 8, [spareHiBr lay true, spareBr lay true], none, 8⟩
def lfAllowed (lay : Nat) : List Nat := [bufferBase lay+16,bufferBase lay+24]
/-- Campaign T51: the global register facts kept through layer `lay`'s leaf and merkle code. The T51 g0 body loads
`s2 = 856064` (the r6 table base), and nothing after it restores main's `s2 = 0xFFF` (the top leaf, merkle and root
compare never read `s2`), so the top keeps only `t0 = 0`; lower layers keep `baseK`. -/
def gkL (lay : Nat) : List (Reg × Word) := if lay = 0 then [(.x5, 0)] else baseK
theorem gkL_low {lay : Nat} (h : lay ≠ 0) : gkL lay = baseK := if_neg h
def leafK (lay : Nat) : List (Reg × Word) :=
  gkL lay ++ (if lay = 0 then [(.x5, 0), (.x6, 520192)] else [(.x7, 1), (.x5, 0)]) ++ [(.x4,BitVec.ofNat 64 (bufferBias lay))]
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .sll (.bin .add (.bin .and (.reg .x31) (kw 63)) (kw 1117)) (kw 9)
  else if lay = 1 then .bin .sll (.reg .x23) (kw 12)
  else .bin .sll (.reg .x23) (kw 9)
def tgtLf (lay : Nat) : E := if lay = 0 then .bin .and (addC (x14lf lay) 320) (.c (~~~1#64)) else .bin .and (addC (.reg .x23) 16) (.c (~~~1#64))
def lfDirs (_lay : Nat) : List Dir := [.jmp]
def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)], [(⟨none, BitVec.ofNat 64 (bufferBase lay+16)⟩, .reg .x28)], 0, false, 7, [], some (tgtLf lay), 7⟩
  else
    ⟨[], [(⟨none, BitVec.ofNat 64 (bufferBase lay+16)⟩, .reg .x28)], 0, false, 4, [],
      some (tgtLf lay), 4⟩
def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ [(.x10, BitVec.ofNat 64 (bufferBase lay)), (.x11, BitVec.ofNat 64 (if lay = 0 then 832 else 704))]
def keepA : List Reg := []
def keepB (lay : Nat) : List Reg := if lay = 3 then [.x28] else [.x28, .x31]
def keepLf : List Reg := [.x23, .x31, .x22]
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_BCWords ====
section

set_option Elab.async false

section


section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.preK lay else
  (T3M.preK lay).filter (fun p => p.1 != .x10 && p.1 != .x12) ++
    [(.x22, BitVec.ofNat 64 (s6v (lay + 1)))]
def bK (lay c : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.bK lay else
  (T3M.bK lay).filter (fun p => p.1 != .x10) ++
    [(.x10, BitVec.ofNat 64 (rowA lay c))]
def ctrE (lay c : Nat) : E :=
  if lay = 3 then T3M.ctrE lay else .un (.ld .wu 0) (.ld (kw (rowA lay c + 32)))
def ctrBr (lay c : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay c, kw 0x400000, d⟩
def headerWrites (lay c : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (rowA lay c + 16)⟩, .reg .x28)]
def specA (lay c : Nat) : Spec :=
  if lay = 3 then T3M.specA lay (trPc lay c) else
  ⟨if lay = 0 then [(.x23, s7E lay), (.x12, .reg .x12)]
   else [(.x23, s7E lay), (.x31, treeE lay), (.x12, .reg .x12)],
   headerWrites lay c, trPc lay c + stepsA lay, true, stepsA lay,
   [], none, stepsA lay⟩
def rejA (lay c : Nat) : Spec :=
  if lay = 3 then T3M.rejA lay (trPc lay c) else
  ⟨[(.x5, kw 1), (.x10, kw 1)], headerWrites lay c,
   rejEcall, true, stepsA lay + 3, [ctrBr lay c true], none, stepsA lay + 3⟩
def keepA (lay : Nat) : List Reg := if lay = 3 then [.x22] else if lay = 0 then [.x28, .x31] else [.x28]
def bKB (lay c : Nat) : List (Reg × Word) := (bK lay c).filter (fun p => p.1 != .x12)
def oblB : List Oblig := [.valid ⟨some (.reg .x12), 8⟩ 8, .valid ⟨some (.reg .x12), 0⟩ 8]
def oblBHi : List Oblig := [.valid ⟨some (.reg .x12), 24⟩ 8, .valid ⟨some (.reg .x12), 16⟩ 8] ++ oblB
def allowed (lay c : Nat) : List Nat :=
  if lay = 3 then [4144, 4176, 4184] else [rowA lay c + 16]
/-- C4 (D7, adapted from b3cc11b): the L3 encoding block loads `s2` (`x18`) itself, so its run starts without the
global `x18 = 0xFFF` fact and re-establishes it from the stack word `TOPB9 - 304` (`x18E3`). -/
def setupGk (lay : Nat) : List (Reg × Word) := if lay = 3 then [(.x5, 0)] else baseK
def bKS (lay c : Nat) : List (Reg × Word) := if lay = 3 then (bK lay c).filter (fun p => p.1 != .x18) else bK lay c
def setupCheck (lay c : Nat) : Bool :=
  specB (allowed lay c) [] (setupGk lay) (runAt (preK lay) [] (setupPc lay (trPc lay c)) [])
    (specA lay c) [] (bKS lay c) (keepA lay)
def copyCheck (lay c : Nat) : Bool :=
  setupCheck lay c &&
  (if lay = 0 then true else
    specB [] [] baseK (runAt (bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay = 3)), .br false, .jmp]) (specBl lay (trPc lay c)) oblB (postBlC lay (trPc lay c)) (keepB lay) &&
    specB [] [] [] (runAt (bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay = 3)), .br true]) (rejCk lay) oblB [] [] &&
    specB [] [] baseK (runAt (bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay ≠ 3)), .br true, .br false, .jmp]) (specBlHi lay (trPc lay c)) oblBHi (postBlC lay (trPc lay c)) (keepB lay) &&
    specB [] [] [] (runAt (bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay ≠ 3)), .br true, .br true]) (rejCkHi lay) oblBHi [] [] &&
    specB [] [] [] (runAt (bKB lay c) [spareTrap lay c] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay ≠ 3)), .br false]) (rejBothSpare lay c) oblBHi [] [] &&
    (vlook (spareTrap lay c) == some 0))
def layerCheck (lay lo n : Nat) : Bool :=
  (List.range' lo n).all fun c => copyCheck lay c
end SigGolfCandidate.T3M.BC
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def keepLfL : List Reg := [.x27, .x1, .x2, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23, .x6, .x25,
  .x26, .x29, .x31, .x30, .x28, .x14]
def lfSlotCheck (lay c : Nat) : Bool :=
  specB (lfAllowed lay) [] baseK (runAt (leafK lay) [] (ckSlot c + partLen c) (lfDirs lay)) (specLf lay) [] (postLf lay) keepLfL
set_option maxRecDepth 100000 in
theorem lfSlotChecks : ([1, 2, 3].all fun lay => (List.range 8).all fun c => lfSlotCheck lay c) = true := by
  decide +kernel
theorem lfSlotCheck_at (lay c : Nat) (h0 : lay ≠ 0) (h4 : lay < 4) (hc : c < 8) : lfSlotCheck lay c = true := by
  have h := List.all_eq_true.mp lfSlotChecks lay (by simp; omega)
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M.BC
set_option maxRecDepth 100000
theorem layerCheck_3 : layerCheck 3 0 1 = true := by decide +kernel
/-- Compose short code-window checks without normalizing a full closed batch. -/
theorem layerCheck_add {lay lo left right : Nat}
    (hleft : layerCheck lay lo left = true)
    (hright : layerCheck lay (lo + left) right = true) :
    layerCheck lay lo (left + right) = true := by
  unfold layerCheck at *
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl
private theorem layerCheck_part_2_0 : layerCheck 2 0 8 = true := by decide +kernel
private theorem layerCheck_part_2_8 : layerCheck 2 8 8 = true := by decide +kernel
private theorem layerCheck_part_2_16 : layerCheck 2 16 8 = true := by decide +kernel
private theorem layerCheck_part_2_24 : layerCheck 2 24 8 = true := by decide +kernel
private theorem layerCheck_part_2_32 : layerCheck 2 32 8 = true := by decide +kernel
private theorem layerCheck_part_2_40 : layerCheck 2 40 8 = true := by decide +kernel
private theorem layerCheck_part_2_48 : layerCheck 2 48 8 = true := by decide +kernel
private theorem layerCheck_part_2_56 : layerCheck 2 56 8 = true := by decide +kernel
theorem layerCheck_2 : layerCheck 2 0 64 = true := by
  exact @layerCheck_add 2 0 8 56 layerCheck_part_2_0 (@layerCheck_add 2 8 8 48 layerCheck_part_2_8 (@layerCheck_add 2 16 8 40 layerCheck_part_2_16 (@layerCheck_add 2 24 8 32 layerCheck_part_2_24 (@layerCheck_add 2 32 8 24 layerCheck_part_2_32 (@layerCheck_add 2 40 8 16 layerCheck_part_2_40 (@layerCheck_add 2 48 8 8 layerCheck_part_2_48 (layerCheck_part_2_56)))))))
private theorem layerCheck_part_1_0 : layerCheck 1 0 8 = true := by decide +kernel
private theorem layerCheck_part_1_8 : layerCheck 1 8 8 = true := by decide +kernel
private theorem layerCheck_part_1_16 : layerCheck 1 16 8 = true := by decide +kernel
private theorem layerCheck_part_1_24 : layerCheck 1 24 8 = true := by decide +kernel
private theorem layerCheck_part_1_32 : layerCheck 1 32 8 = true := by decide +kernel
private theorem layerCheck_part_1_40 : layerCheck 1 40 8 = true := by decide +kernel
private theorem layerCheck_part_1_48 : layerCheck 1 48 8 = true := by decide +kernel
private theorem layerCheck_part_1_56 : layerCheck 1 56 8 = true := by decide +kernel
theorem layerCheck_1 : layerCheck 1 0 64 = true := by
  exact @layerCheck_add 1 0 8 56 layerCheck_part_1_0 (@layerCheck_add 1 8 8 48 layerCheck_part_1_8 (@layerCheck_add 1 16 8 40 layerCheck_part_1_16 (@layerCheck_add 1 24 8 32 layerCheck_part_1_24 (@layerCheck_add 1 32 8 24 layerCheck_part_1_32 (@layerCheck_add 1 40 8 16 layerCheck_part_1_40 (@layerCheck_add 1 48 8 8 layerCheck_part_1_48 (layerCheck_part_1_56)))))))
private theorem layerCheck_part_0_0 : layerCheck 0 0 8 = true := by decide +kernel
private theorem layerCheck_part_0_8 : layerCheck 0 8 8 = true := by decide +kernel
private theorem layerCheck_part_0_16 : layerCheck 0 16 8 = true := by decide +kernel
private theorem layerCheck_part_0_24 : layerCheck 0 24 8 = true := by decide +kernel
private theorem layerCheck_part_0_32 : layerCheck 0 32 8 = true := by decide +kernel
private theorem layerCheck_part_0_40 : layerCheck 0 40 8 = true := by decide +kernel
private theorem layerCheck_part_0_48 : layerCheck 0 48 8 = true := by decide +kernel
private theorem layerCheck_part_0_56 : layerCheck 0 56 8 = true := by decide +kernel
theorem layerCheck_0a : layerCheck 0 0 64 = true := by
  exact @layerCheck_add 0 0 8 56 layerCheck_part_0_0 (@layerCheck_add 0 8 8 48 layerCheck_part_0_8 (@layerCheck_add 0 16 8 40 layerCheck_part_0_16 (@layerCheck_add 0 24 8 32 layerCheck_part_0_24 (@layerCheck_add 0 32 8 24 layerCheck_part_0_32 (@layerCheck_add 0 40 8 16 layerCheck_part_0_40 (@layerCheck_add 0 48 8 8 layerCheck_part_0_48 (layerCheck_part_0_56)))))))
private theorem layerCheck_part_0_64 : layerCheck 0 64 8 = true := by decide +kernel
private theorem layerCheck_part_0_72 : layerCheck 0 72 8 = true := by decide +kernel
private theorem layerCheck_part_0_80 : layerCheck 0 80 8 = true := by decide +kernel
private theorem layerCheck_part_0_88 : layerCheck 0 88 8 = true := by decide +kernel
private theorem layerCheck_part_0_96 : layerCheck 0 96 8 = true := by decide +kernel
private theorem layerCheck_part_0_104 : layerCheck 0 104 8 = true := by decide +kernel
private theorem layerCheck_part_0_112 : layerCheck 0 112 8 = true := by decide +kernel
private theorem layerCheck_part_0_120 : layerCheck 0 120 8 = true := by decide +kernel
theorem layerCheck_0b : layerCheck 0 64 64 = true := by
  exact @layerCheck_add 0 64 8 56 layerCheck_part_0_64 (@layerCheck_add 0 72 8 48 layerCheck_part_0_72 (@layerCheck_add 0 80 8 40 layerCheck_part_0_80 (@layerCheck_add 0 88 8 32 layerCheck_part_0_88 (@layerCheck_add 0 96 8 24 layerCheck_part_0_96 (@layerCheck_add 0 104 8 16 layerCheck_part_0_104 (@layerCheck_add 0 112 8 8 layerCheck_part_0_112 (layerCheck_part_0_120)))))))
end SigGolfCandidate.T3M.BC
end
end

section


namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def CounterWord : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat),
  LoadKind.wu.fromWord (wword w j) 0 = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wle32 w (8 * j)).toNat
theorem counterWord : CounterWord := fun w j => by
  apply BitVec.eq_of_toNat_eq
  simp [LoadKind.fromWord, extractWord32, wword_toNat, ClaudeWCT.W9.T3M.wle32,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, ← Nat.mul_assoc]
set_option maxRecDepth 100000
theorem nCopy_eq : nCopy 3 = 1 ∧ nCopy 2 = 64 ∧ nCopy 1 = 64 ∧ nCopy 0 = 128 := by decide +kernel
theorem copyCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : copyCheck lay c = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ lo n, layerCheck lay lo n = true → lo ≤ c → c < lo + n → copyCheck lay c = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · by_cases h : c < 64
    · exact hall 0 64 layerCheck_0a (by omega) (by omega)
    · exact hall 64 64 layerCheck_0b (by omega) (by omega)
  · exact hall 0 64 layerCheck_1 (by omega) (by omega)
  · exact hall 0 64 layerCheck_2 (by omega) (by omega)
  · exact hall 0 1 layerCheck_3 (by omega) (by omega)
def CounterPadBytes : Prop := ∀ (c : BitVec 32) (pad : BitVec 96),
  SphincsSecurity.bytesLE 4 c ++ SphincsSecurity.bytesLE 12 pad =
    SphincsSecurity.bytesLE 16 (pad ++ c)
theorem counterPadBytes : CounterPadBytes := fun c pad => by
  apply readLE_inj (by simp [SphincsSecurity.bytesLE_length])
  simp only [readLE_append, SphincsSecurity.bytesLE_length, readLE_bytesLE, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt c.isLt, Nat.shiftLeft_eq]
  omega
def CounterPadExtract : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (o : Nat),
  (w.extractLsb' (8 * (o + 4)) 96 ++ ClaudeWCT.W9.T3M.wle32 w o) = ClaudeWCT.W9.T3M.wdig w o
theorem counterPadExtract : CounterPadExtract := fun w o =>
  BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)
end SigGolfCandidate.T3M.BC
end
end
