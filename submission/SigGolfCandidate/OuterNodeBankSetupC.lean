import SigGolfCandidate.OuterNodeBankPrefix
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeBankSetupC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.FtsGrind W9Drv.SharedCProof

theorem c_ecall_slices : ∀ j : Fin 128,∀ l : Fin 5,
    ((OuterNodeBankLayout.cWords j.val).drop (ecIdx j.val (l.val+1))).take 1=[0x73] ∧
      ecIdx j.val (l.val+1)+1≤64 := by decide +kernel

theorem fetchC {im : Image} (j : Fin 128) (l : Fin 5)
    (hc : CodeAt im (pcOf (childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    (s : MachineState) (hp : s.pc=pcOf (childBase j.val+ecIdx j.val (l.val+1))) :
    fetch im s=some (.base .ECALL) := by
  have hsl:=c_ecall_slices j l
  have hlen:=(OuterNodeBankLayout.c_slices j).1
  have hcode:=codeAt_sub (seg:=[0x73]) (ecIdx j.val (l.val+1)) hc
    (by rw [hlen];exact hsl.2) hsl.1
  exact (CodeAt.fetch hcode s hp).trans (by rfl)

theorem lvl_core {im : Image} {j : Nat} (hj : j < 128) (hcode : CodeAt im (pcOf (childBase j)) (OuterNodeBankLayout.cWords j))
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (l : Nat) (hl : l < 6) (v : Digest) (s : MachineState)
    (hs : Mid j B k index u l v s) :
    ∃ t, Steps im s (lvlSt j l) (lvlSt j l) t ∧ (l<5→fetch im t = some (.base .ECALL)) ∧ t.getReg .x5 = 0 ∧
      t.getReg .x10 = BitVec.ofNat 64 (B + blkO j l) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = ((lvlRegs j l).get .x12).eval s ∧
      t.pc = pcOf (childBase j + ecIdx j (l + 1)) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      t.getReg .x3 = ((lvlRegs j l).get .x3).eval s ∧
      hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) ∧
      Frame s t (fun A => A = B + tw24 j l ∨ A = B + blkO j l + 16) ∧
      DigAt t (B+blkO j l) (if bitAt j l=0 then v else sibs l) ∧
      DigAt t (B+blkO j l+16) (nodeHeader k index (heapOf l j) (hpOf j tws l)) ∧
      DigAt t (B+blkO j l+48) (if bitAt j l=0 then sibs l else v) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hbl := blk_bounds j hj l hl
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (childBase j + (ecIdx j l + 1)) := by rw [hs.pc, Nat.add_assoc]
  have hst:=OuterNodeBankPrefix.runC (im:=im) ⟨j,hj⟩ ⟨l,hl⟩ hcode s hs.pc
    (lvlObl_holds j hj l hl hx8 h8 (by unfold MEMORY_BYTES;omega))
  have hreg : ∀ x, ((lvlRes j l).toState s).getReg x = ((lvlRegs j l).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((lvlRes j l).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO j l + 24 ∧ ¬ l ≤ 3 then s.getReg (heapReg (heapOf l j))
      else if A = B + blkO j l + 16 then (if l ≤ 3 then (lowE j l).eval s else s.getReg .x15)
      else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j hj l A hl hA)
  have hpcT : ((lvlRes j l).toState s).pc = pcOf (childBase j + ecIdx j (l + 1)) := by
    rw [PRes.toState_pc (lvlRes j l) s rfl]; rfl
  have hec : l<5→fetch im ((lvlRes j l).toState s)=some (.base .ECALL) := by
    intro hl5
    exact fetchC ⟨j,hj⟩ ⟨l,hl5⟩ hcode _ hpcT
  generalize ht : (lvlRes j l).toState s = t at hst hec hreg hmem hpcT
  have hb := bitAt_lt j l
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + blkO j l) := by rw [hreg, lvlRegs_x10, eX8_eval hx8]
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
    rw [hreg, lvlRegs_x11]
    split_ifs with h0
    · rfl
    · exact hs.a1 h0
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h3 h10' h11' h12'
    rw [hreg, lvlRegs_other j l r h3 h10' h11' h12', RegFile.init_get_eval]
    exact hkeep r h3 h10' h11' h12'
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.t0
  have tS : ∀ o, o ≤ 1024 → o ≠ blkO j l + 16 → o ≠ blkO j l + 24 →
      t.getMem (BitVec.ofNat 64 (B + o)) = s.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho h16 h24
    rw [hmem _ (by omega), if_neg (fun h => h24 (by have := h.1; omega)), if_neg (by omega)]
  have sU : ∀ o, o ≤ 1024 → o ∉ stagesW j (l + 1) →
      s.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho hn
    refine hs.frame (B + o) (by omega) ?_
    rintro ⟨off, hoff, he⟩
    have : off = o := by omega
    subst this; exact hn hoff
  have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) hj (by omega) h
  have hpad : DigAt t (B + blkO j l + 32) (pads l) := by
    have hP := hu.padAt l hl
    unfold padO at hP
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).1 (by unfold padO; rfl))]
    · rw [show B + (blkO j l + 32) + 8 = B + (blkO j l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        sU _ (by omega) (fun h => (hf _ h).2.1 (by unfold padO; omega))]
  have hcs := sibO_cases j l hl
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l hl
    have hsb : sibO l j = blkO j l ∨ sibO l j = blkO j l + 48 := by omega
    refine DigAt.of_eq hS ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.1 rfl)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.2 rfl)]
  have hnode : DigAt t (B + curO l j) v := by
    have hcb := curO_cases j l
    refine DigAt.of_eq hs.node ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega)]
  have hx15 : s.getReg .x15 = BitVec.ofNat 64 (w0n k index) :=
    (hkeep .x15 (by decide) (by decide) (by decide) (by decide)).trans hu.w0
  have hw0 : 0 ≤ w0n k index ∧ w0n k index < 2 ^ 64 := by
    have := Nat.mod_lt index (show 0 < 2 ^ 31 by norm_num)
    have := Nat.mod_lt k (show 0 < 16 by norm_num)
    unfold w0n V3.nodeLow
    rw [ClaudeWCT.WCT9.ftsLeafLow_zero]
    unfold SigGolfCandidate.T3.ftsBiasN
    omega
  have hhdr : DigAt t (B + blkO j l + 16) (nodeHeader k index (heapOf l j) (hpOf j tws l)) := by
    by_cases h3 : l ≤ 3
    · have hpk := heapOf_packed j l hj h3
      constructor
      · rw [hmem _ (by omega), if_neg (fun h => by have := h.1; omega), if_pos rfl, if_pos h3, hdr11_lo,
          if_pos hpk]
        unfold lowE
        rw [addC_eval]
        simp only [E.eval]
        rw [hx15]
        exact ofNat_add_neg_wrap _ _ (by omega)
      · rw [show B + blkO j l + 16 + 8 = B + blkO j l + 24 by omega, hdr11_hi, if_pos hpk]
        rw [hmem _ (by omega), if_neg (fun h => h.2 h3), if_neg (by omega),
          show B + blkO j l + 24 = B + (blkO j l + 24) by omega,
          sU _ (by omega) (fun hm => tw_free hj (by omega) hm rfl)]
        have hT := (hu.twAt l hl).2
        rw [show B + blkO j l + 16 + 8 = B + (blkO j l + 24) by omega] at hT
        rw [hT]
        unfold hpOf; rw [if_pos (by omega)]
    · have hlo := heapOf_low j l hj (by omega) (by omega)
      have hnp : ¬ (8 ≤ heapOf l j ∧ heapOf l j < 128) := by omega
      constructor
      · rw [hmem _ (by omega), if_neg (fun h => by have := h.1; omega), if_pos rfl, if_neg h3, hdr11_lo,
          if_neg hnp, hx15]
      · rw [show B + blkO j l + 16 + 8 = B + blkO j l + 24 by omega, hmem _ (by omega),
          if_pos ⟨rfl, h3⟩, hdr11_hi, if_neg hnp]
        have hs64 : s.getReg .x11 = BitVec.ofNat 64 64 := hs.a1 (by omega)
        have hr := heapReg_eval (s := s) (l := l) hj (by omega) (by omega) hs64 (fun h h1 h6 => by
          obtain ⟨n3, n10, n11, n12⟩ := heapReg_ne h h6
          rw [hkeep _ n3 n10 n11 n12]; exact hu.heaps h h1 h6)
        exact hr
  have hin : hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) := by
    unfold nodeIn
    rcases hcs with ⟨e0, ec, es⟩ | ⟨e1, ec, es⟩
    · simp only [e0, if_true]
      rw [ec] at hnode; rw [es, ← Nat.add_assoc] at hsib
      exact W9Drv.SharedCProof.hashInput_blk4 t _ _ _ _ _ h10 h11 (by omega) (by omega) hnode hhdr hpad hsib
    · simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
      rw [ec, ← Nat.add_assoc] at hnode; rw [es] at hsib
      exact W9Drv.SharedCProof.hashInput_blk4 t _ _ _ _ _ h10 h11 (by omega) (by omega) hsib hhdr hpad hnode
  have hpair : DigAt t (B+blkO j l) (if bitAt j l=0 then v else sibs l) ∧
      DigAt t (B+blkO j l+48) (if bitAt j l=0 then sibs l else v) := by
    rcases hcs with ⟨e0,ec,es⟩|⟨e1,ec,es⟩
    · simp only [e0,if_true]
      rw [ec] at hnode
      rw [es,←Nat.add_assoc] at hsib
      exact ⟨hnode,hsib⟩
    · simp only [e1,show (1:Nat)≠0 by decide,if_false]
      rw [ec,←Nat.add_assoc] at hnode
      rw [es] at hsib
      exact ⟨hsib,hnode⟩
  refine ⟨t, hst, hec, h5, h10, h11, hreg .x12, hpcT, hother, hreg .x3, hin, ?_,hpair.1,hhdr,hpair.2⟩
  intro A hA hn
  simp only [not_or] at hn
  rw [hmem A hA, if_neg ?_, if_neg hn.2]
  rintro ⟨h24, hc⟩
  apply hn.1
  unfold tw24
  rw [if_neg hc]
  exact h24

theorem last_setup {im : Image} {j : Nat} (hj : j < 128) (hcode : CodeAt im (pcOf (childBase j)) (OuterNodeBankLayout.cWords j))
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 768 ≤ B)
    (v : Digest) (s : MachineState) (hs : Mid j B k index u 5 v s) :
    ∃ t, Steps im s 4 4 t ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v 5)) ∧
      t.pc = pcOf (childBase j + ecIdx j 6) ∧ t.getReg .x11 = 64 ∧
      t.getReg .x10=BitVec.ofNat 64 (B+blkO j 5) ∧
      t.getReg .x12 = BitVec.ofNat 64 (B - handO j) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      Frame u t (fun A => ∃ off ∈ stagesW j 6, A = B + off) ∧
      DigAt t (B+blkO j 5) (if bitAt j 5=0 then v else sibs 5) ∧
      DigAt t (B+blkO j 5+16) (nodeHeader k index (heapOf 5 j) (hpOf j tws 5)) ∧
      DigAt t (B+blkO j 5+48) (if bitAt j 5=0 then sibs 5 else v) := by
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have h8 := hu.base8
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B :=
    (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, hec, h5, h10, h11, h12', hpcT, hother, -, hin, hP,hleft,hhdr,hright⟩ := lvl_core hj hcode hu 5 (by decide) v s hs
  have hl5 : lvlSt j 5 = 4 := by
    have h6 : ecIdx j 6 = ecIdx j 5 + lvlLen j 5 + (if 5 = 0 then 1 else 0) := rfl
    have hlen : lvlLen j 5 = 5 := by simp [lvlLen, skipA2_five]
    unfold lvlSt; rw [h6, hlen, if_neg (by decide)]; omega
  rw [hl5] at hst
  have hbl := blk_bounds j hj 5 (by decide)
  have hho := handO_cases j
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B - handO j) := by
    rw [h12', show (lvlRegs j 5).get .x12 = addC (.reg .x8) (BitVec.ofNat 64 (2 ^ 64 - handO j)) by
      unfold lvlRegs; rw [skipA2_five]; rfl, addC_eval]
    simp only [E.eval, hx8]
    exact ofNat_add_neg B (handO j) (by omega) (by omega) (by omega)
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO j 5) 64 (B - handO j) h10 h11 h12 (by omega) (by decide)
      (by omega) (by omega) (by omega)
  refine ⟨t, hst, h5, hv, hin, hpcT, h11, h10, h12, hother, ?_,hleft,hhdr,hright⟩
  apply (hs.frame.trans hP).mono
  intro A hA h
  rcases h with h | rfl | rfl
  · exact h
  · exact ⟨tw24 j 5, mem_stagesW (m := 5) (by omega) (by simp [stageW]), rfl⟩
  · exact ⟨blkO j 5 + 16, mem_stagesW (m := 5) (by omega) (by simp [stageW]), by omega⟩

#print axioms lvl_core
#print axioms last_setup
end OuterNodeBankSetupC
