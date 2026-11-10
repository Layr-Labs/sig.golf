import SigGolfCandidate.FtsCopyCPieces
set_option debug.skipKernelTC true
set_option linter.all false

/-! # FTS carrier grind: a C family child routine through its expand copy refines `childProgramC`

The routine enters copy `j` at `copyBase j + 1` with the bank routine's entry state (`ChildPre`, read at the bank
pc). The copy computes the leaf and levels 0..2 exactly as the bank; at the level-3 fold it jumps to the
trampoline, which grinds the node with `tramp_search` and returns into the bank after the bank's level-3 `ecall`.
The bank finishes (level 4, the hand) with its proved `tail_tbsim`, run from a virtual entry state that agrees with
the real one except on the words the copy and the search wrote. -/

namespace W9Drv.SharedCProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.FtsGrind (SEARCH searchWords trampWords SearchIn SearchOut tramp_search widthOf
  groundFold W_SEARCH FUEL slotA SCR WADJ frame_readWordsG)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def CopyCodeAt (im : Image) (j : Nat) : Prop :=
  ∀ i w, (copyPre j)[i]? = some w → im.code[copyBase j + i]? = some w

theorem copyLook_ok {im : Image} {j : Nat} (h : CopyCodeAt im j) : LookOK im (copyLook j) := by
  intro n w hw
  unfold copyLook at hw
  split at hw
  · rename_i hle
    have := h (n - copyBase j) w hw
    rwa [Nat.add_sub_cancel' hle] at this
  · cases hw

theorem copyRun_sound {im : Image} {j i : Nat} {r : PRes} (hcode : CopyCodeAt im j)
    (h : copyRun j i = some r) (s : MachineState) (hpc : s.pc = pcOf (copyBase j + i))
    (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : r.brs = []) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h (copyLook_ok hcode) s hpc (by intro p hp; cases hp) hobl
    (by rw [hbr]; intro b hb; cases hb)

/-- Entry: the bank's `ChildPre`, read at the bank entry pc. -/
def bankPc (j : Nat) (u : MachineState) : MachineState := u.setPC (pcOf (childBase j + 1))

/-- After the copy's level `l` value (`l ≤ 3`). -/
structure MidC (j B k index : Nat) (u : MachineState) (l : Nat) (v : Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (copyBase j + ecIdx j l + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  a1 : l ≠ 0 → s.getReg .x11 = BitVec.ofNat 64 64
  a2 : s.getReg .x12 = BitVec.ofNat 64 (B + outO l j)
  node : DigAt s (B + curO l j) v
  frame : Frame u s (fun A => ∃ off ∈ stagesW j (l + 1), A = B + off)

variable {sk : BitVec 256}

theorem lvl_coreC {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (l : Nat) (hl : l < 4) (v : Digest) (s : MachineState)
    (hs : MidC j B k index u l v s) :
    ∃ t, Steps im s (lvlSt j l) (lvlSt j l) t ∧ (l < 2 → fetch im t = some (.base .ECALL)) ∧ t.getReg .x5 = 0 ∧
      t.getReg .x10 = BitVec.ofNat 64 (B + blkO j l) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = ((lvlRegs j l).get .x12).eval s ∧
      t.pc = pcOf (copyBase j + ecIdx j (l + 1)) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      t.getReg .x3 = ((lvlRegs j l).get .x3).eval s ∧
      hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) ∧
      Frame s t (fun A => A = B + tw24 j l ∨ A = B + blkO j l + 16) ∧
      DigAt t (B + blkO j l) (if bitAt j l = 0 then v else sibs l) ∧
      DigAt t (B + blkO j l + 16) (nodeHeader k index (heapOf l j) (hpOf j tws l)) ∧
      DigAt t (B + blkO j l + 48) (if bitAt j l = 0 then sibs l else v) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hbl := blk_bounds j hj l (by omega)
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (copyBase j + (ecIdx j l + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, hec⟩ := copyRun_sound hcode (copyRun_lvl j hj l (by omega)) s hpc
    (lvlObl_holds j hj l (by omega) hx8 h8 (by unfold MEMORY_BYTES; omega)) rfl
  have hreg : ∀ x, ((clvlRes j l).toState s).getReg x = ((lvlRegs j l).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((clvlRes j l).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO j l + 24 ∧ ¬ l ≤ 3 then s.getReg (heapReg (heapOf l j))
      else if A = B + blkO j l + 16 then (if l ≤ 3 then (lowE j l).eval s else s.getReg .x15)
      else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j hj l A (by omega) hA)
  have hpcT : ((clvlRes j l).toState s).pc = pcOf (copyBase j + ecIdx j (l + 1)) := by
    rw [PRes.toState_pc (clvlRes j l) s rfl]; rfl
  generalize ht : (clvlRes j l).toState s = t at hst hec hreg hmem hpcT
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
    have hP := hu.padAt l (by omega)
    unfold padO at hP
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).1 (by unfold padO; rfl))]
    · rw [show B + (blkO j l + 32) + 8 = B + (blkO j l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        sU _ (by omega) (fun h => (hf _ h).2.1 (by unfold padO; omega))]
  have hcs := sibO_cases j l (by omega)
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l (by omega)
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
        have hT := (hu.twAt l (by omega)).2
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
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by omega) (by omega) hnode hhdr hpad hsib
    · simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
      rw [ec, ← Nat.add_assoc] at hnode; rw [es] at hsib
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by omega) (by omega) hsib hhdr hpad hnode
  have hpair : DigAt t (B + blkO j l) (if bitAt j l = 0 then v else sibs l) ∧
      DigAt t (B + blkO j l + 48) (if bitAt j l = 0 then sibs l else v) := by
    rcases sibO_cases j l (by omega) with ⟨e0, ec, es⟩ | ⟨e1, ec, es⟩
    · simp only [e0, if_true]
      rw [ec] at hnode; rw [es, ← Nat.add_assoc] at hsib
      exact ⟨hnode, hsib⟩
    · simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
      rw [ec, ← Nat.add_assoc] at hnode; rw [es] at hsib
      exact ⟨hsib, hnode⟩
  refine ⟨t, hst, fun h3 => hec (by simp [clvlRes, h3]), h5, h10, h11, hreg .x12, hpcT, hother, hreg .x3, hin, ?_,
    hpair.1, hhdr, hpair.2⟩
  intro A hA hn
  simp only [not_or] at hn
  rw [hmem A hA, if_neg ?_, if_neg hn.2]
  rintro ⟨h24, hc⟩
  apply hn.1
  unfold tw24
  rw [if_neg hc]
  exact h24
theorem lvl_stepC {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (l : Nat) (hl : l < 2) (v : Digest) (s : MachineState)
    (hs : MidC j B k index u l v s) :
    ∃ t, Steps im s (lvlSt j l) (lvlSt j l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) ∧
      ∀ a : BitVec 256, MidC j B k index u (l + 1) (selD j (l + 1) a) (writeHash t a) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, hec, h5, h10, h11, h12', hpcT, hother, h3', hin, hP, -, -, -⟩ := lvl_coreC hj hcode hu l (by omega) v s hs
  have hbl := blk_bounds j hj l (by omega)
  have hbl1 := blk_bounds j hj (l + 1) (by omega)
  have hb1 := bitAt_lt j (l + 1)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + outO (l + 1) j) := by
    rw [h12', lvlRegs_x12 j l (by omega)]
    by_cases hsk : skipA2 j l = true
    · rw [if_pos hsk, skipA2_out hsk]
      simp only [E.eval]
      exact (hs.a2)
    · rw [if_neg hsk, eX8_eval hx8]
  have hoa := outO_arith j (l + 1) hj (by omega)
  have hcur : outO (l + 1) j % 8 = 0 ∧ outO (l + 1) j + 32 ≤ 864 := by
    have := curO_cases j (l + 1); omega
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO j l) 64 (B + outO (l + 1) j) h10 h11 h12 (by omega) (by decide)
      (by omega) (by omega) (by omega)
  refine ⟨t, hst, hec hl, h5, hv, hin, fun a => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]
  · intro r h3 h10' h11' h12'; rw [writeHash_getReg]; exact hother r h3 h10' h11' h12'
  · intro _; rw [writeHash_getReg]; exact h11
  · rw [writeHash_getReg]; exact h12
  · exact DigAt_selD t a hj (by omega) h12 (by omega)
  · have hW := frame_writeHash4 t a (B + outO (l + 1) j) h12 (by omega)
    refine ((hs.frame.trans hP).trans hW).mono ?_
    intro A _ hA
    rcases hA with (⟨off, hoff, rfl⟩ | (rfl | rfl)) | (rfl | rfl | rfl | rfl)
    · exact ⟨off, stagesW_mono hoff (by omega), rfl⟩
    · exact ⟨tw24 j l, mem_stagesW (m := l) (by omega) (by simp [stageW]), rfl⟩
    · exact ⟨blkO j l + 16, mem_stagesW (m := l) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨outO (l + 1) j, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), rfl⟩
    · exact ⟨outO (l + 1) j + 8, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨outO (l + 1) j + 16, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨outO (l + 1) j + 24, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
theorem leafC_tbsim {im : Image} {j : Nat} (hj : j<128) (hcode : CopyCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat→Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) {x : MachineState} (hxu : u = bankPc j x)
    (hpu : x.pc = pcOf (copyBase j + 1)) :
    TBSim im sk x 17 (SharedV3.hashSel (hiSel j 0) (leafBytes leaf)) (MidC j B k index u 0) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hRx : ∀ r, x.getReg r = u.getReg r := by subst hxu; intro r; cases r <;> rfl
  have hMx : ∀ A, x.getMem A = u.getMem A := by subst hxu; intro A; rfl
  have hobl : ∀ o ∈ (cp0Res j).st.obl, o.holds x := by
    intro o ho
    simp only [cp0Res, p0Res, List.not_mem_nil] at ho
  obtain ⟨hst, hec⟩ := copyRun_sound hcode (copyRun_p0 j hj) x hpu hobl rfl
  have hreg : ∀ y, ((cp0Res j).toState x).getReg y =
      ((RegFile.init.set .x12 (eX8 (outO 0 j))).get y).eval x := fun y => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((cp0Res j).toState x).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [PRes.toState_getMem, ← hMx]
    simp only [cp0Res, p0Res, memEval_nil]
  have hpcT : ((cp0Res j).toState x).pc = pcOf (copyBase j + 2) := PRes.toState_pc (cp0Res j) x rfl
  generalize ht : (cp0Res j).toState x = t at hst hec hreg hmem hpcT
  have hother : ∀ r : Reg, r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h12; rw [hreg, RegFile.get_set_ne _ _ h12, RegFile.init_get_eval, hRx]
  have hb0 := blk_bounds j hj 0 (by decide)
  have hoa0 := outO_arith j 0 hj (by decide)
  have hc0 : outO 0 j % 8 = 0 ∧ outO 0 j + 32 ≤ 864 := by have := curO_cases j 0; omega
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + leafO) := (hother .x10 (by decide)).trans hu.a0
  have h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (1 + 1)) := (hother .x11 (by decide)).trans hu.a1
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + outO 0 j) := by
    rw [hreg, RegFile.get_set_self _ _ (by decide), eX8_eval ((hRx _).trans hu.s0)]
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide)).trans hu.t0
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + leafO) 128 (B + outO 0 j) h10 h11 h12 (by unfold leafO; omega) (by decide)
      (by unfold leafO; omega) (by omega) (by omega)
  have hslot : ∀ i, i < 8 → DigAt t (B + leafO + 16 * i) (leaf i) := by
    intro i hi
    refine DigAt.of_eq (hu.leafAt i hi) ?_ ?_
    · rw [hmem _ (by unfold leafO; omega)]
    · rw [hmem _ (by unfold leafO; omega)]
  have hin : hashInput t = toQ (pad64 (leafBytes leaf)) := by
    rw [pad64_of_aligned _ (by rw [leafBytes_length])]
    apply hashInput_toQ t _ 1 (B + leafO) (leafBytes_length leaf) h10 (by unfold leafO; omega)
      (by unfold leafO; omega) h11 (by norm_num)
    have hD : DigsAt t (B + leafO) ((List.range 8).map leaf) := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      have e : ((List.range 8).map leaf).getD i 0 = leaf i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rw [e]
      exact hslot i hi
    have hw := hD.words
    simp only [List.length_map, List.length_range] at hw
    rw [hw]
    rfl

  have hmid (a : BitVec 256) : MidC j B k index u 0 (selD j 0 a) (writeHash t a) := by
    refine ⟨?_, ?_, fun h => absurd rfl h, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]; rfl
    · intro r _ _ _ h12'; rw [writeHash_getReg]; exact hother r h12'
    · rw [writeHash_getReg]; exact h12
    · exact DigAt_selD t a hj (by decide) h12 (by omega)
    · have hT : Frame u t (fun _ => False) := by
        intro A hA _
        rw [hmem A hA]
      refine (hT.trans (frame_writeHash4 t a (B + outO 0 j) h12 (by omega))).mono ?_
      intro A _ hA
      rcases hA with hF | (rfl | rfl | rfl | rfl)
      · exact hF.elim
      · exact ⟨outO 0 j, mem_stagesW (m := 0) (by omega) (by simp [stageW]), rfl⟩
      · exact ⟨outO 0 j + 8, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
      · exact ⟨outO 0 j + 16, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
      · exact ⟨outO 0 j + 24, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
  have H : TBSim im sk t (8*(toQ (pad64 (leafBytes leaf))).blocks+0)
      (SharedV3.hashSel (hiSel j 0) (leafBytes leaf) >>= pure) (MidC j B k index u 0) :=
    TBSim.hashSel_bind (hec rfl) h5 hv hin (fun a=>TBSim.pure (hmid a))
  rw [bind_pure,leaf_blocks] at H
  exact (TBSim.steps hst H).mono (by simp only [cp0Res, p0Res];omega) (fun _ _ h=>h)

theorem restC_tbsim {im : Image} {j : Nat} (hj : j<128) (hcode : CopyCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat→Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) :
    ∀ n l v state,l+n=2→MidC j B k index u l v state→
      TBSim im sk state (cycR j l n)
        ((List.range' l n).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v)
        (MidC j B k index u 2) := by
  intro n
  induction n with
  | zero =>
      intro l v state hln hs
      have hl:l=2:=by omega
      subst l
      simpa only [List.range'_zero,List.foldlM_nil,cycR] using (TBSim.pure hs (sk:=sk) (image:=im))
  | succ n ih =>
      intro l v state hln hs
      obtain ⟨t,hst,hf,h5,hv,hin,hpost⟩:=lvl_stepC hj hcode hu l (by omega) v state hs
      rw [List.range'_succ,List.foldlM_cons,childLevelP_eq]
      have H:=TBSim.hashSel_bind (sk:=sk) (W:=cycR j (l+1) n) (hi:=hiSel j (l+1))
        (f:=fun v'=>(List.range' (l+1) n).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v')
        (Q:=MidC j B k index u 2) hf h5 hv hin
        (fun a=>ih (l+1) _ _ (by omega) (hpost a))
      rw [nodeIn_blocks] at H
      simpa only [cycR,Nat.add_assoc] using TBSim.steps hst H

/-! ## Level 3 through the trampoline, then the bank's tail -/

/-- Level-3 ground trial halves: `pre = pair.1 ‖ header`, `right = pair.2`. -/
def preC (k index j : Nat) (tws sibs : Nat → Digest) (v : Digest) : List UInt8 :=
  bytesLE 16 (if bitAt j 3 = 0 then v else sibs 3) ++ bytesLE 16 (nodeHeader k index (heapOf 3 j) (hpOf j tws 3))
def rightC (j : Nat) (sibs : Nat → Digest) (v : Digest) : List UInt8 :=
  bytesLE 16 (if bitAt j 3 = 0 then sibs 3 else v)

/-- Back at the caller (`ra + 300`) after a copy routine: the bank's `HandPost`, plus the nonce record and the
re-zeroed search scratch; the frame adds the record, the saves and `SCR`. -/
structure HandPostC (B j : Nat) (u : MachineState) (res : Nat × Digest) (t : MachineState) : Prop where
  pc : t.pc = (u.getReg .x1 + 316) &&& ~~~1#64
  a1 : t.getReg .x11 = 64
  top : DigAt t (B - valO j) res.2
  a2 : t.getReg .x12 = BitVec.ofNat 64 (B - handO j)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r
  slot0 : t.getMem (BitVec.ofNat 64 (slotA B)) = BitVec.ofNat 64 (B + blkO j 3 + WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slotA B + 8)) = BitVec.ofNat 64 res.1
  nle : res.1 ≤ FUEL (widthOf B)
  saves : ∀ i < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * i)) = 0
  scr : ∀ i < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * i)) = 0
  frame : Frame u t (fun A => prefixWrites B A ∨ (B - handO j ≤ A ∧ A < B - handO j + 32) ∨
    (slotA B ≤ A ∧ A < slotA B + 16) ∨ (1104 ≤ A ∧ A < 1144) ∨ (SCR ≤ A ∧ A < SCR + 32))

/-- A digest read back from memory. -/
def rdD (s : MachineState) (A : Nat) : Digest := s.getMem (BitVec.ofNat 64 (A + 8)) ++ s.getMem (BitVec.ofNat 64 A)
theorem digAt_rdD (s : MachineState) (A : Nat) : DigAt s A (rdD s A) :=
  ⟨BitVec.extractLsb'_append_eq_right.symm, BitVec.extractLsb'_append_eq_left.symm⟩

/-- The virtual bank entry state: registers and stage words of the real entry `u`, everything else from `s`. -/
def virt (j B : Nat) (u s : MachineState) : MachineState :=
  { s with regs := u.regs, pc := pcOf (childBase j + 1),
           mem := fun A => if (stagesW j 5).any (fun off => A == BitVec.ofNat 64 (B + off)) then u.mem A else s.mem A }

theorem virt_getReg (j B : Nat) (u s : MachineState) (r : Reg) : (virt j B u s).getReg r = u.getReg r := by
  cases r <;> rfl
theorem virt_getMem (j B : Nat) (u s : MachineState) (hB : B + 1024 < 2 ^ 64) (hj : j < 128) (A : Nat)
    (hA : A < 2 ^ 64) :
    (virt j B u s).getMem (BitVec.ofNat 64 A) =
      if ∃ off ∈ stagesW j 5, A = B + off then u.getMem (BitVec.ofNat 64 A) else s.getMem (BitVec.ofNat 64 A) := by
  show (if _ then _ else _) = _
  congr 1
  apply propext
  rw [List.any_eq_true]
  constructor
  · rintro ⟨off, h1, h2⟩
    have hb := stagesW_bound hj (by decide) h1
    refine ⟨off, h1, (ofNat_inj hA (by omega)).mp (by simpa using h2)⟩
  · rintro ⟨off, h1, rfl⟩
    exact ⟨off, h1, by simp⟩

theorem lowHalf (a : BitVec 256) :
    (a.extractLsb' 0 128).extractLsb' 0 64 = a.extractLsb' 0 64 ∧
      (a.extractLsb' 0 128).extractLsb' 64 64 = a.extractLsb' 64 64 := by
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero] <;> omega

theorem codeAt_one {im : Image} {n : Nat} {w : BitVec 32} (h : im.code[n]? = some w) (hn : n < 2 ^ 60) :
    CodeAt im (pcOf n) [w] := by
  have hp : (pcOf n).toNat = 0x1000 + 4 * n := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, by omega, by simp; omega, ?_⟩
  rw [hp, show (0x1000 + 4 * n - 0x1000) / 4 = n by omega]
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hl, he]
  exact ⟨_, rfl⟩

section main
variable {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j) (hbank : ChildCodeAt im j)
  (hS : CodeAt im (pcOf SEARCH) searchWords)
  (hT : CodeAt im (pcOf (trampOf j)) (trampWords (trampOf j) SEARCH (siteB j + 1)))
  {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
  (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 1848 ≤ B) (hB : B < 2 ^ 14)
include hj hcode hbank hS hT hu hlo hB

/-- Level 3 (the ground fold through the trampoline) and the bank's tail. -/
theorem lvl3C_tbsim (v : Digest) (s : MachineState) (hs : MidC j B k index u 3 v s) :
    TBSim im sk s (lvlSt j 3 + 1 + W_SEARCH (widthOf B) + (cycR j 4 1 + 13))
      (groundFold (widthOf B) (preC k index j tws sibs v) (rightC j sibs v) >>= fun r =>
        (List.range' 4 1).foldlM (childLevelP k index j pads (hpOf j tws) sibs) (r.2.extractLsb' 0 128) >>= fun v5 =>
        childLevelTop k index j pads (hpOf j tws) sibs v5 >>= fun c => pure (r.1, c))
      (HandPostC B j u) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hsl := site_lt j hj
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, -, h5, h10, h11, h12', hpcT, hother, -, -, hP, hpre1, hhdr, hright⟩ :=
    lvl_coreC hj hcode hu 3 (by decide) v s hs
  have hbl := blk_bounds j hj 3 (by decide)
  have hbl4 := blk_bounds j hj 4 (by decide)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + outO 4 j) := by
    rw [h12', lvlRegs_x12 j 3 (by decide)]
    by_cases hsk : skipA2 j 3 = true
    · rw [if_pos hsk, skipA2_out hsk]
      simp only [E.eval]
      exact hs.a2
    · rw [if_neg hsk, eX8_eval hx8]
  have hoa := outO_lo (hiSel_four j hj)
  have hcur : outO 4 j % 8 = 0 ∧ outO 4 j + 32 ≤ 864 := by have := curO_cases j 4; omega
  -- the site `jal`
  have hjal : CodeAt im (pcOf (siteC j))
      [SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (siteC j) (trampOf j))] := by
    refine codeAt_one ?_ (by unfold siteC copyBase cSlot SigGolfCandidate.FtsGrind.COPY_K8; omega)
    have hlen : (((childWords j).take (ecIdx j 4)).set (ecIdx j 3)
        (SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (site16C j) (tramp16Of j)))).length =
        ecIdx j 4 := by
      rw [List.length_set, List.length_take]; have := ecIdx4_le j hj; omega
    have := hcode (ecIdx j 4)
      (SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (siteC j) (trampOf j))) (by
      unfold copyPre; rw [List.getElem?_append_right (by omega), hlen]; simp)
    simpa [siteC] using this
  have hjs := SigGolfCandidate.FtsGrind.jal_step (r := .x0) (by decide) rfl hjal
    (by unfold siteC copyBase cSlot SigGolfCandidate.FtsGrind.COPY_K8; omega)
    (by unfold trampOf cSlot SigGolfCandidate.FtsGrind.TRAMP; omega) t (by rw [hpcT]; rfl)
  set t1 := ((t.setReg .x0 (pcOf (siteC j + 1))).setPC (pcOf (trampOf j))) with ht1
  have r1 : ∀ r, t1.getReg r = t.getReg r := fun r => by cases r <;> rfl
  have m1 : Frame t t1 (fun _ => False) := fun _ _ _ => rfl
  have hA : (B + blkO j 3) % 8 = 0 := by omega
  have F : SearchIn (trampOf j) (siteB j + 1) (B + blkO j 3) (B + outO 4 j) B
      (preC k index j tws sibs v) (rightC j sibs v) t1 :=
    { pc := rfl
      x5 := by rw [r1]; exact h5
      x8 := by rw [r1, hother .x8 (by decide) (by decide) (by decide) (by decide)]; exact hu.s0
      x10 := by rw [r1]; exact h10
      x11 := by rw [r1]; exact h11
      x12 := by rw [r1]; exact h12
      lpre := by simp [preC, bytesLE_length]
      lright := by simp [rightC, bytesLE_length]
      mpre := by
        rw [frame_readWordsG m1 _ 4 (by omega) (fun _ _ h => h), show (4 : Nat) = 2 + 2 from rfl, readWords_add,
          hpre1.words, show B + blkO j 3 + 8 * 2 = B + blkO j 3 + 16 by ring, hhdr.words, preC,
          wordsOf_append _ _ (by simp [bytesLE_length])]
      mright := by
        rw [frame_readWordsG m1 _ 2 (by omega) (fun _ _ h => h), hright.words, rightC]
      hA := hA
      hA1 := by omega
      hA2 := by simp only [SCR]; omega
      hD := by omega
      hD1 := by omega
      hD2 := by simp only [SCR]; omega
      hS0 := h8
      hS1 := by omega
      hS2 := hB
      hb := by unfold trampOf cSlot SigGolfCandidate.FtsGrind.TRAMP; omega
      hret := by unfold siteB childBase; omega }
  have HS := tramp_search (sk := sk) hS hT F
  refine (TBSim.steps hst (TBSim.steps hjs (TBSim.bind (W₂ := cycR j 4 1 + (13 + 0)) HS (fun r s6 ho => ?_)))).mono (by omega) (fun _ _ h => h)
  -- the virtual bank entry and the bank's tail
  have hBl : B + 1024 < 2 ^ 64 := by omega
  set u' := virt j B u s6 with hvd
  have g6 : ∀ x, x ∉ ([] : List Reg) → s6.getReg x = t1.getReg x := ho.regs
  have hsw : ∀ X, X < 2 ^ 64 → ¬ (∃ off ∈ stagesW j 5, X = B + off) →
      ¬ (X = B + padO j 3 ∨ X = B + padO j 3 + 8) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA B ≤ X ∧ X < slotA B + 16) → ¬ (1104 ≤ X ∧ X < 1144) →
      s6.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := by
    intro X hX h1 h2 h3 h4 h5'
    have e6 := ho.frame.get hX (by
      unfold SigGolfCandidate.FtsGrind.SearchW
      rintro (h | h | h | h | h | h)
      · rcases h with h | h | h | h
        · exact h1 ⟨outO 4 j, mem_stagesW (m := 4) (by omega) (by simp [stageW]), h⟩
        · exact h1 ⟨outO 4 j + 8, mem_stagesW (m := 4) (by omega) (by simp [stageW]), by omega⟩
        · exact h1 ⟨outO 4 j + 16, mem_stagesW (m := 4) (by omega) (by simp [stageW]), by omega⟩
        · exact h1 ⟨outO 4 j + 24, mem_stagesW (m := 4) (by omega) (by simp [stageW]), by omega⟩
      · exact h2 (Or.inl (by unfold padO; omega))
      · exact h2 (Or.inr (by unfold padO; omega))
      · exact h4 h
      · exact h5' h
      · exact h3 h)
    rw [e6, m1.get hX (fun h => h), hP.get hX (by
      rintro (h | h)
      · exact h1 ⟨tw24 j 3, mem_stagesW (m := 3) (by omega) (by simp [stageW]), h⟩
      · exact h1 ⟨blkO j 3 + 16, mem_stagesW (m := 3) (by omega) (by simp [stageW]), by omega⟩)]
    exact hs.frame.get hX (fun ⟨off, hoff, he⟩ => h1 ⟨off, stagesW_mono hoff (by omega), he⟩)
  have hvu : ∀ X, X < 2 ^ 64 → ¬ (X = B + padO j 3 ∨ X = B + padO j 3 + 8) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA B ≤ X ∧ X < slotA B + 16) → ¬ (1104 ≤ X ∧ X < 1144) →
      u'.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := by
    intro X hX h2 h3 h4 h5'
    rw [hvd, virt_getMem j B u s6 hBl hj X hX]
    split_ifs with hw
    · rfl
    · exact hsw X hX hw h2 h3 h4 h5'
  have hp3 := pad3_prefix j hj
  have hbl5 := blk_bounds j hj 5 (by decide)
  have hbl0 : padO j 4 % 16 = 0 ∧ sibO 4 j % 16 = 0 ∧ padO j 3 % 16 = 0 ∧ padO j 5 % 16 = 0 ∧
      sibO 5 j % 16 = 0 := by
    have := sibO_cases j 4 (by decide); have := sibO_cases j 5 (by decide); unfold padO; omega
  have far : ∀ X, B ≤ X → X < B + 1024 → ¬ (SCR ≤ X ∧ X < SCR + 32) ∧ ¬ (slotA B ≤ X ∧ X < slotA B + 16) ∧
      ¬ (1104 ≤ X ∧ X < 1144) := fun X h1 h2 => by simp only [SCR, slotA]; omega
  have hsb4 := sibO_cases j 4 (by decide)
  have hsb5 := sibO_cases j 5 (by decide)
  have dig4 : ∀ (o : Nat) (d : Digest), (o = padO j 4 ∨ o = sibO 4 j ∨ o = padO j 5 ∨ o = sibO 5 j) →
      o + 16 ≤ 1024 → DigAt u (B + o) d →
      DigAt u' (B + o) d := by
    intro o d ho hlt hd
    have h16 : o % 16 = 0 ∧ o ≠ padO j 3 := by rcases ho with rfl | rfl | rfl | rfl <;> omega
    refine DigAt.of_eq hd ?_ ?_
    · have := far (B + o) (by omega) (by omega)
      exact hvu _ (by omega) (by omega) this.1 this.2.1 this.2.2
    · have := far (B + o + 8) (by omega) (by omega)
      exact hvu _ (by omega) (by omega) this.1 this.2.1 this.2.2
  let pads' : Nat → Digest := fun l => if l = 4 ∨ l = 5 then pads l else rdD u' (B + padO j l)
  let sibs' : Nat → Digest := fun l => if l = 4 ∨ l = 5 then sibs l else rdD u' (B + sibO l j)
  let tws' : Nat → Digest := fun l => rdD u' (B + blkO j l + 16)
  let leaf' : Nat → Digest := fun i => rdD u' (B + leafO + 16 * i)
  have hu' : ChildPre j B k index leaf' pads' sibs' tws' u' :=
    { pc := rfl
      base8 := h8
      baseHi := hu.baseHi
      t0 := by rw [virt_getReg]; exact hu.t0
      s0 := by rw [virt_getReg]; exact hu.s0
      a0 := by rw [virt_getReg]; exact hu.a0
      a1 := by rw [virt_getReg]; exact hu.a1
      w0 := by rw [virt_getReg]; exact hu.w0
      heaps := fun h h1 h2 => by rw [virt_getReg]; exact hu.heaps h h1 h2
      leafAt := fun i _ => digAt_rdD _ _
      padAt := fun l hl => by
        by_cases e : l = 4 ∨ l = 5
        · simp only [pads', if_pos e]
          rcases e with rfl | rfl
          · exact dig4 _ _ (Or.inl rfl) (by unfold padO; omega) (hu.padAt 4 (by decide))
          · exact dig4 _ _ (Or.inr (Or.inr (Or.inl rfl))) (by unfold padO; omega) (hu.padAt 5 (by decide))
        · simp only [pads', if_neg e]; exact digAt_rdD _ _
      sibAt := fun l hl => by
        by_cases e : l = 4 ∨ l = 5
        · simp only [sibs', if_pos e]
          rcases e with rfl | rfl
          · exact dig4 _ _ (Or.inr (Or.inl rfl)) (by omega) (hu.sibAt 4 (by decide))
          · exact dig4 _ _ (Or.inr (Or.inr (Or.inr rfl))) (by omega) (hu.sibAt 5 (by decide))
        · simp only [sibs', if_neg e]; exact digAt_rdD _ _
      twAt := fun l _ => digAt_rdD _ _ }
  have hmid : Mid j B k index u' 4 (r.2.extractLsb' 0 128) s6 :=
    { pc := by rw [ho.pc]; unfold siteB; rw [Nat.add_assoc]
      keep := fun x h3 h10' h11' h12' => by
        rw [virt_getReg, g6 x (by simp), r1, hother x h3 h10' h11' h12']
      a1 := fun _ => by rw [g6 _ (by simp), r1]; exact h11
      a2 := by rw [g6 _ (by simp), r1, h12]
      node := by
        have e0 := ho.ans 0 (by decide); have e1 := ho.ans 1 (by decide)
        simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at e0 e1
        rw [← hoa]
        exact ⟨e0.trans (lowHalf r.2).1.symm, e1.trans (lowHalf r.2).2.symm⟩
      frame := fun A hA hn => by
        rw [hvd, virt_getMem j B u s6 hBl hj A hA, if_neg hn] }
  have HR := rest_tbsim (sk := sk) hj hbank hu' 1 4 _ s6 rfl hmid
  have HT := TBSim.bind HR (fun v5 s7 hs7 => TBSim.bind (W₂ := 0)
    (tail_tbsim (sk := sk) hj hbank hu' (by omega) v5 s7 hs7)
    (fun c t7 hp => TBSim.pure (α := Nat × Digest) (sk := sk) (image := im) (a := (r.1, c)) (s := t7)
      (Q := fun res t => res.1 = r.1 ∧ HandPost B j u' res.2 t) ⟨rfl, hp⟩))
  have e1 : ∀ v, (List.range' 4 1).foldlM (childLevelP k index j pads' (hpOf j tws') sibs') v =
      (List.range' 4 1).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v := fun v => by
    simp only [List.range', List.foldlM, childLevelP, hpOf, pads', sibs', show (4 = 4 ∨ 4 = 5) by decide, true_or, or_true, if_true,
      show ¬ (4 < 4) by decide, if_false]
  have e2 : ∀ v, childLevelTop k index j pads' (hpOf j tws') sibs' v = childLevelTop k index j pads (hpOf j tws) sibs v :=
    fun v => by
      simp only [childLevelTop, nodeIn, hpOf, pads', sibs', show (5 = 4 ∨ 5 = 5) by decide, true_or, or_true, if_true,
        show ¬ (5 < 4) by decide, if_false]
  simp only [e1, e2] at HT
  refine HT.mono (by omega) ?_
  rintro ⟨n0, c⟩ t7 ⟨hn0, hp⟩
  simp only at hn0
  subst hn0
  have hhO := handO_cases j
  have t7m : ∀ X, X < 2 ^ 64 → ¬ prefixWrites B X → ¬ (B - handO j ≤ X ∧ X < B - handO j + 32) →
      t7.getMem (BitVec.ofNat 64 X) = u'.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 =>
    hp.frame.get hX (by rintro (h | h) <;> contradiction)
  have u's : ∀ X, X < 2 ^ 64 → (X < B ∨ B + 1024 ≤ X) →
      u'.getMem (BitVec.ofNat 64 X) = s6.getMem (BitVec.ofNat 64 X) := fun X hX h => by
    rw [hvd, virt_getMem j B u s6 hBl hj X hX, if_neg]
    rintro ⟨off, hoff, rfl⟩
    have := stagesW_bound hj (by decide) hoff
    omega
  refine ⟨by rw [hp.pc, virt_getReg], hp.a1, hp.top, hp.a2, fun x h3 h10' h11' h12' => by
      rw [hp.keep x h3 h10' h11' h12', virt_getReg], ?_, ?_, ho.nle, ?_, ?_, ?_⟩
  · rw [t7m _ (by simp only [slotA, SCR]; omega) (by unfold prefixWrites slotA SCR; omega)
      (by simp only [slotA, SCR]; omega), u's _ (by simp only [slotA, SCR]; omega)
      (by simp only [slotA, SCR]; omega)]
    exact ho.slot0
  · rw [t7m _ (by simp only [slotA, SCR]; omega) (by unfold prefixWrites slotA SCR; omega)
      (by simp only [slotA, SCR]; omega), u's _ (by simp only [slotA, SCR]; omega)
      (by simp only [slotA, SCR]; omega)]
    exact ho.slot1
  · intro i hi
    rw [t7m _ (by omega) (by unfold prefixWrites; omega) (by omega), u's _ (by omega) (by omega)]
    exact ho.saves i hi
  · intro i hi
    rw [t7m _ (by simp only [SCR]; omega) (by unfold prefixWrites SCR; omega) (by simp only [SCR]; omega),
      u's _ (by simp only [SCR]; omega) (by simp only [SCR]; omega)]
    exact ho.scr i hi
  · intro X hX hn
    simp only [not_or] at hn
    rw [t7m _ hX hn.1 hn.2.1, hvd, virt_getMem j B u s6 hBl hj X hX]
    split_ifs with hw
    · rfl
    · exact hsw X hX hw (by unfold prefixWrites at hn; unfold padO at hp3 ⊢; omega) hn.2.2.2.2 hn.2.2.1
        hn.2.2.2.1

end main

/-! ## Y5 #1: level 2 (heap 16..31) through its trampoline -/

open SigGolfCandidate.FtsGrind (SEARCH16 search16Words Search16In Search16Out Plain16Out tramp_search16
  tramp_plain16 W_SEARCH16 W_PLAIN16 W16 groundFoldH slot16 SCR16 SEL16 Search16W)

/-- Level-2 ground trial halves: `pre = pair.1 ‖ header`, `right = pair.2`. -/
def pre2C (k index j : Nat) (tws sibs : Nat → Digest) (v : Digest) : List UInt8 :=
  bytesLE 16 (if bitAt j 2 = 0 then v else sibs 2) ++ bytesLE 16 (nodeHeader k index (heapOf 2 j) (hpOf j tws 2))
def right2C (j : Nat) (sibs : Nat → Digest) (v : Digest) : List UInt8 :=
  bytesLE 16 (if bitAt j 2 = 0 then sibs 2 else v)

/-- The level-2 fold of a copy routine: on a selected coordinate (`sel`) ground for one zero bit of the kept half,
else the plain hash (nonce 0). -/
def level2C (k index j : Nat) (sel : Bool) (pads tws sibs : Nat → Digest) (v : Digest) : M (Nat × HashOutput) :=
  if sel then groundFoldH (hiSel j 3) 1 (pre2C k index j tws sibs v) (right2C j sibs v)
  else (fun a => (0, a)) <$> SigGolfCandidate.T3.publicHash (nodeIn k index j pads (hpOf j tws) sibs v 2)

/-- The copy routine's program: the bank's `childProgram` with the level-2 fold `level2C` and the level-3 fold
ground for `b` zero bits; it also returns both nonces (level 3, level 2). -/
def childProgramC (k index j b : Nat) (sel : Bool) (leaf pads sibs tws : Nat → Digest) :
    M (Nat × Nat × Digest) := do
  let initial ← SharedV3.hashSel (hiSel j 0) (leafBytes leaf)
  let v2 ← (List.range 2).foldlM (childLevelP k index j pads (hpOf j tws) sibs) initial
  let r2 ← level2C k index j sel pads tws sibs v2
  let r ← groundFold b (preC k index j tws sibs (selD j 3 r2.2)) (rightC j sibs (selD j 3 r2.2))
  let v5 ← (List.range' 4 1).foldlM (childLevelP k index j pads (hpOf j tws) sibs) (r.2.extractLsb' 0 128)
  let computed ← childLevelTop k index j pads (hpOf j tws) sibs v5
  pure (r.1, r2.1, computed)

/-- Words the level-2 trampoline writes outside the routine's block area: its record, the saves, `SCR16`. -/
abbrev far16 (B A : Nat) : Prop :=
  (slot16 B ≤ A ∧ A < slot16 B + 16) ∨ (1104 ≤ A ∧ A < 1144) ∨ (SCR16 ≤ A ∧ A < SCR16 + 32)

/-- The virtual entry after level 2: `u` with the level-2 pad and the `far16` words of `s`. -/
def virt2 (j B : Nat) (u s : MachineState) : MachineState :=
  { u with mem := fun A => if A = BitVec.ofNat 64 (B + padO j 2) ∨ A = BitVec.ofNat 64 (B + padO j 2 + 8) ∨
      far16 B A.toNat then s.mem A else u.mem A }

theorem virt2_getMem (j B : Nat) (u s : MachineState) (A : Nat) (hA : A < 2 ^ 64) (hB : B + padO j 2 + 8 < 2 ^ 64) :
    (virt2 j B u s).getMem (BitVec.ofNat 64 A) =
      if A = B + padO j 2 ∨ A = B + padO j 2 + 8 ∨ far16 B A then s.getMem (BitVec.ofNat 64 A)
      else u.getMem (BitVec.ofNat 64 A) := by
  show (if _ then _ else _) = _
  have e1 : (BitVec.ofNat 64 A = BitVec.ofNat 64 (B + padO j 2)) ↔ A = B + padO j 2 := ofNat_inj hA (by omega)
  have e2 : (BitVec.ofNat 64 A = BitVec.ofNat 64 (B + padO j 2 + 8)) ↔ A = B + padO j 2 + 8 := ofNat_inj hA hB
  have e3 : (BitVec.ofNat 64 A).toNat = A := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hA
  simp only [e1, e2, e3]
  split_ifs <;> rfl

theorem highHalf (a : BitVec 256) :
    (a.extractLsb' 128 128).extractLsb' 0 64 = a.extractLsb' 128 64 ∧
      (a.extractLsb' 128 128).extractLsb' 64 64 = a.extractLsb' 192 64 := by
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.pow_zero,
      Nat.div_one] <;> omega

theorem digAt_sel3 {j : Nat} (hj : j < 128) {s : MachineState} {a : HashOutput} {B : Nat}
    (h : ∀ k < 4, s.getMem (BitVec.ofNat 64 (B + outO 3 j + 8 * k)) = a.extractLsb' (64 * k) 64) :
    DigAt s (B + curO 3 j) (selD j 3 a) := by
  unfold selD
  rcases Bool.eq_false_or_eq_true (hiSel j 3) with hh | hh
  · rw [if_pos hh, ← outO_hi hj (by decide) hh]
    have e2 := h 2 (by decide); have e3 := h 3 (by decide)
    rw [show B + outO 3 j + 8 * 2 = B + (outO 3 j + 16) by ring] at e2
    rw [show B + outO 3 j + 8 * 3 = B + (outO 3 j + 16) + 8 by ring] at e3
    exact ⟨e2.trans (highHalf a).1.symm, e3.trans (highHalf a).2.symm⟩
  · rw [if_neg (by rw [hh]; decide), ← outO_lo hh]
    have e0 := h 0 (by decide); have e1 := h 1 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at e0 e1
    exact ⟨e0.trans (lowHalf a).1.symm, e1.trans (lowHalf a).2.symm⟩

theorem and_one_zero (X : Nat) : (BitVec.ofNat 64 X &&& 1#64 = 0#64) ↔ X % 2 = 0 := by
  have key : (BitVec.ofNat 64 X &&& 1#64).toNat = X % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
    omega
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [key] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [key]
    simpa using h

theorem w0n_even (k index : Nat) : w0n k index % 2 = 0 := by
  unfold w0n V3.nodeLow
  rw [ClaudeWCT.WCT9.ftsLeafLow_zero]
  unfold SigGolfCandidate.T3.ftsBiasN
  omega

/-- After the level-2 trampoline: the routine at level 3 from the virtual entry `virt2`, the record. -/
structure L2Post (j B k index : Nat) (u : MachineState) (sel : Bool) (r : Nat × HashOutput) (s : MachineState) :
    Prop where
  mid : MidC j B k index (virt2 j B u s) 3 (selD j 3 r.2) s
  rec0 : sel = true → s.getMem (BitVec.ofNat 64 (slot16 B)) = BitVec.ofNat 64 (B + blkO j 2 + WADJ)
  rec1 : sel = true → s.getMem (BitVec.ofNat 64 (slot16 B + 8)) = BitVec.ofNat 64 r.1
  nle : r.1 ≤ 255
  n0 : sel = false → r.1 = 0
  scr : sel = true → ∀ i < 4, s.getMem (BitVec.ofNat 64 (SCR16 + 8 * i)) = 0

theorem virt2_frame {j B : Nat} (hj : j < 128) (hB : B < 2 ^ 14) {u s : MachineState}
    (hF : Frame u s (fun A => (∃ off ∈ stagesW j 4, A = B + off) ∨ A = B + padO j 2 ∨ A = B + padO j 2 + 8 ∨
      far16 B A)) :
    Frame (virt2 j B u s) s (fun A => ∃ off ∈ stagesW j 4, A = B + off) := by
  have hbl := blk_bounds j hj 2 (by decide)
  intro A hA hn
  rw [virt2_getMem j B u s A hA (by unfold padO; omega)]
  split_ifs with h
  · rfl
  · exact hF A hA (by rintro (h1 | h1); exact hn h1; exact h h1)

section level2
variable {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j)
  (hS16 : CodeAt im (pcOf SEARCH16) search16Words)
  (hT16 : CodeAt im (pcOf (tramp16Of j)) (trampWords (tramp16Of j) SEARCH16 (site16C j + 1)))
  {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
  (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 1848 ≤ B) (hB : B < 2 ^ 14)
include hj hcode hS16 hT16 hu hlo hB

/-- **Level 2 through the heap-16..31 trampoline**: ground on a selected coordinate, plain otherwise. -/
theorem lvl2C_tbsim (v : Digest) (s : MachineState) (hs : MidC j B k index u 2 v s) :
    TBSim im sk s (lvlSt j 2 + 1 + W16 (decide (SEL16 ≤ B)))
      (level2C k index j (decide (SEL16 ≤ B)) pads tws sibs v) (L2Post j B k index u (decide (SEL16 ≤ B))) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have h16 := site16_lt j hj
  have hsl := site_lt j hj
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, -, h5, h10, h11, h12', hpcT, hother, -, hin, hP, hpre1, hhdr, hright⟩ :=
    lvl_coreC hj hcode hu 2 (by decide) v s hs
  have hbl := blk_bounds j hj 2 (by decide)
  have hbl3 := blk_bounds j hj 3 (by decide)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + outO 3 j) := by
    rw [h12', lvlRegs_x12 j 2 (by decide)]
    by_cases hsk : skipA2 j 2 = true
    · rw [if_pos hsk, skipA2_out hsk]
      simp only [E.eval]
      exact hs.a2
    · rw [if_neg hsk, eX8_eval hx8]
  have hoa := outO_arith j 3 hj (by decide)
  have hcur : outO 3 j % 8 = 0 ∧ outO 3 j + 32 ≤ 864 := by have := curO_cases j 3; omega
  -- the level-2 site `jal`
  have hjal : CodeAt im (pcOf (site16C j))
      [SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (site16C j) (tramp16Of j))] := by
    refine codeAt_one ?_ (by unfold site16C copyBase cSlot SigGolfCandidate.FtsGrind.COPY_K8; omega)
    have hlt : ecIdx j 3 < ((childWords j).take (ecIdx j 4)).length := by
      rw [List.length_take]; have := ecIdx4_le j hj; omega
    have := hcode (ecIdx j 3)
      (SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (site16C j) (tramp16Of j))) (by
      unfold copyPre
      rw [List.getElem?_append_left (by rw [List.length_set]; exact hlt), List.getElem?_set_self hlt])
    simpa [site16C] using this
  have hjs := SigGolfCandidate.FtsGrind.jal_step (r := .x0) (by decide) rfl hjal
    (by unfold site16C copyBase cSlot SigGolfCandidate.FtsGrind.COPY_K8; omega)
    (by unfold tramp16Of cSlot SigGolfCandidate.FtsGrind.TRAMP16; omega) t (by rw [hpcT]; rfl)
  set t1 := ((t.setReg .x0 (pcOf (site16C j + 1))).setPC (pcOf (tramp16Of j))) with ht1
  have r1 : ∀ r, t1.getReg r = t.getReg r := fun r => by cases r <;> rfl
  have m1 : Frame t t1 (fun _ => False) := fun _ _ _ => rfl
  have hA : (B + blkO j 2) % 8 = 0 := by omega
  have hb16 : tramp16Of j + 5 < 2 ^ 18 := by unfold tramp16Of cSlot SigGolfCandidate.FtsGrind.TRAMP16; omega
  have hret16 : site16C j + 1 < 2 ^ 18 := by unfold site16C copyBase cSlot SigGolfCandidate.FtsGrind.COPY_K8; omega
  -- the frame from the entry to `t1`
  have fu1 : Frame u t1 (fun A => (∃ off ∈ stagesW j 4, A = B + off)) := ((hs.frame.trans hP).trans m1).mono
    (fun A _ h => by
      rcases h with (⟨off, hoff, rfl⟩ | (rfl | rfl)) | h
      · exact ⟨off, stagesW_mono hoff (by omega), rfl⟩
      · exact ⟨tw24 j 2, mem_stagesW (m := 2) (by omega) (by simp [stageW]), rfl⟩
      · exact ⟨blkO j 2 + 16, mem_stagesW (m := 2) (by omega) (by simp [stageW]), by omega⟩
      · exact h.elim)
  have Dw : ∀ X, (X = B + outO 3 j ∨ X = B + outO 3 j + 8 ∨ X = B + outO 3 j + 16 ∨ X = B + outO 3 j + 24) →
      ∃ off ∈ stagesW j 4, X = B + off := by
    rintro X (rfl | rfl | rfl | rfl)
    · exact ⟨outO 3 j, mem_stagesW (m := 3) (by omega) (by simp [stageW]), rfl⟩
    · exact ⟨outO 3 j + 8, mem_stagesW (m := 3) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨outO 3 j + 16, mem_stagesW (m := 3) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨outO 3 j + 24, mem_stagesW (m := 3) (by omega) (by simp [stageW]), by omega⟩
  have midOf : ∀ (a : HashOutput) (s6 : MachineState), s6.pc = pcOf (site16C j + 1) → RegsExcept t1 s6 [] →
      (∀ k < 4, s6.getMem (BitVec.ofNat 64 (B + outO 3 j + 8 * k)) = a.extractLsb' (64 * k) 64) →
      Frame u s6 (fun A => (∃ off ∈ stagesW j 4, A = B + off) ∨ A = B + padO j 2 ∨ A = B + padO j 2 + 8 ∨
        far16 B A) →
      MidC j B k index (virt2 j B u s6) 3 (selD j 3 a) s6 := by
    intro a s6 p6 r6 ans6 f6
    exact { pc := by rw [p6]; unfold site16C; rw [Nat.add_assoc]
            keep := fun x h3 h10' h11' h12' => by
              rw [r6.get (by simp), r1, hother x h3 h10' h11' h12']; rfl
            a1 := fun _ => by rw [r6.get (by simp), r1]; exact h11
            a2 := by rw [r6.get (by simp), r1, h12]
            node := digAt_sel3 hj ans6
            frame := virt2_frame hj hB f6 }
  by_cases hsel : SEL16 ≤ B
  · rw [show decide (SEL16 ≤ B) = true from decide_eq_true hsel]
    change TBSim im sk s _ (groundFoldH (hiSel j 3) 1 (pre2C k index j tws sibs v) (right2C j sibs v)) _
    have hpk := heapOf_packed j 2 hj (by decide)
    have F : Search16In (tramp16Of j) (site16C j + 1) (B + blkO j 2) (B + outO 3 j) B (hiSel j 3)
        (pre2C k index j tws sibs v) (right2C j sibs v) t1 :=
      { pc := rfl
        x5 := by rw [r1]; exact h5
        x8 := by rw [r1, hother .x8 (by decide) (by decide) (by decide) (by decide)]; exact hu.s0
        x10 := by rw [r1]; exact h10
        x11 := by rw [r1]; exact h11
        x12 := by rw [r1]; exact h12
        lpre := by simp [pre2C, bytesLE_length]
        lright := by simp [right2C, bytesLE_length]
        mpre := by
          rw [frame_readWordsG m1 _ 4 (by omega) (fun _ _ h => h), show (4 : Nat) = 2 + 2 from rfl, readWords_add,
            hpre1.words, show B + blkO j 2 + 8 * 2 = B + blkO j 2 + 16 by ring, hhdr.words, pre2C,
            wordsOf_append _ _ (by simp [bytesLE_length])]
        mright := by
          rw [frame_readWordsG m1 _ 2 (by omega) (fun _ _ h => h), hright.words, right2C]
        label := by
          rw [m1.get (by omega) (fun h => h), hhdr.1, hdr11_lo, if_pos hpk, and_one_zero]
          have := w0n_even k index
          rcases Bool.eq_false_or_eq_true (hiSel j 3) with hh | hh
          · rw [hh, if_pos rfl] at h16; simp only [hh, iff_true]; omega
          · rw [hh] at h16; simp only [hh, Bool.false_eq_true, if_false, iff_false] at h16 ⊢; omega
        hA := hA
        hA1 := by omega
        hA2 := by simp only [SigGolfCandidate.FtsGrind.SCR]; omega
        hD := by omega
        hD1 := by omega
        hD2 := by simp only [SigGolfCandidate.FtsGrind.SCR]; omega
        hS0 := h8
        hS1 := by omega
        hS2 := hB
        hb := hb16
        hret := hret16 }
    have HS := tramp_search16 (sk := sk) hS16 hT16 F hsel
    refine (TBSim.steps hst (TBSim.steps hjs (HS.mono le_rfl (fun r s6 ho => ?_)))).mono
      (by simp only [W16, if_true]; omega) (fun _ _ h => h)
    have f6 : Frame u s6 (fun A => (∃ off ∈ stagesW j 4, A = B + off) ∨ A = B + padO j 2 ∨ A = B + padO j 2 + 8 ∨
        far16 B A) := (fu1.trans ho.frame).mono (fun A _ h => by
      unfold Search16W at h
      rcases h with h | (h | h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inl (Dw A h)
      · exact Or.inr (Or.inl (by unfold padO; omega))
      · exact Or.inr (Or.inr (Or.inl (by unfold padO; omega)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    exact { mid := midOf r.2 s6 ho.pc ho.regs (fun k hk => ho.ans k hk) f6
            rec0 := fun _ => by rw [ho.slot0, Nat.add_assoc]
            rec1 := fun _ => ho.slot1
            nle := ho.nle
            n0 := fun h => absurd h (by decide)
            scr := fun _ => ho.scr }
  · rw [show decide (SEL16 ≤ B) = false from decide_eq_false hsel]
    change TBSim im sk s _ ((fun a => (0, a)) <$>
      SigGolfCandidate.T3.publicHash (nodeIn k index j pads (hpOf j tws) sibs v 2)) _
    rw [map_eq_bind_pure_comp]
    have hl : (nodeIn k index j pads (hpOf j tws) sibs v 2).length = 64 := by
      unfold nodeIn; exact blk4_length _ _ _ _
    have HP := tramp_plain16 (sk := sk) (s := t1) (inp := nodeIn k index j pads (hpOf j tws) sibs v 2) hS16 hT16 rfl
      (by rw [r1]; exact h5) (by rw [r1, hother .x8 (by decide) (by decide) (by decide) (by decide)]; exact hu.s0)
      (by omega) (by rw [r1]; exact h10) (by rw [r1]; exact h11) (by rw [r1]; exact h12) hl hin hA (by omega)
      (by omega) (by omega) (by omega) (by omega) hb16 hret16
    refine (TBSim.steps hst (TBSim.steps hjs (TBSim.bind (W₂ := 0) HP (fun a s6 ho => TBSim.pure ?_)))).mono
      (by simp only [W16, Bool.false_eq_true, if_false]; omega) (fun _ _ h => h)
    have f6 : Frame u s6 (fun A => (∃ off ∈ stagesW j 4, A = B + off) ∨ A = B + padO j 2 ∨ A = B + padO j 2 + 8 ∨
        far16 B A) := (fu1.trans ho.frame).mono (fun A _ h => by
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inl (Dw A h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    exact { mid := midOf a s6 ho.pc ho.regs (fun k hk => ho.ans k hk) f6
            rec0 := fun h => absurd h (by decide)
            rec1 := fun h => absurd h (by decide)
            nle := Nat.zero_le _
            n0 := fun _ => rfl
            scr := fun h => absurd h (by decide) }

end level2

/-- Back at the caller after a copy routine: `HandPostC` with the level-2 record and the widened frame. -/
structure HandPostC16 (B j : Nat) (u : MachineState) (sel : Bool) (res : Nat × Nat × Digest) (t : MachineState) :
    Prop where
  pc : t.pc = (u.getReg .x1 + 316) &&& ~~~1#64
  a1 : t.getReg .x11 = 64
  top : DigAt t (B - valO j) res.2.2
  a2 : t.getReg .x12 = BitVec.ofNat 64 (B - handO j)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r
  slot0 : t.getMem (BitVec.ofNat 64 (slotA B)) = BitVec.ofNat 64 (B + blkO j 3 + WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slotA B + 8)) = BitVec.ofNat 64 res.1
  nle : res.1 ≤ FUEL (widthOf B)
  rec0 : sel = true → t.getMem (BitVec.ofNat 64 (slot16 B)) = BitVec.ofNat 64 (B + blkO j 2 + WADJ)
  rec1 : sel = true → t.getMem (BitVec.ofNat 64 (slot16 B + 8)) = BitVec.ofNat 64 res.2.1
  nle16 : res.2.1 ≤ 255
  n0 : sel = false → res.2.1 = 0
  saves : ∀ i < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * i)) = 0
  scr : ∀ i < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * i)) = 0
  scr16 : sel = true → ∀ i < 4, t.getMem (BitVec.ofNat 64 (SCR16 + 8 * i)) = 0
  frame : Frame u t (fun A => prefixWrites B A ∨ (B - handO j ≤ A ∧ A < B - handO j + 32) ∨
    (slotA B ≤ A ∧ A < slotA B + 16) ∨ (1104 ≤ A ∧ A < 1144) ∨ (SCR ≤ A ∧ A < SCR + 32) ∨ far16 B A)

/-- **A copy routine refines `childProgramC`**: from the copy entry `x` (the bank entry state `u` at the copy pc). -/
theorem childC_tbsim {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j) (hbank : ChildCodeAt im j)
    (hS : CodeAt im (pcOf SEARCH) searchWords)
    (hT : CodeAt im (pcOf (trampOf j)) (trampWords (trampOf j) SEARCH (siteB j + 1)))
    (hS16 : CodeAt im (pcOf SEARCH16) search16Words)
    (hT16 : CodeAt im (pcOf (tramp16Of j)) (trampWords (tramp16Of j) SEARCH16 (site16C j + 1)))
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 1848 ≤ B) (hB : B < 2 ^ 14)
    {x : MachineState} (hxu : u = bankPc j x) (hpx : x.pc = pcOf (copyBase j + 1)) :
    TBSim im sk x (17 + (cycR j 0 2 + (lvlSt j 2 + 1 + W16 (decide (SEL16 ≤ B)) +
      (lvlSt j 3 + 1 + W_SEARCH (widthOf B) + (cycR j 4 1 + 13)))))
      (childProgramC k index j (widthOf B) (decide (SEL16 ≤ B)) leaf pads sibs tws)
      (HandPostC16 B j u (decide (SEL16 ≤ B))) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hbl2 := blk_bounds j hj 2 (by decide)
  have hp2 := (site16_lt j hj).2.1
  have hfresh := pad2_fresh j hj
  have hfar : ∀ X, B ≤ X → X < B + 1024 → ¬ far16 B X := fun X h1 h2 => by
    simp only [far16, slot16, SCR16]; omega
  have L3 : ∀ (r2 : Nat × HashOutput) (s6 : MachineState), L2Post j B k index u (decide (SEL16 ≤ B)) r2 s6 →
      TBSim im sk s6 (lvlSt j 3 + 1 + W_SEARCH (widthOf B) + (cycR j 4 1 + 13) + 0)
        ((groundFold (widthOf B) (preC k index j tws sibs (selD j 3 r2.2)) (rightC j sibs (selD j 3 r2.2)) >>=
          fun r => (List.range' 4 1).foldlM (childLevelP k index j pads (hpOf j tws) sibs) (r.2.extractLsb' 0 128) >>=
            fun v5 => childLevelTop k index j pads (hpOf j tws) sibs v5 >>= fun c =>
            pure (r.1, c)) >>= fun p => pure (p.1, r2.1, p.2))
        (HandPostC16 B j u (decide (SEL16 ≤ B))) := by
    intro r2 s6 h6
    set u2 := virt2 j B u s6 with hu2d
    have vu : ∀ o, o + 8 ≤ 1024 → away j o = true →
        u2.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
      intro o ho ha
      have := away_spec ha
      rw [hu2d, virt2_getMem j B u s6 _ (by omega) (by unfold padO; omega), if_neg]
      rintro (h | h | h)
      · omega
      · omega
      · exact hfar _ (by omega) (by omega) h
    have dv : ∀ o (d : Digest), o + 16 ≤ 1024 → away j o = true → away j (o + 8) = true → DigAt u (B + o) d →
        DigAt u2 (B + o) d := fun o d ho h1 h2 hd =>
      DigAt.of_eq hd (vu o (by omega) h1) (by rw [Nat.add_assoc]; exact vu (o + 8) (by omega) h2)
    let pads2 : Nat → Digest := fun l => if l = 2 then rdD u2 (B + padO j 2) else pads l
    have hu2 : ChildPre j B k index leaf pads2 sibs tws u2 :=
      { pc := hu.pc
        base8 := h8
        baseHi := hu.baseHi
        t0 := hu.t0
        s0 := hu.s0
        a0 := hu.a0
        a1 := hu.a1
        w0 := hu.w0
        heaps := hu.heaps
        leafAt := fun i hi => by
          have a1 := hfresh.2 (2 * i) (by omega)
          have a2 := hfresh.2 (2 * i + 1) (by omega)
          rw [show leafO + 8 * (2 * i) = leafO + 16 * i by ring] at a1
          rw [show leafO + 8 * (2 * i + 1) = leafO + 16 * i + 8 by ring] at a2
          have := dv (leafO + 16 * i) (leaf i) (by unfold leafO; omega) a1 a2
            (by rw [← Nat.add_assoc]; exact hu.leafAt i hi)
          rwa [← Nat.add_assoc] at this
        padAt := fun l hl => by
          by_cases e : l = 2
          · subst e; simp only [pads2, if_true]; exact digAt_rdD _ _
          · simp only [pads2, e, if_false]
            have hb := blk_bounds j hj l hl
            exact dv _ _ (by unfold padO; omega) ((hfresh.1 l hl).1 e).1 ((hfresh.1 l hl).1 e).2 (hu.padAt l hl)
        sibAt := fun l hl => by
          have hb := blk_bounds j hj l hl
          have := sibO_cases j l hl
          exact dv _ _ (by omega) (hfresh.1 l hl).2.1 (hfresh.1 l hl).2.2.1 (hu.sibAt l hl)
        twAt := fun l hl => by
          have hb := blk_bounds j hj l hl
          have := dv (blkO j l + 16) (tws l) (by omega) (hfresh.1 l hl).2.2.2.1
            (by rw [Nat.add_assoc]; exact (hfresh.1 l hl).2.2.2.2) (by rw [← Nat.add_assoc]; exact hu.twAt l hl)
          rwa [← Nat.add_assoc] at this }
    have HT := lvl3C_tbsim (sk := sk) hj hcode hbank hS hT hu2 hlo hB (selD j 3 r2.2) s6 h6.mid
    have e : ∀ c : Digest, childLevelTop k index j pads2 (hpOf j tws) sibs c =
        childLevelTop k index j pads (hpOf j tws) sibs c := fun c => by
      simp only [childLevelTop, nodeIn, pads2]
      rfl
    have e1 : ∀ v, (List.range' 4 1).foldlM (childLevelP k index j pads2 (hpOf j tws) sibs) v =
        (List.range' 4 1).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v := fun v => by
      simp only [List.range', List.foldlM, childLevelP, pads2]
      rfl
    simp only [e, e1] at HT
    refine TBSim.bind HT (fun p t hp => TBSim.pure ?_)
    -- `t` against `u`: through `u2`
    have tu2 : ∀ X, X < 2 ^ 64 → ¬ (prefixWrites B X ∨ (B - handO j ≤ X ∧ X < B - handO j + 32) ∨
        (slotA B ≤ X ∧ X < slotA B + 16) ∨ (1104 ≤ X ∧ X < 1144) ∨ (SCR ≤ X ∧ X < SCR + 32)) →
        t.getMem (BitVec.ofNat 64 X) = u2.getMem (BitVec.ofNat 64 X) := fun X hX h => hp.frame.get hX h
    have u2s : ∀ X, X < 2 ^ 64 → far16 B X → u2.getMem (BitVec.ofNat 64 X) = s6.getMem (BitVec.ofNat 64 X) :=
      fun X hX h => by rw [hu2d, virt2_getMem j B u s6 _ hX (by unfold padO; omega), if_pos (Or.inr (Or.inr h))]
    have nfar : ∀ X, far16 B X → (slot16 B ≤ X ∧ X < slot16 B + 16 ∨ SCR16 ≤ X ∧ X < SCR16 + 32) →
        ¬ (prefixWrites B X ∨ (B - handO j ≤ X ∧ X < B - handO j + 32) ∨
          (slotA B ≤ X ∧ X < slotA B + 16) ∨ (1104 ≤ X ∧ X < 1144) ∨ (SCR ≤ X ∧ X < SCR + 32)) := by
      intro X _ h
      have := handO_cases j
      unfold prefixWrites
      simp only [slotA, slot16, SCR, SCR16] at h ⊢
      omega
    have rd : ∀ X, X < 2 ^ 64 → (slot16 B ≤ X ∧ X < slot16 B + 16 ∨ SCR16 ≤ X ∧ X < SCR16 + 32) →
        t.getMem (BitVec.ofNat 64 X) = s6.getMem (BitVec.ofNat 64 X) := fun X hX h => by
      have hf : far16 B X := by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
      rw [tu2 X hX (nfar X hf h), u2s X hX hf]
    exact { pc := hp.pc
            a1 := hp.a1
            top := hp.top
            a2 := hp.a2
            keep := hp.keep
            slot0 := hp.slot0
            slot1 := hp.slot1
            nle := hp.nle
            rec0 := fun h => by
              rw [rd _ (by simp only [slot16, SCR16]; omega) (Or.inl (by omega))]; exact h6.rec0 h
            rec1 := fun h => by
              rw [rd _ (by simp only [slot16, SCR16]; omega) (Or.inl (by omega))]; exact h6.rec1 h
            nle16 := h6.nle
            n0 := h6.n0
            saves := hp.saves
            scr := hp.scr
            scr16 := fun h i hi => by
              rw [rd _ (by simp only [SCR16]; omega) (Or.inr (by omega))]; exact h6.scr h i hi
            frame := fun X hX hn => by
              have hn1 : ¬ prefixWrites B X := fun h => hn (Or.inl h)
              have hn6 : ¬ far16 B X := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
              rw [hp.frame.get hX (fun h => hn (by
                  rcases h with h | h | h | h | h
                  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
                    Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))])),
                hu2d, virt2_getMem j B u s6 _ hX (by unfold padO; omega), if_neg]
              rintro (h | h | h)
              · exact hn1 (by unfold prefixWrites; omega)
              · exact hn1 (by unfold prefixWrites; omega)
              · exact hn6 h }
  have H := TBSim.bind (leafC_tbsim (sk := sk) hj hcode hu hxu hpx) (fun v s hs =>
    TBSim.bind (restC_tbsim (sk := sk) hj hcode hu 2 0 v s rfl hs) (fun v2 s2 hs2 =>
      TBSim.bind (lvl2C_tbsim (sk := sk) hj hcode hS16 hT16 hu hlo hB v2 s2 hs2) (fun r2 s6 h6 => L3 r2 s6 h6)))
  rw [childProgramC, List.range_eq_range']
  simpa only [bind_assoc, pure_bind, Nat.add_zero] using H

end W9Drv.SharedCProof
