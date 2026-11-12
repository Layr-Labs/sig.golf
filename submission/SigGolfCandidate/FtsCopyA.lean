import SigGolfCandidate.FtsCopyAPieces
import SigGolfCandidate.FtsExpand16
set_option debug.skipKernelTC true
set_option linter.all false

/-! # FTS carrier grind: a first-coordinate (A) child routine through its expand copy refines `childProgramC`

The routine enters copy `j` at `copyBase j + 1` with the bank routine's entry state (`ChildPre`, read at the bank
pc). The copy computes the leaf and levels 0..2 exactly as the bank; at the level-3 fold it jumps to the
trampoline, which grinds the node with `tramp_search` and returns into the bank after the bank's level-3 `ecall`.
The bank finishes (level 4, the hand) with its proved `tail_tbsim`, run from a virtual entry state that agrees with
the real one except on the words the copy and the search wrote. -/

namespace W9Drv.SharedAProof
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

theorem lvl_coreG {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (l : Nat) (hl : l < 4) (v : Digest) (s : MachineState)
    (hpc0 : s.pc = pcOf (copyBase j + ecIdx j l + 1))
    (hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r)
    (ha1 : l ≠ 0 → s.getReg .x11 = BitVec.ofNat 64 64)
    (hnode0 : DigAt s (B + curO l j) v)
    (hsU : ∀ o, o ≤ 1024 → (o = padO j l ∨ o = padO j l + 8 ∨ o = sibO l j ∨ o = sibO l j + 8 ∨ o = blkO j l + 24) →
      s.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o))) :
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
      DigAt t (B + blkO j l + 48) (if bitAt j l = 0 then sibs l else v) ∧
      DigAt t (B + blkO j l + 32) (pads l) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hbl := blk_bounds j hj l (by omega)
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (copyBase j + (ecIdx j l + 1)) := by rw [hpc0, Nat.add_assoc]
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
    · exact ha1 h0
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h3 h10' h11' h12'
    rw [hreg, lvlRegs_other j l r h3 h10' h11' h12', RegFile.init_get_eval]
    exact hkeep r h3 h10' h11' h12'
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.t0
  have tS : ∀ o, o ≤ 1024 → o ≠ blkO j l + 16 → o ≠ blkO j l + 24 →
      t.getMem (BitVec.ofNat 64 (B + o)) = s.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho h16 h24
    rw [hmem _ (by omega), if_neg (fun h => h24 (by have := h.1; omega)), if_neg (by omega)]
  have hpad : DigAt t (B + blkO j l + 32) (pads l) := by
    have hP := hu.padAt l (by omega)
    unfold padO at hP
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), hsU _ (by omega) (Or.inl (by unfold padO; omega))]
    · rw [show B + (blkO j l + 32) + 8 = B + (blkO j l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        hsU _ (by omega) (Or.inr (Or.inl (by unfold padO; omega)))]
  have hcs := sibO_cases j l (by omega)
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l (by omega)
    have hsb : sibO l j = blkO j l ∨ sibO l j = blkO j l + 48 := by omega
    refine DigAt.of_eq hS ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), hsU _ (by omega) (Or.inr (Or.inr (Or.inl rfl)))]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega), hsU _ (by omega) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
  have hnode : DigAt t (B + curO l j) v := by
    have hcb := curO_cases j l
    refine DigAt.of_eq hnode0 ?_ ?_
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
          hsU _ (by omega) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
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
        have hs64 : s.getReg .x11 = BitVec.ofNat 64 64 := ha1 (by omega)
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
    hpair.1, hhdr, hpair.2, hpad⟩
  intro A hA hn
  simp only [not_or] at hn
  rw [hmem A hA, if_neg ?_, if_neg hn.2]
  rintro ⟨h24, hc⟩
  apply hn.1
  unfold tw24
  rw [if_neg hc]
  exact h24

/-! ## q098 helpers (lvl2C / lvl3C from `Mid2C`) -/

theorem blk4_parts (a b c d : Digest) :
    (blk4 a b c d).take 32 = bytesLE 16 a ++ bytesLE 16 b ∧
      ((blk4 a b c d).drop 32).take 16 = bytesLE 16 c ∧ (blk4 a b c d).drop 48 = bytesLE 16 d := by
  unfold blk4
  refine ⟨?_, ?_, ?_⟩ <;> simp [List.take_append, List.drop_append, bytesLE_length, List.drop_eq_nil_of_le]

theorem nodeIn_parts (k index j : Nat) (pads : Nat → Digest) (hps : Nat → BitVec 64) (sibs : Nat → Digest)
    (v : Digest) (l : Nat) :
    (nodeIn k index j pads hps sibs v l).take 32 =
        bytesLE 16 (if bitAt j l = 0 then v else sibs l) ++ bytesLE 16 (nodeHeader k index (heapOf l j) (hps l)) ∧
      ((nodeIn k index j pads hps sibs v l).drop 32).take 16 = bytesLE 16 (pads l) ∧
      (nodeIn k index j pads hps sibs v l).drop 48 = bytesLE 16 (if bitAt j l = 0 then sibs l else v) := by
  unfold nodeIn
  by_cases h : bitAt j l = 0
  · simp only [h, if_true]; exact blk4_parts _ _ _ _
  · simp only [h, if_false]; exact blk4_parts _ _ _ _

theorem lowHalf2 (a : BitVec 256) :
    (a.extractLsb' 0 128).extractLsb' 0 64 = a.extractLsb' 0 64 ∧
      (a.extractLsb' 0 128).extractLsb' 64 64 = a.extractLsb' 64 64 := by
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero] <;> omega

theorem codeAt_oneG {im : Image} {n : Nat} {w : BitVec 32} (h : im.code[n]? = some w) (hn : n < 2 ^ 60) :
    CodeAt im (pcOf n) [w] := by
  have hp : (pcOf n).toNat = 0x1000 + 4 * n := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, by omega, by simp; omega, ?_⟩
  rw [hp, show (0x1000 + 4 * n - 0x1000) / 4 = n by omega]
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hl, he]
  exact ⟨_, rfl⟩

/-- The kept half of a 32-byte answer already in memory at `B + outO m j`. -/
theorem DigAt_selD_mem (t : MachineState) (a : BitVec 256) {j m B : Nat} (hj : j < 128) (hm : m < 6)
    (e0 : t.getMem (BitVec.ofNat 64 (B + outO m j)) = a.extractLsb' 0 64)
    (e1 : t.getMem (BitVec.ofNat 64 (B + outO m j + 8)) = a.extractLsb' 64 64)
    (e2 : t.getMem (BitVec.ofNat 64 (B + outO m j + 16)) = a.extractLsb' 128 64)
    (e3 : t.getMem (BitVec.ofNat 64 (B + outO m j + 24)) = a.extractLsb' 192 64) :
    DigAt t (B + curO m j) (selD j m a) := by
  unfold selD
  rcases Bool.eq_false_or_eq_true (hiSel j m) with h | h
  · rw [if_pos h, ← outO_hi hj hm h, ← Nat.add_assoc]
    constructor
    · rw [e2]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; omega
    · rw [show B + outO m j + 16 + 8 = B + outO m j + 24 by omega, e3]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; omega
  · rw [if_neg (by rw [h]; decide), ← outO_lo h]
    exact ⟨e0.trans (lowHalf2 a).1.symm, e1.trans (lowHalf2 a).2.symm⟩

/-! ## S5185 (FTS16, TIER2 E13): level 2 through its trampoline -/

/-- After level 2 through `tramp2Of j` (`TIER2 E13`): `MidC` at level 3 with the record and the frame widened by the
level-2 pad, the level-2 record and the search scratch. `res = (nonce, level-3 value)`. -/
structure Mid2C (j B k index : Nat) (u : MachineState) (res : Nat × Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (copyBase j + ecIdx j 3 + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  a1 : s.getReg .x11 = BitVec.ofNat 64 64
  a2 : s.getReg .x12 = BitVec.ofNat 64 (B + outO 3 j)
  node : DigAt s (B + curO 3 j) res.2
  nle : res.1 ≤ SigGolfCandidate.FtsGrind.FUEL 1
  rec0 : 3400 ≤ B → s.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 B)) =
    BitVec.ofNat 64 (B + blkO j 2 + SigGolfCandidate.FtsGrind.WADJ)
  rec1 : 3400 ≤ B → s.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 B + 8)) = BitVec.ofNat 64 res.1
  /-- TIER2B D1: coordinate 8 (`B < 3400`): plain level 2, nonce 0, the level-2 record words untouched. -/
  plain2 : B < 3400 → res.1 = 0 ∧ ∀ o < 16, s.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 B + o)) =
    u.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 B + o))
  frame : Frame u s (fun A => (∃ off ∈ stagesW j 4, A = B + off) ∨ A = B + padO j 2 ∨ A = B + padO j 2 + 8 ∨
    (SigGolfCandidate.FtsGrind.slot2 B ≤ A ∧ A < SigGolfCandidate.FtsGrind.slot2 B + 16) ∨
    (1104 ≤ A ∧ A < 1144) ∨ (SigGolfCandidate.FtsGrind.SCR ≤ A ∧ A < SigGolfCandidate.FtsGrind.SCR + 32))

/-- **Level 2 through the level-2 trampoline** (`TIER2 E13`, the level-2 twin of `lvl3C_tbsim`'s head): the level-2
block (`nodeIn .. 2`, split 32 / 16 / 16) goes through `node2 (hiSel j 3) B`, whose kept half is the level-3 value. -/
theorem lvl2C_tbsim {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j)
    (hS2 : CodeAt im (pcOf (SigGolfCandidate.FtsGrind.s2Base (hiSel j 3)))
      (SigGolfCandidate.FtsGrind.search2Words (hiSel j 3)))
    (hT2 : CodeAt im (pcOf (tramp2Of j))
      (SigGolfCandidate.FtsGrind.trampWords (tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (hiSel j 3)) (site2C j + 1)))
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 1848 ≤ B) (hB : B < 2 ^ 14) (v : Digest) (s : MachineState)
    (hs : MidC j B k index u 2 v s) :
    TBSim im sk s (lvlSt j 2 + 1 + SigGolfCandidate.FtsGrind.W_SEARCH2)
      (SigGolfCandidate.FtsGrind.node2 (hiSel j 3) B ((nodeIn k index j pads (hpOf j tws) sibs v 2).take 32)
          (((nodeIn k index j pads (hpOf j tws) sibs v 2).drop 32).take 16)
          ((nodeIn k index j pads (hpOf j tws) sibs v 2).drop 48) >>= fun r => pure (r.1, selD j 3 r.2))
      (Mid2C j B k index u) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hsl := site_lt j hj
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hsU : ∀ o, o ≤ 1024 → (o = padO j 2 ∨ o = padO j 2 + 8 ∨ o = sibO 2 j ∨ o = sibO 2 j + 8 ∨ o = blkO j 2 + 24) →
      s.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho hd
    refine hs.frame (B + o) (by omega) ?_
    rintro ⟨off, hoff, he⟩
    have e : off = o := by omega
    subst e
    have hf := stagesW_free (off := off) hj (by omega) hoff
    rcases hd with rfl | rfl | rfl | rfl | rfl
    exacts [hf.1 rfl, hf.2.1 rfl, hf.2.2.1 rfl, hf.2.2.2 rfl, tw_free hj (by omega) hoff rfl]
  obtain ⟨t, hst, -, h5, h10, h11, h12', hpcT, hother, -, -, hP, hpre1, hhdr, hright, hpadt⟩ :=
    lvl_coreG hj hcode hu 2 (by decide) v s hs.pc hkeep hs.a1 hs.node hsU
  have hbl := blk_bounds j hj 2 (by decide)
  have hbl3 := blk_bounds j hj 3 (by decide)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + outO (2 + 1) j) := by
    rw [h12', lvlRegs_x12 j 2 (by decide)]
    by_cases hsk : skipA2 j 2 = true
    · have hso : outO (2 + 1) j = outO 2 j := skipA2_out hsk
      rw [if_pos hsk, hso]
      simp only [E.eval]
      exact hs.a2
    · rw [if_neg hsk, eX8_eval hx8]
  have hoa := outO_arith j 3 hj (by decide)
  have hcur : outO 3 j % 8 = 0 ∧ outO 3 j + 32 ≤ 864 := by
    have := curO_cases j 3; omega
  have hlt3 : ecIdx j 3 < ecIdx j 4 := by
    have e : ecIdx j 4 = ecIdx j 3 + lvlLen j 3 + (if (3 : Nat) = 0 then 1 else 0) := rfl
    have h4 : 4 ≤ lvlLen j 3 := by unfold lvlLen; split <;> omega
    rw [if_neg (by decide)] at e
    omega
  have hjal : CodeAt im (pcOf (site2C j))
      [SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (site2C j) (tramp2Of j))] := by
    refine codeAt_oneG ?_ (by unfold site2C copyBase cSlot SigGolfCandidate.FtsGrind.COPY_FIRST; omega)
    have hlen : ((childWords j).take (ecIdx j 4)).length = ecIdx j 4 := by
      rw [List.length_take]; have := ecIdx4_le j hj; omega
    have := hcode (ecIdx j 3)
      (SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (site2C j) (tramp2Of j))) (by
        unfold copyPre
        rw [List.getElem?_append_left (by rw [List.length_set, hlen]; omega),
          List.getElem?_set_self (by rw [hlen]; omega)])
    simpa [site2C] using this
  have hjs := SigGolfCandidate.FtsGrind.jal_step (r := .x0) (by decide) rfl hjal
    (by unfold site2C copyBase cSlot SigGolfCandidate.FtsGrind.COPY_FIRST; omega)
    (by unfold tramp2Of cSlot SigGolfCandidate.FtsGrind.TRAMP2; omega) t (by rw [hpcT]; rfl)
  set t1 := ((t.setReg .x0 (pcOf (site2C j + 1))).setPC (pcOf (tramp2Of j))) with ht1
  have r1 : ∀ r, t1.getReg r = t.getReg r := fun r => by cases r <;> rfl
  have m1 : Frame t t1 (fun _ => False) := fun _ _ _ => rfl
  have hA : (B + blkO j 2) % 8 = 0 := by omega
  obtain ⟨hp32, hpmid, hpright⟩ := nodeIn_parts k index j pads (hpOf j tws) sibs v 2
  have F : SigGolfCandidate.FtsGrind.Search2In (tramp2Of j) (site2C j + 1) (B + blkO j 2) (B + outO 3 j) B
      ((nodeIn k index j pads (hpOf j tws) sibs v 2).take 32)
      (((nodeIn k index j pads (hpOf j tws) sibs v 2).drop 32).take 16)
      ((nodeIn k index j pads (hpOf j tws) sibs v 2).drop 48) t1 :=
    { pc := rfl
      x5 := by rw [r1]; exact h5
      x8 := by rw [r1, hother .x8 (by decide) (by decide) (by decide) (by decide)]; exact hu.s0
      x10 := by rw [r1]; exact h10
      x11 := by rw [r1]; exact h11
      x12 := by rw [r1]; exact h12
      lpre := by rw [hp32]; simp [bytesLE_length]
      lmid := by rw [hpmid]; simp [bytesLE_length]
      lright := by rw [hpright]; simp [bytesLE_length]
      mpre := by
        rw [hp32, frame_readWordsG m1 _ 4 (by omega) (fun _ _ h => h), show (4 : Nat) = 2 + 2 from rfl, readWords_add,
          hpre1.words, show B + blkO j 2 + 8 * 2 = B + blkO j 2 + 16 by ring, hhdr.words,
          wordsOf_append _ _ (by simp [bytesLE_length])]
      mmid := by
        rw [hpmid, frame_readWordsG m1 _ 2 (by omega) (fun _ _ h => h), hpadt.words]
      mright := by
        rw [hpright, frame_readWordsG m1 _ 2 (by omega) (fun _ _ h => h), hright.words]
      hA := hA
      hA1 := by omega
      hA2 := by simp only [SigGolfCandidate.FtsGrind.SCR]; omega
      hD := by omega
      hD1 := by omega
      hD2 := by simp only [SigGolfCandidate.FtsGrind.SCR]; omega
      hS0 := h8
      hS1 := by omega
      hS2 := hB
      hb := by unfold tramp2Of cSlot SigGolfCandidate.FtsGrind.TRAMP2; omega
      hret := by unfold site2C copyBase cSlot SigGolfCandidate.FtsGrind.COPY_FIRST; omega }
  have HS := SigGolfCandidate.FtsGrind.tramp_search2 (sk := sk) hS2 hT2 F
  refine (TBSim.steps hst (TBSim.steps hjs (TBSim.bind (W₂ := 0) HS (fun r s6 ho => TBSim.pure ?_)))).mono
    (by omega) (fun _ _ h => h)
  have g6 : ∀ x, x ∉ ([] : List Reg) → s6.getReg x = t1.getReg x := ho.regs
  have hstg : ∀ o ∈ stageW j 3, o ∈ stagesW j 4 := fun o ho' => mem_stagesW (m := 3) (by omega) ho'
  refine ⟨?_, ?_, ?_, ?_, ?_, ho.nle, ho.rec0, ho.rec1, ?_, ?_⟩
  · exact ho.pc
  · intro x h3 h10' h11' h12'
    rw [g6 x (by simp), r1, hother x h3 h10' h11' h12']
  · rw [g6 _ (by simp), r1]; exact h11
  · rw [g6 _ (by simp), r1]; exact h12
  · have e0 : s6.getMem (BitVec.ofNat 64 (B + outO 3 j)) = r.2.extractLsb' 0 64 := ho.ans 0 (by decide)
    have e1 : s6.getMem (BitVec.ofNat 64 (B + outO 3 j + 8)) = r.2.extractLsb' 64 64 := ho.ans 1 (by decide)
    have e2 : s6.getMem (BitVec.ofNat 64 (B + outO 3 j + 16)) = r.2.extractLsb' 128 64 := ho.ans 2 (by decide)
    have e3 : s6.getMem (BitVec.ofNat 64 (B + outO 3 j + 24)) = r.2.extractLsb' 192 64 := ho.ans 3 (by decide)
    exact DigAt_selD_mem s6 r.2 hj (by decide) e0 e1 e2 e3
  · intro hB3
    refine ⟨(ho.plain hB3).1, fun o ho' => ?_⟩
    have hn : ¬ (∃ off ∈ stagesW j 3, SigGolfCandidate.FtsGrind.slot2 B + o = B + off) := by
      rintro ⟨off, hoff, he⟩
      have := stagesW_bound hj (by decide) hoff
      simp only [SigGolfCandidate.FtsGrind.slot2, SigGolfCandidate.FtsGrind.slotA, SigGolfCandidate.FtsGrind.SCR] at he
      omega
    rw [(ho.plain hB3).2.get (by simp only [SigGolfCandidate.FtsGrind.slot2, SigGolfCandidate.FtsGrind.slotA,
        SigGolfCandidate.FtsGrind.SCR]; omega) (by simp only [SigGolfCandidate.FtsGrind.slot2,
        SigGolfCandidate.FtsGrind.slotA, SigGolfCandidate.FtsGrind.SCR]; omega), m1.get (by simp only [SigGolfCandidate.FtsGrind.slot2, SigGolfCandidate.FtsGrind.slotA, SigGolfCandidate.FtsGrind.SCR]; omega) (fun h => h),
      hP.get (by simp only [SigGolfCandidate.FtsGrind.slot2, SigGolfCandidate.FtsGrind.slotA,
        SigGolfCandidate.FtsGrind.SCR]; omega) (by
        simp only [SigGolfCandidate.FtsGrind.slot2, SigGolfCandidate.FtsGrind.slotA, SigGolfCandidate.FtsGrind.SCR]
        unfold tw24; split_ifs <;> omega)]
    exact hs.frame.get (by simp only [SigGolfCandidate.FtsGrind.slot2, SigGolfCandidate.FtsGrind.slotA,
      SigGolfCandidate.FtsGrind.SCR]; omega) hn
  · intro A hA hn
    have hn' : ¬ (∃ off ∈ stagesW j 3, A = B + off) := fun ⟨off, hoff, he⟩ =>
      hn (Or.inl ⟨off, stagesW_mono hoff (by omega), he⟩)
    have e6 := ho.frame.get hA (by
      unfold SigGolfCandidate.FtsGrind.SearchW2
      rintro (h | h | h | h | h | h)
      · rcases h with h | h | h | h
        · exact hn (Or.inl ⟨outO 3 j, hstg _ (by simp [stageW]), h⟩)
        · exact hn (Or.inl ⟨outO 3 j + 8, hstg _ (by simp [stageW]), by omega⟩)
        · exact hn (Or.inl ⟨outO 3 j + 16, hstg _ (by simp [stageW]), by omega⟩)
        · exact hn (Or.inl ⟨outO 3 j + 24, hstg _ (by simp [stageW]), by omega⟩)
      · exact hn (Or.inr (Or.inl (by unfold padO; omega)))
      · exact hn (Or.inr (Or.inr (Or.inl (by unfold padO; omega))))
      · exact hn (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    rw [e6, m1.get hA (fun h => h), hP.get hA (by
      rintro (h | h)
      · exact hn (Or.inl ⟨tw24 j 2, mem_stagesW (m := 2) (by omega) (by simp [stageW]), h⟩)
      · exact hn (Or.inl ⟨blkO j 2 + 16, mem_stagesW (m := 2) (by omega) (by simp [stageW]), by omega⟩))]
    exact hs.frame.get hA hn'

/-! ## Level 3 through the trampoline, then the bank's tail -/

/-- Level-3 ground trial halves: `pre = pair.1 ‖ header`, `right = pair.2`. -/
def preC (k index j : Nat) (tws sibs : Nat → Digest) (v : Digest) : List UInt8 :=
  bytesLE 16 (if bitAt j 3 = 0 then v else sibs 3) ++ bytesLE 16 (nodeHeader k index (heapOf 3 j) (hpOf j tws 3))
def rightC (j : Nat) (sibs : Nat → Digest) (v : Digest) : List UInt8 :=
  bytesLE 16 (if bitAt j 3 = 0 then sibs 3 else v)

/-- The copy routine's program: the bank's `childProgram` with the level-3 fold ground for `b` zero bits and (S5185
FTS16, TIER2B D1) the level-2 node `node2` of frame base `B`; it returns the packed nonce `2^64 n2 + n3` (NONCE2). -/
def childProgramC (k index j b B : Nat) (leaf pads sibs tws : Nat → Digest) : M (Nat × Digest) := do
  let initial ← SharedV3.hashSel (hiSel j 0) (leafBytes leaf)
  let v2 ← (List.range 2).foldlM (childLevelP k index j pads (hpOf j tws) sibs) initial
  -- S5185 (FTS16, TIER2B D1): level 2 through `tramp2Of j`: `node2` (ground iff `3400 <= B`), kept half `hiSel j 3`.
  let r2 ← SigGolfCandidate.FtsGrind.node2 (hiSel j 3) B ((nodeIn k index j pads (hpOf j tws) sibs v2 2).take 32)
    (((nodeIn k index j pads (hpOf j tws) sibs v2 2).drop 32).take 16)
    ((nodeIn k index j pads (hpOf j tws) sibs v2 2).drop 48)
  let v3 := selD j 3 r2.2
  let r ← groundFold b (preC k index j tws sibs v3) (rightC j sibs v3)
  let computed ← childLevelHi k index j pads (hpOf j tws) sibs (r.2.extractLsb' 0 128)
  pure (2 ^ 64 * r2.1 + r.1, computed)

/-- Back at the caller (`ra + 300`) after a copy routine: the bank's `HandPost`, plus the nonce record and the
re-zeroed search scratch; the frame adds the record, the saves and `SCR`. -/
structure HandPostC (B j : Nat) (u : MachineState) (res : Nat × Digest) (t : MachineState) : Prop where
  pc : t.pc = (u.getReg .x1 + 300) &&& ~~~1#64
  a1 : t.getReg .x11 = 64
  top : DigAt t (B - handO j + 16) res.2
  a2 : t.getReg .x12 = BitVec.ofNat 64 (B - handO j)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r
  slot0 : t.getMem (BitVec.ofNat 64 (slotA B)) = BitVec.ofNat 64 (B + blkO j 3 + WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slotA B + 8)) = BitVec.ofNat 64 res.1
  /-- S5185 (FTS16, TIER2B D1): `res.1 = 2^64 n2 + n3` (NONCE2 packing). -/
  nle : res.1 % 2 ^ 64 ≤ FUEL (widthOf B) ∧ res.1 / 2 ^ 64 ≤ FUEL 1
  rec2a : 3400 ≤ B → t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 B)) = BitVec.ofNat 64 (B + blkO j 2 + WADJ)
  rec2b : 3400 ≤ B → t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 B + 8)) = BitVec.ofNat 64 (res.1 / 2 ^ 64)
  plain2 : B < 3400 → res.1 / 2 ^ 64 = 0
  saves : ∀ i < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * i)) = 0
  scr : ∀ i < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * i)) = 0
  frame : Frame u t (fun A => prefixWrites B A ∨ (B - handO j ≤ A ∧ A < B - handO j + 32) ∨
    (slotA B ≤ A ∧ A < slotA B + 16 ∨ 3400 ≤ B ∧ slotA B + 16 ≤ A ∧ A < slotA B + 32) ∨ (1104 ≤ A ∧ A < 1144) ∨
    (SCR ≤ A ∧ A < SCR + 32))

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

/-- (S4 layout facts) the level-2 pad words (`padO j 2`) are disjoint from the level-3/4 pad, sibling and tweak words,
and lie inside the 784-byte prefix.  Kernel check over all 128 `j`. -/
theorem pad2_far : ∀ j < 128,
    (padO j 3 + 16 ≤ padO j 2 ∨ padO j 2 + 16 ≤ padO j 3) ∧
    (sibO 3 j + 16 ≤ padO j 2 ∨ padO j 2 + 16 ≤ sibO 3 j) ∧
    (padO j 4 + 16 ≤ padO j 2 ∨ padO j 2 + 16 ≤ padO j 4) ∧
    (sibO 4 j + 16 ≤ padO j 2 ∨ padO j 2 + 16 ≤ sibO 4 j) ∧
    (blkO j 3 + 24 + 8 ≤ padO j 2 ∨ padO j 2 + 16 ≤ blkO j 3 + 24) ∧ padO j 2 + 16 ≤ 784 := by
  decide +kernel

section main
variable {im : Image} {j : Nat} (hj : j < 128) (hcode : CopyCodeAt im j) (hbank : ChildCodeAt im j)
  (hS : CodeAt im (pcOf SEARCH) searchWords)
  (hT : CodeAt im (pcOf (trampOf j)) (trampWords (trampOf j) SEARCH (siteB j + 1)))
  {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
  (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 1848 ≤ B) (hB : B < 2 ^ 14)
include hj hcode hbank hS hT hu hlo hB

/-- Level 3 (the ground fold through the trampoline) and the bank's tail, after level 2 (`Mid2C`, TIER2B D1). -/
theorem lvl3C_tbsim (r2 : Nat × Digest) (s : MachineState) (hs : Mid2C j B k index u r2 s) :
    TBSim im sk s (lvlSt j 3 + 1 + W_SEARCH (widthOf B) + 13)
      (groundFold (widthOf B) (preC k index j tws sibs r2.2) (rightC j sibs r2.2) >>= fun r =>
        childLevelHi k index j pads (hpOf j tws) sibs (r.2.extractLsb' 0 128) >>= fun c => pure (2 ^ 64 * r2.1 + r.1, c))
      (HandPostC B j u) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hsl := site_lt j hj
  have hfar2 := pad2_far j hj
  set v : Digest := r2.2 with hvdef
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hsU : ∀ o, o ≤ 1024 → (o = padO j 3 ∨ o = padO j 3 + 8 ∨ o = sibO 3 j ∨ o = sibO 3 j + 8 ∨ o = blkO j 3 + 24) →
      s.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho hd
    refine hs.frame (B + o) (by omega) ?_
    rintro (⟨off, hoff, he⟩ | h | h | h | h | h)
    · have e : off = o := by omega
      subst e
      have hf := stagesW_free (off := off) hj (by omega) hoff
      rcases hd with rfl | rfl | rfl | rfl | rfl
      exacts [hf.1 rfl, hf.2.1 rfl, hf.2.2.1 rfl, hf.2.2.2 rfl, tw_free hj (by omega) hoff rfl]
    · omega
    · omega
    · simp only [SigGolfCandidate.FtsGrind.slot2, SigGolfCandidate.FtsGrind.slotA, SigGolfCandidate.FtsGrind.SCR] at h
      omega
    · omega
    · simp only [SigGolfCandidate.FtsGrind.SCR] at h
      omega
  obtain ⟨t, hst, -, h5, h10, h11, h12', hpcT, hother, -, -, hP, hpre1, hhdr, hright, -⟩ :=
    lvl_coreG hj hcode hu 3 (by decide) v s hs.pc hkeep (fun _ => hs.a1) hs.node hsU
  have hbl := blk_bounds j hj 3 (by decide)
  have hbl2 := blk_bounds j hj 2 (by decide)
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
    refine codeAt_oneG ?_ (by unfold siteC copyBase cSlot SigGolfCandidate.FtsGrind.COPY_FIRST; omega)
    have hlen : ((childWords j).take (ecIdx j 4)).length = ecIdx j 4 := by
      rw [List.length_take]; have := ecIdx4_le j hj; omega
    have := hcode (ecIdx j 4)
      (SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (siteC j) (trampOf j))) (by
      unfold copyPre; rw [List.getElem?_append_right (by simp only [List.length_set]; omega)]
      simp only [List.length_set, hlen, Nat.sub_self]; simp)
    simpa [siteC] using this
  have hjs := SigGolfCandidate.FtsGrind.jal_step (r := .x0) (by decide) rfl hjal
    (by unfold siteC copyBase cSlot SigGolfCandidate.FtsGrind.COPY_FIRST; omega)
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
      hret := by unfold siteB childBase tableBase; omega }
  have HS := tramp_search (sk := sk) hS hT F
  refine (TBSim.steps hst (TBSim.steps hjs (TBSim.bind (W₂ := 13 + 0) HS (fun r s6 ho => ?_)))).mono (by omega) (fun _ _ h => h)
  -- the virtual bank entry and the bank's tail
  have hBl : B + 1024 < 2 ^ 64 := by omega
  set u' := virt j B u s6 with hvd
  have g6 : ∀ x, x ∉ ([] : List Reg) → s6.getReg x = t1.getReg x := ho.regs
  have hs6s : ∀ X, X < 2 ^ 64 → ¬ (∃ off ∈ stagesW j 5, X = B + off) →
      ¬ (X = B + padO j 3 ∨ X = B + padO j 3 + 8) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA B ≤ X ∧ X < slotA B + 16) → ¬ (1104 ≤ X ∧ X < 1144) →
      s6.getMem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
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
  have hsw : ∀ X, X < 2 ^ 64 → ¬ (∃ off ∈ stagesW j 5, X = B + off) →
      ¬ (X = B + padO j 3 ∨ X = B + padO j 3 + 8) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA B ≤ X ∧ X < slotA B + 16) → ¬ (1104 ≤ X ∧ X < 1144) →
      ¬ (X = B + padO j 2 ∨ X = B + padO j 2 + 8) → ¬ (SigGolfCandidate.FtsGrind.slot2 B ≤ X ∧
        X < SigGolfCandidate.FtsGrind.slot2 B + 16) →
      s6.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := by
    intro X hX h1 h2 h3 h4 h5' h6 h7
    rw [hs6s X hX h1 h2 h3 h4 h5']
    exact hs.frame.get hX (by
      rintro (⟨off, hoff, he⟩ | h | h | h | h | h)
      · exact h1 ⟨off, stagesW_mono hoff (by omega), he⟩
      · exact h6 (Or.inl h)
      · exact h6 (Or.inr h)
      · exact h7 h
      · exact h5' h
      · exact h3 h)
  have hvu : ∀ X, X < 2 ^ 64 → ¬ (X = B + padO j 3 ∨ X = B + padO j 3 + 8) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA B ≤ X ∧ X < slotA B + 16) → ¬ (1104 ≤ X ∧ X < 1144) →
      ¬ (X = B + padO j 2 ∨ X = B + padO j 2 + 8) → ¬ (SigGolfCandidate.FtsGrind.slot2 B ≤ X ∧
        X < SigGolfCandidate.FtsGrind.slot2 B + 16) →
      u'.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := by
    intro X hX h2 h3 h4 h5' h6 h7
    rw [hvd, virt_getMem j B u s6 hBl hj X hX]
    split_ifs with hw
    · rfl
    · exact hsw X hX hw h2 h3 h4 h5' h6 h7
  have hp3 := pad3_prefix j hj
  have hbl0 : padO j 4 % 16 = 0 ∧ sibO 4 j % 16 = 0 ∧ padO j 3 % 16 = 0 := by
    have := sibO_cases j 4 (by decide); unfold padO; omega
  have far : ∀ X, B ≤ X → X < B + 1024 → ¬ (SCR ≤ X ∧ X < SCR + 32) ∧ ¬ (slotA B ≤ X ∧ X < slotA B + 16) ∧
      ¬ (1104 ≤ X ∧ X < 1144) ∧ ¬ (SigGolfCandidate.FtsGrind.slot2 B ≤ X ∧
        X < SigGolfCandidate.FtsGrind.slot2 B + 16) := fun X h1 h2 => by
    simp only [SCR, slotA, SigGolfCandidate.FtsGrind.slot2]; omega
  have hsb4 := sibO_cases j 4 (by decide)
  have dig4 : ∀ (o : Nat) (d : Digest), (o = padO j 4 ∨ o = sibO 4 j) → o + 16 ≤ 1024 → DigAt u (B + o) d →
      DigAt u' (B + o) d := by
    intro o d ho hlt hd
    have h16 : o % 16 = 0 ∧ o ≠ padO j 3 := by rcases ho with rfl | rfl <;> omega
    have h2o : ¬ (B + o = B + padO j 2 ∨ B + o = B + padO j 2 + 8) ∧
        ¬ (B + o + 8 = B + padO j 2 ∨ B + o + 8 = B + padO j 2 + 8) := by
      rcases ho with rfl | rfl
      · omega
      · omega
    refine DigAt.of_eq hd ?_ ?_
    · have := far (B + o) (by omega) (by omega)
      exact hvu _ (by omega) (by omega) this.1 this.2.1 this.2.2.1 h2o.1 this.2.2.2
    · have := far (B + o + 8) (by omega) (by omega)
      exact hvu _ (by omega) (by omega) this.1 this.2.1 this.2.2.1 h2o.2 this.2.2.2
  let pads' : Nat → Digest := fun l => if l = 4 then pads 4 else rdD u' (B + padO j l)
  let sibs' : Nat → Digest := fun l => if l = 4 then sibs 4 else rdD u' (B + sibO l j)
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
        by_cases e : l = 4
        · subst e; simp only [pads', if_true]
          exact dig4 _ _ (Or.inl rfl) (by unfold padO; omega) (hu.padAt 4 (by decide))
        · simp only [pads', e, if_false]; exact digAt_rdD _ _
      sibAt := fun l hl => by
        by_cases e : l = 4
        · subst e; simp only [sibs', if_true]
          exact dig4 _ _ (Or.inr rfl) (by omega) (hu.sibAt 4 (by decide))
        · simp only [sibs', e, if_false]; exact digAt_rdD _ _
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
  have HT := tail_tbsim (sk := sk) hj hbank hu' (by omega) _ s6 hmid
  have e : childLevelHi k index j pads' (hpOf j tws') sibs' (r.2.extractLsb' 0 128) =
      childLevelHi k index j pads (hpOf j tws) sibs (r.2.extractLsb' 0 128) := by
    simp only [childLevelHi, nodeIn, hpOf, pads', sibs', if_true, show ¬ (4 < 4) by decide, if_false]
  rw [e] at HT
  refine (TBSim.bind HT (fun c t7 hp => TBSim.pure ?_)).mono (Nat.le_refl _) (fun _ _ h => h)
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
  have hF : SigGolfCandidate.FtsGrind.FUEL (widthOf B) = 511 := rfl
  have hq1 : (2 ^ 64 * r2.1 + r.1) % 2 ^ 64 = r.1 := by have := ho.nle; omega
  have hq2 : (2 ^ 64 * r2.1 + r.1) / 2 ^ 64 = r2.1 := by have := ho.nle; omega
  have hpk : BitVec.ofNat 64 (2 ^ 64 * r2.1 + r.1) = BitVec.ofNat 64 r.1 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have hslot2 : SigGolfCandidate.FtsGrind.slot2 B = SCR + 2 * B + 16 := rfl
  refine ⟨by rw [hp.pc, virt_getReg], hp.a1, hp.top, hp.a2, fun x h3 h10' h11' h12' => by
      rw [hp.keep x h3 h10' h11' h12', virt_getReg], ?_, ?_, ⟨by rw [hq1]; exact ho.nle, by rw [hq2]; exact hs.nle⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t7m _ (by simp only [slotA, SCR]; omega) (by unfold prefixWrites slotA SCR; omega)
      (by simp only [slotA, SCR]; omega), u's _ (by simp only [slotA, SCR]; omega)
      (by simp only [slotA, SCR]; omega)]
    exact ho.slot0
  · rw [t7m _ (by simp only [slotA, SCR]; omega) (by unfold prefixWrites slotA SCR; omega)
      (by simp only [slotA, SCR]; omega), u's _ (by simp only [slotA, SCR]; omega)
      (by simp only [slotA, SCR]; omega), hpk]
    exact ho.slot1
  · intro h3400
    rw [t7m _ (by rw [hslot2]; simp only [SCR]; omega) (by rw [hslot2]; unfold prefixWrites SCR; omega)
      (by rw [hslot2]; simp only [SCR]; omega), u's _ (by rw [hslot2]; simp only [SCR]; omega)
      (by rw [hslot2]; simp only [SCR]; omega),
      hs6s _ (by rw [hslot2]; simp only [SCR]; omega)
        (by
          rintro ⟨off, hoff, he⟩
          have := stagesW_bound hj (by decide) hoff
          rw [hslot2] at he; simp only [SCR] at he; omega)
        (by rw [hslot2]; simp only [SCR]; omega) (by rw [hslot2]; simp only [SCR]; omega)
        (by rw [hslot2]; simp only [SCR, slotA]; omega) (by rw [hslot2]; simp only [SCR]; omega)]
    exact hs.rec0 h3400
  · intro h3400
    rw [hq2]
    rw [t7m _ (by rw [hslot2]; simp only [SCR]; omega) (by rw [hslot2]; unfold prefixWrites SCR; omega)
      (by rw [hslot2]; simp only [SCR]; omega), u's _ (by rw [hslot2]; simp only [SCR]; omega)
      (by rw [hslot2]; simp only [SCR]; omega),
      hs6s _ (by rw [hslot2]; simp only [SCR]; omega)
        (by
          rintro ⟨off, hoff, he⟩
          have := stagesW_bound hj (by decide) hoff
          rw [hslot2] at he; simp only [SCR] at he; omega)
        (by rw [hslot2]; simp only [SCR]; omega) (by rw [hslot2]; simp only [SCR]; omega)
        (by rw [hslot2]; simp only [SCR, slotA]; omega) (by rw [hslot2]; simp only [SCR]; omega)]
    exact hs.rec1 h3400
  · intro hB3; rw [hq2]; exact (hs.plain2 hB3).1
  · intro i hi
    rw [t7m _ (by omega) (by unfold prefixWrites; omega) (by omega), u's _ (by omega) (by omega)]
    exact ho.saves i hi
  · intro i hi
    rw [t7m _ (by simp only [SCR]; omega) (by unfold prefixWrites SCR; omega) (by simp only [SCR]; omega),
      u's _ (by simp only [SCR]; omega) (by simp only [SCR]; omega)]
    exact ho.scr i hi
  · intro X hX hn
    have hn' : ¬ prefixWrites B X ∧ ¬ (B - handO j ≤ X ∧ X < B - handO j + 32) ∧
        ¬ (slotA B ≤ X ∧ X < slotA B + 16) ∧ ¬ (3400 ≤ B ∧ slotA B + 16 ≤ X ∧ X < slotA B + 32) ∧
        ¬ (1104 ≤ X ∧ X < 1144) ∧ ¬ (SCR ≤ X ∧ X < SCR + 32) :=
      ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr (Or.inl h)),
        fun h => hn (Or.inr (Or.inr (Or.inl (Or.inl h)))), fun h => hn (Or.inr (Or.inr (Or.inl (Or.inr h)))),
        fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))), fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    rw [t7m _ hX hn'.1 hn'.2.1]
    by_cases hX2 : SigGolfCandidate.FtsGrind.slot2 B ≤ X ∧ X < SigGolfCandidate.FtsGrind.slot2 B + 16
    · have hB3 : B < 3400 := by
        by_contra hc
        apply hn'.2.2.2.1
        rw [hslot2] at hX2
        simp only [slotA]
        omega
      have hgt : ¬ ∃ off ∈ stagesW j 5, X = B + off := by
        rintro ⟨off, hoff, he⟩
        have := stagesW_bound hj (by decide) hoff
        rw [hslot2] at hX2; simp only [SCR] at hX2; omega
      rw [hvd, virt_getMem j B u s6 hBl hj X hX, if_neg hgt,
        hs6s X hX hgt (by rw [hslot2] at hX2; simp only [SCR] at hX2; omega) (by rw [hslot2] at hX2; simp only [SCR] at hX2; omega)
          (by rw [hslot2] at hX2; simp only [SCR, slotA] at hX2 ⊢; omega) (by rw [hslot2] at hX2; simp only [SCR] at hX2; omega)]
      have := (hs.plain2 hB3).2 (X - SigGolfCandidate.FtsGrind.slot2 B) (by omega)
      rwa [show SigGolfCandidate.FtsGrind.slot2 B + (X - SigGolfCandidate.FtsGrind.slot2 B) = X by omega] at this
    · rw [hvd, virt_getMem j B u s6 hBl hj X hX]
      split_ifs with hw
      · rfl
      · exact hsw X hX hw (by unfold prefixWrites at hn'; unfold padO at hp3 ⊢; omega) hn'.2.2.2.2.2 hn'.2.2.1
          hn'.2.2.2.2.1 (by
            rintro h
            apply hn'.1
            unfold prefixWrites; omega) hX2

/-- **A copy routine refines `childProgramC`**: from the copy entry `x` (the bank entry state `u` at the copy pc). -/
theorem childC_tbsim {x : MachineState} (hxu : u = bankPc j x) (hpx : x.pc = pcOf (copyBase j + 1))
    (hS2 : CodeAt im (pcOf (SigGolfCandidate.FtsGrind.s2Base (hiSel j 3)))
      (SigGolfCandidate.FtsGrind.search2Words (hiSel j 3)))
    (hT2 : CodeAt im (pcOf (tramp2Of j)) (SigGolfCandidate.FtsGrind.trampWords (tramp2Of j)
      (SigGolfCandidate.FtsGrind.s2Base (hiSel j 3)) (site2C j + 1))) :
    TBSim im sk x (17 + (cycR j 0 2 + (lvlSt j 2 + 1 + SigGolfCandidate.FtsGrind.W_SEARCH2) + (lvlSt j 3 + 1 + W_SEARCH (widthOf B) + 13)))
      (childProgramC k index j (widthOf B) B leaf pads sibs tws) (HandPostC B j u) := by
  -- TIER2B D1: `TBSim.bind` of `leafC_tbsim`, `restC_tbsim 2 0`, `lvl2C_tbsim hj hcode hS2 hT2 hu hlo hB` and
  -- `lvl3C_tbsim` (from `Mid2C`), then `rw [childProgramC, List.range_eq_range']` as in the D1 proof.
  have H := TBSim.bind (leafC_tbsim (sk := sk) hj hcode hu hxu hpx) (fun v s hs =>
    TBSim.bind (restC_tbsim (sk := sk) hj hcode hu 2 0 v s rfl hs) (fun v2 s2 hs2 =>
      TBSim.bind (lvl2C_tbsim (sk := sk) hj hcode hS2 hT2 hu hlo hB v2 s2 hs2) (fun r2 s3 hs3 =>
        lvl3C_tbsim hj hcode hbank hS hT hu hlo hB r2 s3 hs3)))
  rw [childProgramC, List.range_eq_range']
  simp only [bind_assoc, pure_bind] at H ⊢
  exact H.mono (by omega) (fun _ _ h => h)

end main

end W9Drv.SharedAProof
