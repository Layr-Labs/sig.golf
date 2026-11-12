import SigGolfCandidate.OuterNodeBankSetup
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeBankStepsB
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedBProof
theorem lvl_step {im : Image} {j : Nat} (hj : j < 128) (hcode : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j)) (OuterNodeBankLayout.bWords j))
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (l : Nat) (hl : l < 5) (v : Digest) (s : MachineState)
    (hs : Mid j B k index u l v s) :
    ∃ t, Steps im s (lvlSt j l) (lvlSt j l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) ∧
      ∀ a : BitVec 256, Mid j B k index u (l + 1) (selD j (l + 1) a) (writeHash t a) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, hec, h5, h10, h11, h12', hpcT, hother, h3', hin, hP,_,_,_⟩ := OuterNodeBankSetup.lvl_core hj hcode hu l (by omega) v s hs
  have hbl := blk_bounds j hj l (by omega)
  have hbl1 := blk_bounds j hj (l + 1) (by omega)
  have hb1 := bitAt_lt j (l + 1)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + outO (l + 1) j) := by
    rw [h12', lvlRegs_x12 j l hl]
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
variable {sk : BitVec 256}
theorem rest_tbsim {im : Image} {j : Nat} (hj : j<128) (hcode : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j)) (OuterNodeBankLayout.bWords j))
    {B k index : Nat} {leaf pads sibs tws : Nat→Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) :
    ∀ n l v state,l+n=5→Mid j B k index u l v state→
      TBSim im sk state (cycR j l n)
        ((List.range' l n).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v)
        (Mid j B k index u 5) := by
  intro n
  induction n with
  | zero =>
      intro l v state hln hs
      have hl:l=5:=by omega
      subst l
      simpa only [List.range'_zero,List.foldlM_nil,cycR] using (TBSim.pure hs (sk:=sk) (image:=im))
  | succ n ih =>
      intro l v state hln hs
      obtain ⟨t,hst,hf,h5,hv,hin,hpost⟩:=OuterNodeBankStepsB.lvl_step hj hcode hu l (by omega) v state hs
      rw [List.range'_succ,List.foldlM_cons,childLevelP_eq]
      have H:=TBSim.hashSel_bind (sk:=sk) (W:=cycR j (l+1) n) (hi:=hiSel j (l+1))
        (f:=fun v'=>(List.range' (l+1) n).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v')
        (Q:=Mid j B k index u 5) hf h5 hv hin
        (fun a=>ih (l+1) _ _ (by omega) (hpost a))
      rw [nodeIn_blocks] at H
      simpa only [cycR,Nat.add_assoc] using TBSim.steps hst H


#print axioms rest_tbsim

#print axioms lvl_step
end OuterNodeBankStepsB
