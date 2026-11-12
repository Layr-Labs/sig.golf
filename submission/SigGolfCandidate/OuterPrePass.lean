import SigGolfCandidate.OuterImageTransfers
import SigGolfCandidate.Merge078
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.PrePass
#check OuterImageTransfers.code
-- rebinding checked code / machine step
theorem codeAt_D1 : CodeAt OuterImages.expandImage (pcOf 54569) codeD1 := OuterImageTransfers.code (b:=54569) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_D1

-- rebinding checked code / machine step
theorem codeAt_r6 : CodeAt OuterImages.expandImage (pcOf 60919) Images.expandR6Code := OuterImageTransfers.code (b:=60919) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_r6

-- rebinding checked code / machine step
theorem d1_spec (s : MachineState) (hpc : s.pc = pcOf 54569) :
    ∃ t, Steps OuterImages.expandImage s 73 73 t ∧ t.pc = pcOf 60919 ∧
      t.getReg .x18 = xR s.getMem ∧ RegsExcept s t [.x6, .x7, .x18, .x28] ∧
      ∀ A, t.getMem A = d1Mem s.getMem A := by
  refine ⟨_, symRun_sound eD1 codeAt_D1 s hpc trivial, eD1_pc s, ?_, ?_, fun A => eD1_mem s A⟩
  · rw [Result.toState_getReg]; exact eD1_x18 s
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem codeAt_dec : CodeAt OuterImages.expandImage (pcOf 88000) cDec := OuterImageTransfers.code (b:=88000) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_dec

-- rebinding checked code / machine step
theorem codeAt_H : CodeAt OuterImages.expandImage (pcOf 54644) cH := OuterImageTransfers.code (b:=54644) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_H

-- rebinding checked code / machine step
theorem r6_at {seg : List (BitVec 32)} (o : Nat) (h : o + seg.length ≤ 63)
    (h2 : (Images.expandR6Code.drop o).take seg.length = seg) :
    CodeAt OuterImages.expandImage (pcOf (60919 + o)) seg :=
  codeAt_sub o codeAt_r6 (by rw [show Images.expandR6Code.length = 63 from rfl]; exact h) h2

-- rebinding checked code / machine step
theorem u1_spec (s : MachineState) (hpc : s.pc = pcOf 60919) :
    ∃ t, Steps OuterImages.expandImage s 6 6 t ∧
      t.pc = (if s.getReg .x18 >>> 33 = 7#64 then pcOf 60925 else pcOf 60930) ∧
      t.getReg .x6 = s.getMem (BitVec.ofNat 64 0x7000) ∧ t.getReg .x7 = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x7000 ∧ t.getReg .x29 = s.getReg .x18 >>> 33 ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound eU1 (r6_at 0 (by decide) rfl) s hpc trivial, ?_, rfl, rfl, rfl, rfl, ?_, fun A => rfl⟩
  · simp only [Result.toState_pc, eU1.res, E.eval, BinOp.eval, CmpOp.eval]
    by_cases h : s.getReg .x18 >>> 33 = 7#64
    · rw [if_pos h]; simp [h]
    · rw [if_neg h]; simp [h]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem u2_spec (s : MachineState) (hpc : s.pc = pcOf 60925) :
    ∃ t, Steps OuterImages.expandImage s 2 2 t ∧
      t.pc = (if s.getReg .x7 = 18446744073709551615#64 then pcOf 60927 else pcOf 60930) ∧
      RegsExcept s t [.x30] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound eU2 (r6_at 6 (by decide) rfl) s hpc trivial, ?_, ?_, fun A => rfl⟩
  · simp only [Result.toState_pc, eU2.res, E.eval, BinOp.eval, CmpOp.eval]
    by_cases h : s.getReg .x7 = 18446744073709551615#64
    · rw [if_pos h]; simp [h]
    · rw [if_neg h]; simp [h]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem u3_spec (s : MachineState) (hpc : s.pc = pcOf 60927) :
    ∃ t, Steps OuterImages.expandImage s 2 2 t ∧
      t.pc = (if (s.getReg .x6).toNat < 18446744073709551368 then pcOf 60930 else pcOf 60929) ∧
      RegsExcept s t [.x30] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound eU3 (r6_at 8 (by decide) rfl) s hpc trivial, ?_, ?_, fun A => rfl⟩
  · simp only [Result.toState_pc, eU3.res, E.eval, BinOp.eval, CmpOp.eval]
    by_cases h : (s.getReg .x6).toNat < 18446744073709551368
    · rw [if_pos h]; simp [BitVec.ult, h]
    · rw [if_neg h]; simp [BitVec.ult, h]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem uR_spec (s : MachineState) (hpc : s.pc = pcOf 60929) :
    ∃ t, Steps OuterImages.expandImage s 1 1 t ∧ t.pc = pcOf 354 :=
  ⟨_, symRun_sound eUR (r6_at 10 (by decide) rfl) s hpc trivial, rfl⟩

-- rebinding checked code / machine step
theorem u4_spec (s : MachineState) (hpc : s.pc = pcOf 60930) (h28 : s.getReg .x28 = BitVec.ofNat 64 0x7000) :
    ∃ t c, Steps OuterImages.expandImage s 31 c t ∧ c ≤ 60 ∧ t.pc = pcOf 88000 ∧
      t.getReg .x29 = r3W (s.getReg .x29) (s.getReg .x7) (s.getReg .x6) ∧
      RegsExcept s t [.x19, .x20, .x29, .x30] ∧
      ∀ A, t.getMem A = if A = BitVec.ofNat 64 0x7000 then qLo (s.getReg .x29) (s.getReg .x7) (s.getReg .x6)
        else if A = BitVec.ofNat 64 0x7008 then qHi (s.getReg .x29) (s.getReg .x7) else s.getMem A := by
  refine ⟨_, _, symRun_sound eU4 (r6_at 11 (by decide) rfl) s hpc ?_, by simp [eU4.res], rfl, rfl, ?_, ?_⟩
  · simp [eU4.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A
    simp only [Result.toState_getMem, eU4.res]
    t3n [h28]
    rfl

-- rebinding checked code / machine step
theorem dec_spec (s : MachineState) (hpc : s.pc = pcOf 88000) (r : Nat) (hr : r < 360)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 r) :
    ∃ t c, Steps OuterImages.expandImage s 57 c t ∧ c ≤ 75 ∧ t.pc = pcOf 54644 ∧
      t.getReg .x6 = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.SharedCodec.packH r) ∧
      RegsExcept s t [.x6, .x7, .x19, .x20, .x28, .x29, .x30] ∧
      ∀ A, t.getMem A = if A = BitVec.ofNat 64 417792 then BitVec.ofNat 64 (ClaudeWCT.W9.T3M.SharedCodec.packH r)
        else s.getMem A := by
  have hv : (eDec.res.toState s).getReg .x6 = decVal (s.getReg .x29) := by
    simp only [Result.toState_getReg, eDec.res, rv_simp]; rfl
  have hv' : decVal (s.getReg .x29) = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.SharedCodec.packH r) := by
    rw [h29]; exact decVal_table ⟨r, hr⟩
  refine ⟨_, _, symRun_sound eDec codeAt_dec s hpc ?_, by simp [eDec.res], rfl, by rw [hv, hv'], ?_, ?_⟩
  · simp [eDec.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · intro q hq
    rw [Result.toState_getReg]
    cases q <;> first | exact (hq (by decide)).elim | rfl
  · intro A
    have hm : (eDec.res.toState s).getMem A =
        if A = BitVec.ofNat 64 417792 then (eDec.res.toState s).getReg .x6 else s.getMem A := by
      simp only [Result.toState_getMem, Result.toState_getReg, eDec.res]
      t3n []
    rw [hm, hv, hv']

-- rebinding checked code / machine step
theorem h_spec (s : MachineState) (hpc : s.pc = pcOf 54644) :
    ∃ t, Steps OuterImages.expandImage s 3 3 t ∧
      t.pc = (if (s.getReg .x6).toNat < 12288 then pcOf 54648 else pcOf 54647) ∧
      RegsExcept s t [.x7] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound eH codeAt_H s hpc trivial, ?_, ?_, fun A => rfl⟩
  · simp only [Result.toState_pc, eH.res, E.eval, BinOp.eval, CmpOp.eval]
    by_cases h : (s.getReg .x6).toNat < 12288
    · rw [if_pos h]; simp [BitVec.ult, h]
    · rw [if_neg h]; simp [BitVec.ult, h]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem tail_spec (s : MachineState) (hpc : s.pc = pcOf 60930) (h28 : s.getReg .x28 = BitVec.ofNat 64 0x7000)
    (hT : (s.getReg .x29).toNat < 128) :
    ∃ t k c, Steps OuterImages.expandImage s k c t ∧ c ≤ 138 ∧ t.pc = pcOf 54648 ∧
      RegsExcept s t [.x6, .x7, .x19, .x20, .x28, .x29, .x30] ∧
      ∀ A, t.getMem A = r6Mem s.getMem (s.getReg .x29) (s.getReg .x7) (s.getReg .x6) A := by
  obtain ⟨t4, c4, s4, hc4, p4, a29, g4, m4⟩ := u4_spec s hpc h28
  have hr : (r3W (s.getReg .x29) (s.getReg .x7) (s.getReg .x6)).toNat < 360 := by
    rw [(r6_arith _ _ _ hT).1]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨t5, c5, s5, hc5, p5, x5, g5, m5⟩ := dec_spec t4 p4 _ hr (by rw [a29, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hlt := ClaudeWCT.W9.T3M.SharedCodec.packH_le_9671 _ hr
  obtain ⟨t8, s8, p8, g8, m8⟩ := h_spec t5 p5
  refine ⟨t8, _, _, (s4.trans s5).trans s8, by omega, ?_, ?_, ?_⟩
  · rw [p8, x5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  · exact (g4.trans (g5.trans g8)).mono (by decide)
  · intro A
    rw [m8, m5, m4]
    unfold r6Mem
    by_cases hA : A = BitVec.ofNat 64 417792 <;> simp [hA]

-- rebinding checked code / machine step
theorem r6_ok (s : MachineState) (hpc : s.pc = pcOf 60919) (hX : (s.getReg .x18).toNat < 68719476736)
    (hc : (s.getMem (BitVec.ofNat 64 0x7000)).toNat + (s.getMem (BitVec.ofNat 64 0x7008)).toNat * 18446744073709551616 +
      (s.getReg .x18 >>> 33).toNat * 340282366920938463463374607431768211456 < 2722258935367507707706996859454145691400) :
    ∃ t k c, Steps OuterImages.expandImage s k c t ∧ c ≤ 148 ∧ t.pc = pcOf 54648 ∧
      RegsExcept s t [.x6, .x7, .x19, .x20, .x28, .x29, .x30] ∧
      ∀ A, t.getMem A = r6Mem s.getMem (s.getReg .x18 >>> 33) (s.getMem (BitVec.ofNat 64 0x7008))
        (s.getMem (BitVec.ofNat 64 0x7000)) A := by
  obtain ⟨t1, s1, p1, a6, a7, a28, a29, g1, m1⟩ := u1_spec s hpc
  have hT := shr29_lt _ hX
  have go : ∀ (u : MachineState) (k c : Nat), Steps OuterImages.expandImage s k c u → c ≤ 10 → u.pc = pcOf 60930 →
      RegsExcept t1 u [.x30] → (∀ A, u.getMem A = s.getMem A) →
      ∃ t k c, Steps OuterImages.expandImage s k c t ∧ c ≤ 148 ∧ t.pc = pcOf 54648 ∧
        RegsExcept s t [.x6, .x7, .x19, .x20, .x28, .x29, .x30] ∧
        ∀ A, t.getMem A = r6Mem s.getMem (s.getReg .x18 >>> 33) (s.getMem (BitVec.ofNat 64 0x7008))
          (s.getMem (BitVec.ofNat 64 0x7000)) A := by
    intro u k c su hcu pu gu mu
    have u28 : u.getReg .x28 = BitVec.ofNat 64 0x7000 := by rw [gu.get (by decide), a28]
    have u29 : u.getReg .x29 = s.getReg .x18 >>> 33 := by rw [gu.get (by decide), a29]
    have u7 : u.getReg .x7 = s.getMem (BitVec.ofNat 64 0x7008) := by rw [gu.get (by decide), a7]
    have u6 : u.getReg .x6 = s.getMem (BitVec.ofNat 64 0x7000) := by rw [gu.get (by decide), a6]
    obtain ⟨t, k', c', st, hc', pt, gt, mt⟩ := tail_spec u pu u28 (by rw [u29]; exact hT)
    refine ⟨t, _, _, su.trans st, by omega, pt, ((g1.trans gu).trans gt).mono (by decide), ?_⟩
    intro A
    rw [mt, u29, u7, u6]
    unfold r6Mem
    rw [mu]
  have hT' := hT
  by_cases h7 : s.getReg .x18 >>> 33 = 7#64
  · rw [if_pos h7] at p1
    obtain ⟨t2, s2, p2, g2, m2⟩ := u2_spec t1 p1
    have hH := (s.getMem (BitVec.ofNat 64 0x7008)).isLt
    have hL := (s.getMem (BitVec.ofNat 64 0x7000)).isLt
    norm_num at hH hL
    have ht : (s.getReg .x18 >>> 33).toNat = 7 := by rw [h7]; rfl
    have hc2 := (canon_iff _ _ _ (shr33_lt8 _ hX) hH hL).1 hc
    rw [ht] at hc2
    by_cases hA : (s.getMem (BitVec.ofNat 64 0x7008)).toNat = 18446744073709551615
    · rw [a7, if_pos ((allOnes_iff _).2 hA)] at p2
      obtain ⟨t3, s3, p3, g3, m3⟩ := u3_spec t2 p2
      have hl : (t2.getReg .x6).toNat < 18446744073709551368 := by
        rw [g2.get (by decide), a6]; omega
      rw [if_pos hl] at p3
      exact go t3 _ _ ((s1.trans s2).trans s3) (by omega) p3 ((g2.trans g3).mono (by decide))
        (fun A => by rw [m3, m2, m1])
    · rw [a7, if_neg (fun e => hA ((allOnes_iff _).1 e))] at p2
      exact go t2 _ _ (s1.trans s2) (by omega) p2 g2 (fun A => by rw [m2, m1])
  · rw [if_neg h7] at p1
    exact go t1 _ _ s1 (by omega) p1 (RegsExcept.refl _ _) m1

-- rebinding checked code / machine step
theorem r6_bad (s : MachineState) (hpc : s.pc = pcOf 60919) (hX : (s.getReg .x18).toNat < 68719476736)
    (hc : ¬ (s.getMem (BitVec.ofNat 64 0x7000)).toNat + (s.getMem (BitVec.ofNat 64 0x7008)).toNat * 18446744073709551616 +
      (s.getReg .x18 >>> 33).toNat * 340282366920938463463374607431768211456 < 2722258935367507707706996859454145691400) :
    ∃ t, Steps OuterImages.expandImage s 11 11 t ∧ t.pc = pcOf 354 := by
  obtain ⟨t1, s1, p1, a6, a7, a28, a29, g1, m1⟩ := u1_spec s hpc
  have hT := shr29_lt _ hX
  have hH := (s.getMem (BitVec.ofNat 64 0x7008)).isLt
  have hL := (s.getMem (BitVec.ofNat 64 0x7000)).isLt
  norm_num at hH hL
  have hb := not_not.1 (fun h => hc ((canon_iff _ _ _ (shr33_lt8 _ hX) hH hL).2 h))
  have h7 : s.getReg .x18 >>> 33 = 7#64 := by apply BitVec.eq_of_toNat_eq; rw [hb.1]; rfl
  rw [if_pos h7] at p1
  obtain ⟨t2, s2, p2, g2, m2⟩ := u2_spec t1 p1
  rw [a7, if_pos ((allOnes_iff _).2 hb.2.1)] at p2
  obtain ⟨t3, s3, p3, g3, m3⟩ := u3_spec t2 p2
  have hl : ¬ (t2.getReg .x6).toNat < 18446744073709551368 := by
    rw [g2.get (by decide), a6]; omega
  rw [if_neg hl] at p3
  obtain ⟨t4, s4, p4⟩ := uR_spec t3 p3
  exact ⟨t4, ((s1.trans s2).trans s3).trans s4, p4⟩

-- rebinding checked code / machine step
theorem codeAt_D3 : CodeAt OuterImages.expandImage (pcOf 54648) codeD3 := OuterImageTransfers.code (b:=54648) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_D3

-- rebinding checked code / machine step
theorem d3_spec (s : MachineState) (hpc : s.pc = pcOf 54648) :
    ∃ t, Steps OuterImages.expandImage s 18 18 t ∧ t.pc = pcOf 54666 ∧
      t.getReg .x19 = s.getMem (BitVec.ofNat 64 0x8440) ∧
      t.getReg .x20 = sibH (s.getMem (BitVec.ofNat 64 0x8448)) (s.getReg .x18) ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * (176 + 147)) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 176) ∧
      RegsExcept s t [.x7, .x19, .x20, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eD3 codeAt_D3 s hpc trivial, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp [eD3.res, rv_simp, sibH]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A _ _
    rfl

-- rebinding checked code / machine step
theorem codeAt_L1 : CodeAt OuterImages.expandImage (pcOf 54666) codeL1 := OuterImageTransfers.code (b:=54666) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_L1

-- rebinding checked code / machine step
theorem stepL1 : StepOK OuterImages.expandImage 54666 128 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL1 codeAt_L1 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL1.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL1.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL1.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL1.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL1.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

-- rebinding checked code / machine step
theorem codeAt_L2 : CodeAt OuterImages.expandImage (pcOf 54676) codeL2 := OuterImageTransfers.code (b:=54676) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_L2

-- rebinding checked code / machine step
theorem stepL2 : StepOK OuterImages.expandImage 54676 64 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL2 codeAt_L2 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL2.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL2.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL2.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL2.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL2.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

-- rebinding checked code / machine step
theorem codeAt_L3 : CodeAt OuterImages.expandImage (pcOf 54686) codeL3 := OuterImageTransfers.code (b:=54686) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_L3

-- rebinding checked code / machine step
theorem stepL3 : StepOK OuterImages.expandImage 54686 48 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL3 codeAt_L3 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL3.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL3.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL3.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL3.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL3.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

-- rebinding checked code / machine step
theorem codeAt_L4 : CodeAt OuterImages.expandImage (pcOf 54696) codeL4 := OuterImageTransfers.code (b:=54696) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_L4

-- rebinding checked code / machine step
theorem stepL4 : StepOK OuterImages.expandImage 54696 32 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL4 codeAt_L4 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL4.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL4.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL4.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL4.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL4.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

-- rebinding checked code / machine step
theorem codeAt_L5 : CodeAt OuterImages.expandImage (pcOf 54706) codeL5 := OuterImageTransfers.code (b:=54706) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_L5

-- rebinding checked code / machine step
theorem stepL5 : StepOK OuterImages.expandImage 54706 16 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL5 codeAt_L5 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL5.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL5.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL5.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL5.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL5.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

-- rebinding checked code / machine step
theorem codeAt_S54672 : CodeAt OuterImages.expandImage (pcOf 54672) codeS54672 := OuterImageTransfers.code (b:=54672) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_S54672

-- rebinding checked code / machine step
theorem setup54672 (s : MachineState) (hpc : s.pc = pcOf 54672) :
    ∃ t, Steps OuterImages.expandImage s 4 4 t ∧ t.pc = pcOf 54676 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 175) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 88) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54672 codeAt_S54672 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem codeAt_S54682 : CodeAt OuterImages.expandImage (pcOf 54682) codeS54682 := OuterImageTransfers.code (b:=54682) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_S54682

-- rebinding checked code / machine step
theorem setup54682 (s : MachineState) (hpc : s.pc = pcOf 54682) :
    ∃ t, Steps OuterImages.expandImage s 4 4 t ∧ t.pc = pcOf 54686 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 87) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 63) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54682 codeAt_S54682 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem codeAt_S54692 : CodeAt OuterImages.expandImage (pcOf 54692) codeS54692 := OuterImageTransfers.code (b:=54692) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_S54692

-- rebinding checked code / machine step
theorem setup54692 (s : MachineState) (hpc : s.pc = pcOf 54692) :
    ∃ t, Steps OuterImages.expandImage s 4 4 t ∧ t.pc = pcOf 54696 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 62) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 38) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54692 codeAt_S54692 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem codeAt_S54702 : CodeAt OuterImages.expandImage (pcOf 54702) codeS54702 := OuterImageTransfers.code (b:=54702) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_S54702

-- rebinding checked code / machine step
theorem setup54702 (s : MachineState) (hpc : s.pc = pcOf 54702) :
    ∃ t, Steps OuterImages.expandImage s 4 4 t ∧ t.pc = pcOf 54706 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 37) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 13) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54702 codeAt_S54702 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

-- rebinding checked code / machine step
theorem codeAt_D6 : CodeAt OuterImages.expandImage (pcOf 54712) codeD6 := OuterImageTransfers.code (b:=54712) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.codeAt_D6

-- rebinding checked code / machine step
theorem d6_spec (s : MachineState) (hpc : s.pc = pcOf 54712) :
    ∃ t, Steps OuterImages.expandImage s 27 27 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30] ∧
      (∀ k w, k < 332 → w < 2 → t.getMem (slotA k w) =
        if dummySlot k then 0 else if k = 180 then (if w = 0 then s.getReg .x19 else s.getReg .x20)
        else s.getMem (slotA k w)) ∧
      Frame s t (fun X => 0x70d0 ≤ X ∧ X < 0x84c0) := by
  refine ⟨_, symRun_sound eD6 codeAt_D6 s hpc (by simp [eD6.res, rv_simp]),
    rfl, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [Result.toState_getReg]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro k w hk hw
    simp only [Result.toState_getMem, eD6.res, slotA]
    t3n []
    rw [Nat.mod_eq_of_lt (show 0x7000 + 16 * k + 8 * w < 18446744073709551616 by omega)]
    by_cases hs : k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 180 ∨ k = 181 ∨ k = 182 ∨ k = 183
    · obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
      all_goals (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dummySlot])
    · iterate 16 rw [if_neg (by omega)]
      rw [if_neg (show ¬ dummySlot k by unfold dummySlot; omega), if_neg (by omega)]
  · intro X hX hn
    simp only [Result.toState_getMem, eD6.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show X < 18446744073709551616 by simpa using hX)]
    iterate 16 rw [if_neg (by omega)]

-- rebinding checked code / machine step
theorem d1r6_ok (s : MachineState) (hpc : s.pc = pcOf 54569)
    (hc : nOfM s.getMem < 2722258935367507707706996859454145691400) :
    ∃ t k c, Steps OuterImages.expandImage s (73 + k) (73 + c) t ∧ c ≤ 148 ∧ t.pc = pcOf 54648 ∧
      t.getReg .x18 = xR s.getMem ∧
      RegsExcept s t [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30] ∧ (∀ A, t.getMem A = dMem s.getMem A) ∧
      Frame s t (fun A => A = 417792 ∨ A = 0x7000 ∨ A = 0x7008 ∨ (31368 ≤ A ∧ A ≤ 31480)) := by
  obtain ⟨s1, st1, p1, x1, r1, m1⟩ := d1_spec s hpc
  have hm1 : s1.getMem = d1Mem s.getMem := funext m1
  have l0 : d1Mem s.getMem (BitVec.ofNat 64 0x7000) = s.getMem (BitVec.ofNat 64 0x7000) :=
    d1Mem_frame _ _ (by decide) (by decide)
  have l1 : d1Mem s.getMem (BitVec.ofNat 64 0x7008) = s.getMem (BitVec.ofNat 64 0x7008) :=
    d1Mem_frame _ _ (by decide) (by decide)
  obtain ⟨t, k, c, st, hcc, pt, rt, mt⟩ := r6_ok s1 p1 (by rw [x1]; exact xR_lt _)
    (by rw [hm1, x1, l0, l1, xR_shr]; exact hc)
  have rt' := rt
  refine ⟨t, k, c, st1.trans st, hcc, pt, by rw [rt.get (by decide), x1], (r1.trans rt).mono (by decide), ?_, ?_⟩
  · intro A; rw [mt, hm1, x1]; rfl
  · intro A hA hn
    simp only [not_or] at hn
    rw [mt, hm1, x1, r6Mem_frame _ _ _ _ A hA hn.1 hn.2.1 hn.2.2.1, d1Mem_frame _ _ hA (by omega)]

-- rebinding checked code / machine step
theorem d1r6_bad (s : MachineState) (hpc : s.pc = pcOf 54569)
    (hc : ¬ nOfM s.getMem < 2722258935367507707706996859454145691400) :
    ∃ t, Steps OuterImages.expandImage s 84 84 t ∧ t.pc = pcOf 354 := by
  obtain ⟨s1, st1, p1, x1, r1, m1⟩ := d1_spec s hpc
  have hm1 : s1.getMem = d1Mem s.getMem := funext m1
  have l0 : d1Mem s.getMem (BitVec.ofNat 64 0x7000) = s.getMem (BitVec.ofNat 64 0x7000) :=
    d1Mem_frame _ _ (by decide) (by decide)
  have l1 : d1Mem s.getMem (BitVec.ofNat 64 0x7008) = s.getMem (BitVec.ofNat 64 0x7008) :=
    d1Mem_frame _ _ (by decide) (by decide)
  obtain ⟨t, st, pt⟩ := r6_bad s1 p1 (by rw [x1]; exact xR_lt _)
    (by rw [hm1, x1, l0, l1, xR_shr]; exact hc)
  exact ⟨t, st1.trans st, pt⟩

-- rebinding checked code / machine step
theorem dec_run (s : MachineState) (hpc : s.pc = pcOf 54569)
    (hc : nOfM s.getMem < 2722258935367507707706996859454145691400) :
    ∃ t k c, Steps OuterImages.expandImage s k c t ∧ c ≤ 2148 ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30] ∧
      (∀ k w, k < 332 → w < 2 → t.getMem (slotA k w) = decOut s.getMem k w) ∧
      t.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.SharedCodec.packH (nOfM s.getMem % 360)) ∧
      Frame s t (fun A => A = 417792 ∨ (0x7000 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨s1, k1, c1, st1, hc1, pc1, x18_1, r1, m1, f1⟩ := d1r6_ok s hpc hc
  obtain ⟨s2, st2, pc2, x19_2, x20_2, x28_2, x30_2, r2, f2⟩ := d3_spec s1 pc1
  obtain ⟨s3, st3, pc3, r3, m3, f3⟩ := loop_slots 8 176 147 stepL1 (by omega) (by omega) (by omega) s2 pc2 x28_2 x30_2
  obtain ⟨s4, st4, pc4, x28_4, x30_4, r4, f4⟩ := setup54672 s3 (by rw [pc3])
  obtain ⟨s5, st5, pc5, r5, m5, f5⟩ := loop_slots 4 88 87 stepL2 (by omega) (by omega) (by omega) s4 pc4
    (by rw [x28_4]) x30_4
  obtain ⟨s6, st6, pc6, x28_6, x30_6, r6, f6⟩ := setup54682 s5 (by rw [pc5])
  obtain ⟨s7, st7, pc7, r7, m7, f7⟩ := loop_slots 3 63 24 stepL3 (by omega) (by omega) (by omega) s6 pc6
    (by rw [x28_6]) x30_6
  obtain ⟨s8, st8, pc8, x28_8, x30_8, r8, f8⟩ := setup54692 s7 (by rw [pc7])
  obtain ⟨s9, st9, pc9, r9, m9, f9⟩ := loop_slots 2 38 24 stepL4 (by omega) (by omega) (by omega) s8 pc8
    (by rw [x28_8]) x30_8
  obtain ⟨s10, st10, pc10, x28_10, x30_10, r10, f10⟩ := setup54702 s9 (by rw [pc9])
  obtain ⟨s11, st11, pc11, r11, m11, f11⟩ := loop_slots 1 13 24 stepL5 (by omega) (by omega) (by omega) s10 pc10
    (by rw [x28_10]) x30_10
  obtain ⟨t, st12, pc12, z12, r12, m12, f12⟩ := d6_spec s11 (by rw [pc11])
  -- frames after R6
  have fA : Frame s2 s11 (fun X => 0x70d0 ≤ X ∧ X < 0x84c0) :=
    ((((((((f3.trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11).mono
      (fun X _ h => by
        rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) <;> first | exact h | exact h.elim)
  have regs11 : RegsExcept s2 s11 [.x6, .x7, .x28, .x30] :=
    ((((((((r3.trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans r10).trans r11).mono
      (by intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  have e8440 : dMem s.getMem (BitVec.ofNat 64 0x8440) = s.getMem (BitVec.ofNat 64 0x8440) := by
    unfold dMem
    rw [r6Mem_frame _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), d1Mem_frame _ _ (by decide) (by decide)]
  have e8448 : dMem s.getMem (BitVec.ofNat 64 0x8448) = s.getMem (BitVec.ofNat 64 0x8448) := by
    unfold dMem
    rw [r6Mem_frame _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), d1Mem_frame _ _ (by decide) (by decide)]
  have st := (((((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9).trans
      st10).trans st11).trans st12)
  refine ⟨t, _, _, st, by omega, pc12, z12, ?_, ?_, ?_, ?_⟩
  · exact ((r1.trans (r2.trans (regs11.trans r12)))).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  · intro k w hk hw
    rw [m12 k w hk hw]
    unfold decOut
    split_ifs with hd h180 hw0
    · rfl
    · rw [regs11.get (by decide), x19_2, m1, e8440]
    · rw [regs11.get (by decide), x20_2, m1, e8448, x18_1]
    · have hk5 := fL_le 13 24 1 k
      have hk4 := fL_le 38 24 2 (fL 13 24 1 k)
      have hk3 := fL_le 63 24 3 (fL 38 24 2 (fL 13 24 1 k))
      have hk2 := fL_le 88 87 4 (fL 63 24 3 (fL 38 24 2 (fL 13 24 1 k)))
      rw [m11 k w hk hw, frame_slot f10 _ w (by omega) hw,
        m9 _ w (by omega) hw, frame_slot f8 _ w (by omega) hw,
        m7 _ w (by omega) hw, frame_slot f6 _ w (by omega) hw,
        m5 _ w (by omega) hw, frame_slot f4 _ w (by omega) hw,
        m3 _ w (by omega) hw, srcK_comp k hk hd h180, frame_slot f2 _ w (by unfold srcK; split_ifs <;> omega) hw, m1]
  · have e : t.getMem (BitVec.ofNat 64 417792) = s2.getMem (BitVec.ofNat 64 417792) :=
      (f12.get (by decide) (by omega)).trans (fA.get (by decide) (by omega))
    rw [e, f2.get (by decide) id, m1, dMem_hint]
  · exact ((((f1.trans f2).trans fA).trans f12).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h
      · rcases h with h | h | h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · exact h.elim
      · exact Or.inr ⟨by omega, h.2⟩
      · exact Or.inr ⟨by omega, h.2⟩))

-- rebinding checked code / machine step
theorem dec_bad (s : MachineState) (hpc : s.pc = pcOf 54569)
    (hc : ¬ nOfM s.getMem < 2722258935367507707706996859454145691400) :
    ∃ t, Steps OuterImages.expandImage s 84 84 t ∧ t.pc = pcOf 354 := d1r6_bad s hpc hc
theorem code_pre : CodeAt OuterImages.expandImage (pcOf 87500) cPre :=
  OuterImageTransfers.code (b:=87500) (words:=cPre) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PrePass.code_pre

theorem pre_spec (s : MachineState) (hpc : s.pc = pcOf 87500) :
    ∃ u, Steps OuterImages.expandImage s 217 217 u ∧ u.pc = pcOf 54569 ∧
      (∀ r ∈ [Reg.x7, .x28, .x29, .x30, .x31], u.getReg r = 0) ∧ RegsExcept s u [.x7, .x28, .x29, .x30, .x31] ∧
      ∀ A, u.getMem A = preMem s.getMem A := by
  refine ⟨_, symRun_sound ePre code_pre s hpc trivial, rfl, ?_, ?_, pre_mem s⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro x hx
    cases x <;> first | (exfalso; simp at hx; done) | rfl

#print axioms dec_run
#print axioms pre_spec
end OuterPrePass
