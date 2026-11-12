import SigGolfCandidate.OuterImageTransfers
import SigGolfCandidate.Merge072
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPadWriter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.PadWriter
variable (s : MachineState)
theorem code_P1 : CodeAt OuterImages.expandImage (pcOf 44961) cP1  := OuterImageTransfers.code (b:=44961) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_P1
theorem code_S1 : CodeAt OuterImages.expandImage (pcOf 44974) cS1  := OuterImageTransfers.code (b:=44974) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_S1
theorem code_S2 : CodeAt OuterImages.expandImage (pcOf 45000) cS2  := OuterImageTransfers.code (b:=45000) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_S2
theorem code_J45015 : CodeAt OuterImages.expandImage (pcOf 45015) cJ45015  := OuterImageTransfers.code (b:=45015) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_J45015
theorem code_hook : CodeAt OuterImages.expandImage (pcOf 54174) cHook  := OuterImageTransfers.code (b:=54174) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_hook
theorem code_table : CodeAt OuterImages.expandImage (pcOf 44193) cTable  := OuterImageTransfers.code (b:=44193) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_table
theorem code_row (r : Nat) (hr : r < 128) : CodeAt OuterImages.expandImage (pcOf (44193 + 6 * r)) (rowCode r)  := by
  have hb : ∀ i : Fin 128,OuterImageTransfers.Clean (44193+6*i.val) (rowCode i.val).length := by decide +kernel
  have h:=hb ⟨r,hr⟩
  dsimp only at h
  exact OuterImageTransfers.code (b:=44193+6*r) h (ClaudeWCT.W9.Machine.Expand.PadWriter.code_row r hr)
theorem row_spec (r : Nat) (hr : r < 128) (v : MachineState) (hpc : v.pc = pcOf (44193 + 6 * r)) :
    ∃ w, Steps OuterImages.expandImage v 6 6 w ∧ w.pc = pcOf (if r < 64 then 44974 else 45000) ∧
      w.getReg .x11 = BitVec.ofNat 64 (offR r 0) ∧ w.getReg .x12 = BitVec.ofNat 64 (offR r 1) ∧
      w.getReg .x13 = BitVec.ofNat 64 (offR r 2) ∧ w.getReg .x15 = BitVec.ofNat 64 (offR r 3) ∧
      w.getReg .x16 = BitVec.ofNat 64 (offR r 4) ∧
      RegsExcept v w [.x11, .x12, .x13, .x15, .x16] ∧ ∀ A, w.getMem A = v.getMem A := by
  refine ⟨_, symRun_sound (run_row r hr) (code_row r hr) v hpc trivial, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    fun A => rfl⟩
  intro x hx
  rw [Result.toState_getReg]
  cases x <;> first | rfl | (exfalso; simp at hx)

/-! ### Dispatch targets -/

theorem p1_spec (s : MachineState) (hpc : s.pc = pcOf 44961) :
    ∃ u, Steps OuterImages.expandImage s 13 13 u ∧
      u.pc = pcOf (44193 + 6 * ((s.getMem (BitVec.ofNat 64 0x66758)).toNat % 64)) ∧
      u.getReg .x28 = BitVec.ofNat 64 0x66700 ∧ u.getReg .x29 = s.getMem (BitVec.ofNat 64 0x66758) ∧
      u.getReg .x30 = BitVec.ofNat 64 11920 ∧
      RegsExcept s u [.x14, .x17, .x28, .x29, .x30] ∧ ∀ A, u.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound eP1 code_P1 s hpc trivial, ?_, rfl, rfl, rfl, ?_, fun A => rfl⟩
  · rw [Result.toState_pc]
    show gT 180868 (s.getMem (BitVec.ofNat 64 0x66758) &&& 63#64) = _
    rw [and63, gA_eq _ (Nat.mod_lt _ (by decide))]
  · intro x hx
    cases x <;> first | (exfalso; simp at hx; done) | (simp only [rv_simp, eP1.res]; done) | rfl


theorem s1_spec (u : MachineState) (hpc : u.pc = pcOf 44974) (a1 a2 a3 a5 a6 : Nat)
    (b1 : a1 % 8 = 0 ∧ a1 ≤ 640) (b2 : a2 % 8 = 0 ∧ a2 ≤ 640) (b3 : a3 % 8 = 0 ∧ a3 ≤ 640)
    (b5 : a5 % 8 = 0 ∧ a5 ≤ 640) (b6 : a6 % 8 = 0 ∧ a6 ≤ 640) (L : Word)
    (h11 : u.getReg .x11 = BitVec.ofNat 64 a1) (h12 : u.getReg .x12 = BitVec.ofNat 64 a2)
    (h13 : u.getReg .x13 = BitVec.ofNat 64 a3) (h15 : u.getReg .x15 = BitVec.ofNat 64 a5)
    (h16 : u.getReg .x16 = BitVec.ofNat 64 a6) (h28 : u.getReg .x28 = BitVec.ofNat 64 0x66700)
    (h29 : u.getReg .x29 = L) (h30 : u.getReg .x30 = BitVec.ofNat 64 11920) :
    ∃ v, Steps OuterImages.expandImage u 26 26 v ∧ v.pc = pcOf (44193 + 6 * (64 + L.toNat / 64 % 64)) ∧
      v.getReg .x28 = BitVec.ofNat 64 0x66700 ∧ v.getReg .x30 = BitVec.ofNat 64 11920 ∧
      RegsExcept u v [.x6, .x11, .x12, .x13, .x14, .x15, .x16, .x17] ∧
      ∀ A, v.getMem A = upd (upd (upd (upd (upd (upd u.getMem (a1 + 11920) (u.getMem (nonceAddr 0)))
        (a2 + 11920) (u.getMem (nonceAddr 1))) (a3 + 11920) (u.getMem (nonceAddr 2)))
        (a5 + 11920) (u.getMem (nonceAddr 3))) (a6 + 11920) (u.getMem (nonceAddr 4)))
        (11920 + 368) (u.getMem (nonceAddr 5)) A := by
  refine ⟨_, symRun_sound eS1 code_S1 u hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rv_simp, accessValid_iff, MEMORY_BYTES, ne_eq, BitVec.toNat_eq, BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.toNat_ofNat, eS1.res, h11, h12, h13, h15, h16, h28, h30] <;> (try and_intros) <;> first | trivial | omega
  · rw [Result.toState_pc]
    show gT 182404 ((u.getReg .x29 >>> 6) &&& 63#64) = _
    rw [and63, srl6, h29, gB_eq _ (Nat.mod_lt _ (by decide))]
  · exact h28
  · exact h30
  · intro x hx
    cases x <;> first | (exfalso; simp at hx; done) | (simp only [rv_simp, eS1.res]; done) | rfl
  · intro A
    simp only [Result.toState_getMem, eS1.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval,
      RegFile.get, h11, h12, h13, h15, h16, h28, h30, BitVec.add_zero, BitVec.ofNat_add_ofNat, upd, nonceAddr]


theorem s2_spec (u : MachineState) (hpc : u.pc = pcOf 45000) (a1 a2 a3 a5 a6 : Nat)
    (b1 : a1 % 8 = 0 ∧ a1 ≤ 640) (b2 : a2 % 8 = 0 ∧ a2 ≤ 640) (b3 : a3 % 8 = 0 ∧ a3 ≤ 640)
    (b5 : a5 % 8 = 0 ∧ a5 ≤ 640) (b6 : a6 % 8 = 0 ∧ a6 ≤ 640)
    (h11 : u.getReg .x11 = BitVec.ofNat 64 a1) (h12 : u.getReg .x12 = BitVec.ofNat 64 a2)
    (h13 : u.getReg .x13 = BitVec.ofNat 64 a3) (h15 : u.getReg .x15 = BitVec.ofNat 64 a5)
    (h16 : u.getReg .x16 = BitVec.ofNat 64 a6) (h28 : u.getReg .x28 = BitVec.ofNat 64 0x66700)
    (h30 : u.getReg .x30 = BitVec.ofNat 64 11920) :
    ∃ v, Steps OuterImages.expandImage u 15 15 v ∧ v.pc = pcOf 45015 ∧
      RegsExcept u v [.x6, .x10, .x11, .x12, .x13, .x15, .x16] ∧
      ∀ A, v.getMem A = upd (upd (upd (upd (upd u.getMem (a1 + 11920) (u.getMem (nonceAddr 6)))
        (a2 + 11920) (u.getMem (nonceAddr 7))) (a3 + 11920) (u.getMem (nonceAddr 8)))
        (a5 + 11920) (u.getMem (nonceAddr 9))) (a6 + 11920) (u.getMem (nonceAddr 10)) A := by
  refine ⟨_, symRun_sound eS2 code_S2 u hpc ?_, rfl, ?_, ?_⟩
  · simp only [rv_simp, accessValid_iff, MEMORY_BYTES, ne_eq, BitVec.toNat_eq, BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.toNat_ofNat, eS2.res, h11, h12, h13, h15, h16, h28, h30] <;> (try and_intros) <;> first | trivial | omega
  · intro x hx
    rw [Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp at hx)
  · intro A
    simp only [Result.toState_getMem, eS2.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval,
      RegFile.get, h11, h12, h13, h15, h16, h28, h30, BitVec.add_zero, BitVec.ofNat_add_ofNat, upd, nonceAddr]


/-! ## U16b positional post-pass (words 54970..55019; pad-address table 55020..56043)
`45015: jal 54970`. For each lower layer (1, 2, 3) the post-pass reads the fold-0 parent heap recorded by the grind stub
at `0x700000 + 32 (lay - 1) + 24`, jumps into the table row `rowBase lay + leaf / 2` (`lui/addi a1, a2, a3`) and stores
the recorded nonces (`+16`, `+8`, `+0`: classes 8..15, 4..7, 2..3) at the three pad addresses; `a0 := 0`; `ecall` at
55019 (`post_spec`). -/

theorem code_postTab : CodeAt OuterImages.expandImage (pcOf 54970) (cPostOld ++ cTab)  := OuterImageTransfers.code (b:=54970) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_postTab
theorem code_postOld : CodeAt OuterImages.expandImage (pcOf 54970) cPostOld  := OuterImageTransfers.code (b:=54970) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_postOld
theorem code_tab : CodeAt OuterImages.expandImage (pcOf 55020) cTab  := OuterImageTransfers.code (b:=55020) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_tab
theorem code_prow (r : Nat) (hr : r < 128) : CodeAt OuterImages.expandImage (pcOf (55020 + 8 * r)) (tabRow r)  := by
  have hb : ∀ i : Fin 128,OuterImageTransfers.Clean (55020+8*i.val) (tabRow i.val).length := by decide +kernel
  have h:=hb ⟨r,hr⟩
  dsimp only at h
  exact OuterImageTransfers.code (b:=55020+8*r) h (ClaudeWCT.W9.Machine.Expand.PadWriter.code_prow r hr)
theorem code_post : CodeAt OuterImages.expandImage (pcOf 60662) cPost  := OuterImageTransfers.code (b:=60662) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PadWriter.code_post
theorem code_prow4 (r : Nat) (hr : r < 128) : CodeAt OuterImages.expandImage (pcOf (60150 + 4 * r)) (tabRow4 r)  := by
  have hb : ∀ i : Fin 128,OuterImageTransfers.Clean (60150+4*i.val) (tabRow4 i.val).length := by decide +kernel
  have h:=hb ⟨r,hr⟩
  dsimp only at h
  exact OuterImageTransfers.code (b:=60150+4*r) h (ClaudeWCT.W9.Machine.Expand.PadWriter.code_prow4 r hr)
theorem code_psl (a b : Nat) (ha : 60662 ≤ a) (hb : b ≤ 60734) (hab : a ≤ b) :
    CodeAt OuterImages.expandImage (pcOf a) (psl a b)  := by
  apply OuterImageTransfers.code (b:=a) ?_ (ClaudeWCT.W9.Machine.Expand.PadWriter.code_psl a b ha hb hab)
  unfold OuterImageTransfers.Clean
  right;left
  simp only [psl,List.length_take,List.length_drop]
  omega
theorem pQ0_spec (hpc : s.pc = pcOf 60662) (q : Nat) (hq : q < 64)
    (h : s.getMem (BitVec.ofNat 64 0x700018) = BitVec.ofNat 64 (64 + q)) :
    ∃ t, Steps OuterImages.expandImage s 5 5 t ∧ t.pc = pcOf 60667 ∧ t.getReg .x18 = BitVec.ofNat 64 q ∧
      t.getReg .x31 = BitVec.ofNat 64 0x700000 ∧ RegsExcept s t [.x18, .x28, .x31] ∧ ∀ A, t.getMem A = s.getMem A := by
  have hc := code_psl 60662 60667 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pQ0 hc s hpc (by simp only [pQ0.res]; t3n []), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pQ0.res, E.eval, CmpOp.eval, BinOp.eval]
    t3n [h]
    have e : BitVec.ofNat 64 (64 + q + 18446744073709551552) = BitVec.ofNat 64 q := by rw [ofNat_eq_iff]; omega
    rw [e, show (64#64 : Word) = BitVec.ofNat 64 64 from rfl, pnb_ult q 64 (by omega) (by omega)]
    simp [hq]
  · simp only [Result.toState_getReg, pQ0.res]; t3n [h]
    omega
  · simp only [Result.toState_getReg, pQ0.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pQ0.res, rv_simp] <;> rfl
  · intro A; rfl


theorem pJ0_spec (hpc : s.pc = pcOf 60667) (q : Nat) (hq : q < 64) (h18 : s.getReg .x18 = BitVec.ofNat 64 q) :
    ∃ t, Steps OuterImages.expandImage s 5 5 t ∧ t.pc = pcOf (55020 + 8 * (q)) ∧ t.getReg .x1 = pcOf 60672 ∧
      RegsExcept s t [.x1, .x28, .x29] ∧ ∀ A, t.getMem A = s.getMem A := by
  have hc := code_psl 60667 60672 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pJ0 hc s hpc (by simp only [pJ0.res]; t3n []), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pJ0.res, E.eval, BinOp.eval]
    t3n [h18]
    rw [show q * 32 + 224176 = 0x1000 + 4 * (55020 + 8 * (q)) by omega]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · simp only [Result.toState_getReg, pJ0.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pJ0.res, rv_simp] <;> rfl
  · intro A; rfl


theorem pS0_spec (hpc : s.pc = pcOf 60672) (a1 a2 a3 : Nat) (b1 : a1 % 8 = 0 ∧ 4256 ≤ a1 ∧ a1 + 8 ≤ 26016)
    (b2 : a2 % 8 = 0 ∧ 4256 ≤ a2 ∧ a2 + 8 ≤ 26016) (b3 : a3 % 8 = 0 ∧ 4256 ≤ a3 ∧ a3 + 8 ≤ 26016)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 a1) (h12 : s.getReg .x12 = BitVec.ofNat 64 a2)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 a3) (h31 : s.getReg .x31 = BitVec.ofNat 64 0x700000) (q : Nat)
    (hq : q < 64) (h18 : s.getReg .x18 = BitVec.ofNat 64 q) :
    ∃ t, Steps OuterImages.expandImage s 11 11 t ∧ t.pc = pcOf (60150 + 4 * (q)) ∧ t.getReg .x1 = pcOf 60683 ∧
      t.getReg .x31 = BitVec.ofNat 64 0x700000 ∧ RegsExcept s t [.x1, .x28, .x29, .x30] ∧
      ∀ A, t.getMem A = upd (upd (upd s.getMem a1 (s.getMem (BitVec.ofNat 64 0x700010))) a2
        (s.getMem (BitVec.ofNat 64 0x700008))) a3 (s.getMem (BitVec.ofNat 64 0x700000)) A := by
  have hc := code_psl 60672 60683 (by norm_num) (by norm_num) (by norm_num)
  have hob : pS0.res.obligs s := by
    simp only [pS0.res]; t3n [h11, h12, h13, h31]
    simp only [and_true, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound pS0 hc s hpc hob, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pS0.res, E.eval, BinOp.eval]
    t3n [h18]
    rw [show q * 16 + 244696 = 0x1000 + 4 * (60150 + 4 * (q)) by omega]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · simp only [Result.toState_getReg, pS0.res]; t3n []
  · simp only [Result.toState_getReg, pS0.res]; t3n [h31]
  · intro r hr; simp at hr; cases r <;> simp_all [pS0.res, rv_simp] <;> rfl
  · intro A
    simp only [Result.toState_getMem, pS0.res, upd]
    t3n [h11, h12, h13, h31, Nat.add_zero]


theorem pT0_spec (hpc : s.pc = pcOf 60683) (a4 : Nat) (b4 : a4 % 8 = 0 ∧ 4256 ≤ a4 ∧ a4 + 8 ≤ 26016)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 a4) (h31 : s.getReg .x31 = BitVec.ofNat 64 0x700000) :
    ∃ t, Steps OuterImages.expandImage s 2 2 t ∧ t.pc = pcOf 60685 ∧ RegsExcept s t [.x30] ∧
      ∀ A, t.getMem A = upd s.getMem a4 (s.getMem (BitVec.ofNat 64 0x700100)) A := by
  have hc := code_psl 60683 60685 (by norm_num) (by norm_num) (by norm_num)
  have hob : pT0.res.obligs s := by
    simp only [pT0.res]; t3n [h14, h31]
    simp only [and_true, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound pT0 hc s hpc hob, ?_, ?_, ?_⟩
  · simp [pT0.res, Result.toState_pc, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [pT0.res, rv_simp] <;> rfl
  · intro A
    simp only [Result.toState_getMem, pT0.res, upd]
    t3n [h14, h31, Nat.add_zero]


theorem pQ1_spec (hpc : s.pc = pcOf 60685) (q : Nat) (hq : q < 32)
    (h : s.getMem (BitVec.ofNat 64 0x700038) = BitVec.ofNat 64 (32 + q)) :
    ∃ t, Steps OuterImages.expandImage s 5 5 t ∧ t.pc = pcOf 60690 ∧ t.getReg .x18 = BitVec.ofNat 64 q ∧
      t.getReg .x31 = BitVec.ofNat 64 0x700000 ∧ RegsExcept s t [.x18, .x28, .x31] ∧ ∀ A, t.getMem A = s.getMem A := by
  have hc := code_psl 60685 60690 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pQ1 hc s hpc (by simp only [pQ1.res]; t3n []), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pQ1.res, E.eval, CmpOp.eval, BinOp.eval]
    t3n [h]
    have e : BitVec.ofNat 64 (32 + q + 18446744073709551584) = BitVec.ofNat 64 q := by rw [ofNat_eq_iff]; omega
    rw [e, show (32#64 : Word) = BitVec.ofNat 64 32 from rfl, pnb_ult q 32 (by omega) (by omega)]
    simp [hq]
  · simp only [Result.toState_getReg, pQ1.res]; t3n [h]
    omega
  · simp only [Result.toState_getReg, pQ1.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pQ1.res, rv_simp] <;> rfl
  · intro A; rfl


theorem pJ1_spec (hpc : s.pc = pcOf 60690) (q : Nat) (hq : q < 32) (h18 : s.getReg .x18 = BitVec.ofNat 64 q) :
    ∃ t, Steps OuterImages.expandImage s 5 5 t ∧ t.pc = pcOf (55020 + 8 * (64 + q)) ∧ t.getReg .x1 = pcOf 60695 ∧
      RegsExcept s t [.x1, .x28, .x29] ∧ ∀ A, t.getMem A = s.getMem A := by
  have hc := code_psl 60690 60695 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pJ1 hc s hpc (by simp only [pJ1.res]; t3n []), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pJ1.res, E.eval, BinOp.eval]
    t3n [h18]
    rw [show q * 32 + 226224 = 0x1000 + 4 * (55020 + 8 * (64 + q)) by omega]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · simp only [Result.toState_getReg, pJ1.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pJ1.res, rv_simp] <;> rfl
  · intro A; rfl


theorem pS1_spec (hpc : s.pc = pcOf 60695) (a1 a2 a3 : Nat) (b1 : a1 % 8 = 0 ∧ 4256 ≤ a1 ∧ a1 + 8 ≤ 26016)
    (b2 : a2 % 8 = 0 ∧ 4256 ≤ a2 ∧ a2 + 8 ≤ 26016) (b3 : a3 % 8 = 0 ∧ 4256 ≤ a3 ∧ a3 + 8 ≤ 26016)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 a1) (h12 : s.getReg .x12 = BitVec.ofNat 64 a2)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 a3) (h31 : s.getReg .x31 = BitVec.ofNat 64 0x700000) (q : Nat)
    (hq : q < 32) (h18 : s.getReg .x18 = BitVec.ofNat 64 q) :
    ∃ t, Steps OuterImages.expandImage s 11 11 t ∧ t.pc = pcOf (60150 + 4 * (64 + q)) ∧ t.getReg .x1 = pcOf 60706 ∧
      t.getReg .x31 = BitVec.ofNat 64 0x700000 ∧ RegsExcept s t [.x1, .x28, .x29, .x30] ∧
      ∀ A, t.getMem A = upd (upd (upd s.getMem a1 (s.getMem (BitVec.ofNat 64 0x700030))) a2
        (s.getMem (BitVec.ofNat 64 0x700028))) a3 (s.getMem (BitVec.ofNat 64 0x700020)) A := by
  have hc := code_psl 60695 60706 (by norm_num) (by norm_num) (by norm_num)
  have hob : pS1.res.obligs s := by
    simp only [pS1.res]; t3n [h11, h12, h13, h31]
    simp only [and_true, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound pS1 hc s hpc hob, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pS1.res, E.eval, BinOp.eval]
    t3n [h18]
    rw [show q * 16 + 245720 = 0x1000 + 4 * (60150 + 4 * (64 + q)) by omega]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · simp only [Result.toState_getReg, pS1.res]; t3n []
  · simp only [Result.toState_getReg, pS1.res]; t3n [h31]
  · intro r hr; simp at hr; cases r <;> simp_all [pS1.res, rv_simp] <;> rfl
  · intro A
    simp only [Result.toState_getMem, pS1.res, upd]
    t3n [h11, h12, h13, h31, Nat.add_zero]


theorem pT1_spec (hpc : s.pc = pcOf 60706) (a4 : Nat) (b4 : a4 % 8 = 0 ∧ 4256 ≤ a4 ∧ a4 + 8 ≤ 26016)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 a4) (h31 : s.getReg .x31 = BitVec.ofNat 64 0x700000) :
    ∃ t, Steps OuterImages.expandImage s 2 2 t ∧ t.pc = pcOf 60708 ∧ RegsExcept s t [.x30] ∧
      ∀ A, t.getMem A = upd s.getMem a4 (s.getMem (BitVec.ofNat 64 0x700120)) A := by
  have hc := code_psl 60706 60708 (by norm_num) (by norm_num) (by norm_num)
  have hob : pT1.res.obligs s := by
    simp only [pT1.res]; t3n [h14, h31]
    simp only [and_true, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound pT1 hc s hpc hob, ?_, ?_, ?_⟩
  · simp [pT1.res, Result.toState_pc, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [pT1.res, rv_simp] <;> rfl
  · intro A
    simp only [Result.toState_getMem, pT1.res, upd]
    t3n [h14, h31, Nat.add_zero]


theorem pQ2_spec (hpc : s.pc = pcOf 60708) (q : Nat) (hq : q < 32)
    (h : s.getMem (BitVec.ofNat 64 0x700058) = BitVec.ofNat 64 (32 + q)) :
    ∃ t, Steps OuterImages.expandImage s 5 5 t ∧ t.pc = pcOf 60713 ∧ t.getReg .x18 = BitVec.ofNat 64 q ∧
      t.getReg .x31 = BitVec.ofNat 64 0x700000 ∧ RegsExcept s t [.x18, .x28, .x31] ∧ ∀ A, t.getMem A = s.getMem A := by
  have hc := code_psl 60708 60713 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pQ2 hc s hpc (by simp only [pQ2.res]; t3n []), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pQ2.res, E.eval, CmpOp.eval, BinOp.eval]
    t3n [h]
    have e : BitVec.ofNat 64 (32 + q + 18446744073709551584) = BitVec.ofNat 64 q := by rw [ofNat_eq_iff]; omega
    rw [e, show (32#64 : Word) = BitVec.ofNat 64 32 from rfl, pnb_ult q 32 (by omega) (by omega)]
    simp [hq]
  · simp only [Result.toState_getReg, pQ2.res]; t3n [h]
    omega
  · simp only [Result.toState_getReg, pQ2.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pQ2.res, rv_simp] <;> rfl
  · intro A; rfl


theorem pJ2_spec (hpc : s.pc = pcOf 60713) (q : Nat) (hq : q < 32) (h18 : s.getReg .x18 = BitVec.ofNat 64 q) :
    ∃ t, Steps OuterImages.expandImage s 5 5 t ∧ t.pc = pcOf (55020 + 8 * (96 + q)) ∧ t.getReg .x1 = pcOf 60718 ∧
      RegsExcept s t [.x1, .x28, .x29] ∧ ∀ A, t.getMem A = s.getMem A := by
  have hc := code_psl 60713 60718 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pJ2 hc s hpc (by simp only [pJ2.res]; t3n []), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pJ2.res, E.eval, BinOp.eval]
    t3n [h18]
    rw [show q * 32 + 227248 = 0x1000 + 4 * (55020 + 8 * (96 + q)) by omega]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · simp only [Result.toState_getReg, pJ2.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pJ2.res, rv_simp] <;> rfl
  · intro A; rfl


theorem pS2_spec (hpc : s.pc = pcOf 60718) (a1 a2 a3 : Nat) (b1 : a1 % 8 = 0 ∧ 4256 ≤ a1 ∧ a1 + 8 ≤ 26016)
    (b2 : a2 % 8 = 0 ∧ 4256 ≤ a2 ∧ a2 + 8 ≤ 26016) (b3 : a3 % 8 = 0 ∧ 4256 ≤ a3 ∧ a3 + 8 ≤ 26016)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 a1) (h12 : s.getReg .x12 = BitVec.ofNat 64 a2)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 a3) (h31 : s.getReg .x31 = BitVec.ofNat 64 0x700000) (q : Nat)
    (hq : q < 32) (h18 : s.getReg .x18 = BitVec.ofNat 64 q) :
    ∃ t, Steps OuterImages.expandImage s 11 11 t ∧ t.pc = pcOf (60150 + 4 * (96 + q)) ∧ t.getReg .x1 = pcOf 60729 ∧
      t.getReg .x31 = BitVec.ofNat 64 0x700000 ∧ RegsExcept s t [.x1, .x28, .x29, .x30] ∧
      ∀ A, t.getMem A = upd (upd (upd s.getMem a1 (s.getMem (BitVec.ofNat 64 0x700050))) a2
        (s.getMem (BitVec.ofNat 64 0x700048))) a3 (s.getMem (BitVec.ofNat 64 0x700040)) A := by
  have hc := code_psl 60718 60729 (by norm_num) (by norm_num) (by norm_num)
  have hob : pS2.res.obligs s := by
    simp only [pS2.res]; t3n [h11, h12, h13, h31]
    simp only [and_true, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound pS2 hc s hpc hob, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [pS2.res, E.eval, BinOp.eval]
    t3n [h18]
    rw [show q * 16 + 246232 = 0x1000 + 4 * (60150 + 4 * (96 + q)) by omega]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · simp only [Result.toState_getReg, pS2.res]; t3n []
  · simp only [Result.toState_getReg, pS2.res]; t3n [h31]
  · intro r hr; simp at hr; cases r <;> simp_all [pS2.res, rv_simp] <;> rfl
  · intro A
    simp only [Result.toState_getMem, pS2.res, upd]
    t3n [h11, h12, h13, h31, Nat.add_zero]


theorem pT2_spec (hpc : s.pc = pcOf 60729) (a4 : Nat) (b4 : a4 % 8 = 0 ∧ 4256 ≤ a4 ∧ a4 + 8 ≤ 26016)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 a4) (h31 : s.getReg .x31 = BitVec.ofNat 64 0x700000) :
    ∃ t, Steps OuterImages.expandImage s 4 4 t ∧ t.pc = pcOf 61050 ∧ t.getReg .x10 = 0 ∧ RegsExcept s t [.x10, .x30] ∧
      (∀ A, t.getMem A = upd s.getMem a4 (s.getMem (BitVec.ofNat 64 0x700140)) A) := by
  have hc := code_psl 60729 60733 (by norm_num) (by norm_num) (by norm_num)
  have hob : pT2.res.obligs s := by
    simp only [pT2.res]; t3n [h14, h31]
    simp only [and_true, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound pT2 hc s hpc hob, ?_, ?_, ?_, ?_⟩
  · simp [pT2.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, pT2.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pT2.res, rv_simp] <;> rfl
  · intro A
    simp only [Result.toState_getMem, pT2.res, upd]
    t3n [h14, h31, Nat.add_zero]


theorem prow_spec (r : Nat) (hr : r < 128) (hpc : s.pc = pcOf (55020 + 8 * r)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps OuterImages.expandImage s 7 7 t ∧ t.pc = pcOf ret ∧ t.getReg .x11 = BitVec.ofNat 64 (pa r 0) ∧
      t.getReg .x12 = BitVec.ofNat 64 (pa r 1) ∧ t.getReg .x13 = BitVec.ofNat 64 (pa r 2) ∧
      RegsExcept s t [.x11, .x12, .x13] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound (run_prow r hr) (code_prow r hr) s hpc trivial, ?_, rfl, rfl, rfl, ?_, fun A => rfl⟩
  · simp only [Result.toState_pc, prowRes, E.eval, BinOp.eval, h1]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · intro x hx
    rw [Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp at hx)


theorem prow4_spec (r : Nat) (hr : r < 128) (hpc : s.pc = pcOf (60150 + 4 * r)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps OuterImages.expandImage s 3 3 t ∧ t.pc = pcOf ret ∧ t.getReg .x14 = BitVec.ofNat 64 (pa4 r) ∧
      RegsExcept s t [.x14] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound (run_prow4 r hr) (code_prow4 r hr) s hpc trivial, ?_, rfl, ?_, fun A => rfl⟩
  · simp only [Result.toState_pc, prow4Res, E.eval, BinOp.eval, h1]
    exact SigGolfCandidate.T3M.Search.pcOf_and_max _
  · intro x hx
    rw [Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp at hx)

/-- Memory after the post-pass: the twelve record-table nonces written at the pad addresses of rows `q1`, `64 + q2`,
`96 + q3` (columns: class 8..15, 4..7, 2..3 = folds `H-4, H-3, H-2`; the level-4 table: class 16..31 = fold `H-5`). -/

theorem post_spec (hpc : s.pc = pcOf 60662) (q1 q2 q3 : Nat) (hq1 : q1 < 64) (hq2 : q2 < 32) (hq3 : q3 < 32)
    (h1 : s.getMem (BitVec.ofNat 64 0x700018) = BitVec.ofNat 64 (64 + q1))
    (h2 : s.getMem (BitVec.ofNat 64 0x700038) = BitVec.ofNat 64 (32 + q2))
    (h3 : s.getMem (BitVec.ofNat 64 0x700058) = BitVec.ofNat 64 (32 + q3)) :
    ∃ t, Steps OuterImages.expandImage s 101 101 t ∧ t.pc = pcOf 61050 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x1, .x10, .x11, .x12, .x13, .x14, .x18, .x28, .x29, .x30, .x31] ∧
      (∀ A, t.getMem A = postMem s.getMem q1 q2 q3 A) := by
  have pb := fun r (hr : r < 128) k (hk : k < 3) => pa_bounds r hr k hk
  have pb4 := fun r (hr : r < 128) => pa4_bounds r hr
  -- layer 1
  obtain ⟨u1, s1, p1, x18a, x31a, r1, m1⟩ := pQ0_spec s hpc q1 hq1 h1
  obtain ⟨u2, s2, p2, x1b, r2, m2⟩ := pJ0_spec u1 p1 q1 hq1 x18a
  obtain ⟨u3, s3, p3, x11c, x12c, x13c, r3, m3⟩ := prow_spec u2 q1 (by omega) p2 60672 x1b
  have e3 : u3.getMem = s.getMem := funext fun A => by rw [m3, m2, m1]
  have g31 : u3.getReg .x31 = BitVec.ofNat 64 0x700000 := by rw [r3.get (by decide), r2.get (by decide)]; exact x31a
  have g18 : u3.getReg .x18 = BitVec.ofNat 64 q1 := by rw [r3.get (by decide), r2.get (by decide)]; exact x18a
  obtain ⟨u4, s4, p4, x1d, x31d, r4, m4⟩ := pS0_spec u3 p3 _ _ _ (pb q1 (by omega) 0 (by omega))
    (pb q1 (by omega) 1 (by omega)) (pb q1 (by omega) 2 (by omega)) x11c x12c x13c g31 q1 hq1 g18
  rw [e3] at m4
  obtain ⟨u5, s5, p5, x14e, r5, m5⟩ := prow4_spec u4 q1 (by omega) p4 60683 x1d
  have g31e : u5.getReg .x31 = BitVec.ofNat 64 0x700000 := by rw [r5.get (by decide)]; exact x31d
  obtain ⟨u6, s6, p6, r6, m6⟩ := pT0_spec u5 p5 _ (pb4 q1 (by omega)) x14e g31e
  have hu5 : u5.getMem = upd (upd (upd s.getMem (pa q1 0) (s.getMem (BitVec.ofNat 64 0x700010))) (pa q1 1)
      (s.getMem (BitVec.ofNat 64 0x700008))) (pa q1 2) (s.getMem (BitVec.ofNat 64 0x700000)) :=
    funext fun A => by rw [m5, m4]
  have q5 : ∀ o, o < 0x200 → u5.getMem (BitVec.ofNat 64 (0x700000 + o)) = s.getMem (BitVec.ofNat 64 (0x700000 + o)) :=
    fun o ho => by
      rw [hu5, upd_rec _ _ _ _ (pb q1 (by omega) 2 (by omega)).2.2 ho,
        upd_rec _ _ _ _ (pb q1 (by omega) 1 (by omega)).2.2 ho, upd_rec _ _ _ _ (pb q1 (by omega) 0 (by omega)).2.2 ho]
  have e6 : u6.getMem = upd (upd (upd (upd s.getMem (pa q1 0) (s.getMem (BitVec.ofNat 64 0x700010))) (pa q1 1)
      (s.getMem (BitVec.ofNat 64 0x700008))) (pa q1 2) (s.getMem (BitVec.ofNat 64 0x700000)))
      (pa4 q1) (s.getMem (BitVec.ofNat 64 0x700100)) := by
    funext A
    rw [m6, show (0x700100 : Nat) = 0x700000 + 0x100 from rfl, q5 0x100 (by norm_num), hu5]
  have q6 : ∀ o, o < 0x200 → u6.getMem (BitVec.ofNat 64 (0x700000 + o)) = s.getMem (BitVec.ofNat 64 (0x700000 + o)) :=
    fun o ho => by
      rw [e6, upd_rec _ _ _ _ (pb4 q1 (by omega)).2.2 ho, upd_rec _ _ _ _ (pb q1 (by omega) 2 (by omega)).2.2 ho,
        upd_rec _ _ _ _ (pb q1 (by omega) 1 (by omega)).2.2 ho, upd_rec _ _ _ _ (pb q1 (by omega) 0 (by omega)).2.2 ho]
  -- layer 2
  obtain ⟨v1, t1, pv1, y18a, y31a, rv1, mv1⟩ := pQ1_spec u6 p6 q2 hq2
    (by rw [show (0x700038 : Nat) = 0x700000 + 0x38 from rfl, q6 0x38 (by norm_num)]; exact h2)
  obtain ⟨v2, t2, pv2, y1b, rv2, mv2⟩ := pJ1_spec v1 pv1 q2 hq2 y18a
  obtain ⟨v3, t3, pv3, y11c, y12c, y13c, rv3, mv3⟩ := prow_spec v2 (64 + q2) (by omega) pv2 60695 y1b
  have f3 : v3.getMem = u6.getMem := funext fun A => by rw [mv3, mv2, mv1]
  have h31v : v3.getReg .x31 = BitVec.ofNat 64 0x700000 := by rw [rv3.get (by decide), rv2.get (by decide)]; exact y31a
  have h18v : v3.getReg .x18 = BitVec.ofNat 64 q2 := by rw [rv3.get (by decide), rv2.get (by decide)]; exact y18a
  obtain ⟨v4, t4, pv4, y1d, y31d, rv4, mv4⟩ := pS1_spec v3 pv3 _ _ _ (pb (64 + q2) (by omega) 0 (by omega))
    (pb (64 + q2) (by omega) 1 (by omega)) (pb (64 + q2) (by omega) 2 (by omega)) y11c y12c y13c h31v q2 hq2 h18v
  rw [f3, show (0x700030 : Nat) = 0x700000 + 0x30 from rfl, show (0x700028 : Nat) = 0x700000 + 0x28 from rfl,
    show (0x700020 : Nat) = 0x700000 + 0x20 from rfl, q6 0x30 (by norm_num), q6 0x28 (by norm_num), q6 0x20 (by norm_num)] at mv4
  obtain ⟨v5, t5, pv5, y14e, rv5, mv5⟩ := prow4_spec v4 (64 + q2) (by omega) pv4 60706 y1d
  have h31e : v5.getReg .x31 = BitVec.ofNat 64 0x700000 := by rw [rv5.get (by decide)]; exact y31d
  obtain ⟨v6, t6, pv6, rv6, mv6⟩ := pT1_spec v5 pv5 _ (pb4 (64 + q2) (by omega)) y14e h31e
  have hv5 : v5.getMem = upd (upd (upd u6.getMem (pa (64 + q2) 0) (s.getMem (BitVec.ofNat 64 (0x700000 + 0x30))))
      (pa (64 + q2) 1) (s.getMem (BitVec.ofNat 64 (0x700000 + 0x28)))) (pa (64 + q2) 2)
      (s.getMem (BitVec.ofNat 64 (0x700000 + 0x20))) := funext fun A => by rw [mv5, mv4]
  have q11 : ∀ o, o < 0x200 → v5.getMem (BitVec.ofNat 64 (0x700000 + o)) = s.getMem (BitVec.ofNat 64 (0x700000 + o)) :=
    fun o ho => by
      rw [hv5, upd_rec _ _ _ _ (pb (64 + q2) (by omega) 2 (by omega)).2.2 ho,
        upd_rec _ _ _ _ (pb (64 + q2) (by omega) 1 (by omega)).2.2 ho,
        upd_rec _ _ _ _ (pb (64 + q2) (by omega) 0 (by omega)).2.2 ho, q6 o ho]
  have f6 : v6.getMem = upd (upd (upd (upd u6.getMem (pa (64 + q2) 0) (s.getMem (BitVec.ofNat 64 (0x700000 + 0x30))))
      (pa (64 + q2) 1) (s.getMem (BitVec.ofNat 64 (0x700000 + 0x28)))) (pa (64 + q2) 2)
      (s.getMem (BitVec.ofNat 64 (0x700000 + 0x20)))) (pa4 (64 + q2)) (s.getMem (BitVec.ofNat 64 (0x700000 + 0x120))) := by
    funext A
    rw [mv6, show (0x700120 : Nat) = 0x700000 + 0x120 from rfl, q11 0x120 (by norm_num), hv5]
  have q12 : ∀ o, o < 0x200 → v6.getMem (BitVec.ofNat 64 (0x700000 + o)) = s.getMem (BitVec.ofNat 64 (0x700000 + o)) :=
    fun o ho => by
      rw [f6, upd_rec _ _ _ _ (pb4 (64 + q2) (by omega)).2.2 ho, upd_rec _ _ _ _ (pb (64 + q2) (by omega) 2 (by omega)).2.2 ho,
        upd_rec _ _ _ _ (pb (64 + q2) (by omega) 1 (by omega)).2.2 ho,
        upd_rec _ _ _ _ (pb (64 + q2) (by omega) 0 (by omega)).2.2 ho, q6 o ho]
  -- layer 3
  obtain ⟨w1, k1, pw1, z18a, z31a, rw1, mw1⟩ := pQ2_spec v6 pv6 q3 hq3
    (by rw [show (0x700058 : Nat) = 0x700000 + 0x58 from rfl, q12 0x58 (by norm_num)]; exact h3)
  obtain ⟨w2, k2, pw2, z1b, rw2, mw2⟩ := pJ2_spec w1 pw1 q3 hq3 z18a
  obtain ⟨w3, k3, pw3, z11c, z12c, z13c, rw3, mw3⟩ := prow_spec w2 (96 + q3) (by omega) pw2 60718 z1b
  have d3 : w3.getMem = v6.getMem := funext fun A => by rw [mw3, mw2, mw1]
  have i31 : w3.getReg .x31 = BitVec.ofNat 64 0x700000 := by rw [rw3.get (by decide), rw2.get (by decide)]; exact z31a
  have i18 : w3.getReg .x18 = BitVec.ofNat 64 q3 := by rw [rw3.get (by decide), rw2.get (by decide)]; exact z18a
  obtain ⟨w4, k4, pw4, z1d, z31d, rw4, mw4⟩ := pS2_spec w3 pw3 _ _ _ (pb (96 + q3) (by omega) 0 (by omega))
    (pb (96 + q3) (by omega) 1 (by omega)) (pb (96 + q3) (by omega) 2 (by omega)) z11c z12c z13c i31 q3 hq3 i18
  rw [d3, show (0x700050 : Nat) = 0x700000 + 0x50 from rfl, show (0x700048 : Nat) = 0x700000 + 0x48 from rfl,
    show (0x700040 : Nat) = 0x700000 + 0x40 from rfl, q12 0x50 (by norm_num), q12 0x48 (by norm_num), q12 0x40 (by norm_num)] at mw4
  obtain ⟨w5, k5, pw5, z14e, rw5, mw5⟩ := prow4_spec w4 (96 + q3) (by omega) pw4 60729 z1d
  have i31e : w5.getReg .x31 = BitVec.ofNat 64 0x700000 := by rw [rw5.get (by decide)]; exact z31d
  obtain ⟨t, st, pt, x10t, rt, mt⟩ := pT2_spec w5 pw5 _ (pb4 (96 + q3) (by omega)) z14e i31e
  have hw5 : w5.getMem = upd (upd (upd v6.getMem (pa (96 + q3) 0) (s.getMem (BitVec.ofNat 64 (0x700000 + 0x50))))
      (pa (96 + q3) 1) (s.getMem (BitVec.ofNat 64 (0x700000 + 0x48)))) (pa (96 + q3) 2)
      (s.getMem (BitVec.ofNat 64 (0x700000 + 0x40))) := funext fun A => by rw [mw5, mw4]
  have q17 : w5.getMem (BitVec.ofNat 64 (0x700000 + 0x140)) = s.getMem (BitVec.ofNat 64 (0x700000 + 0x140)) := by
    rw [hw5, upd_rec _ _ _ _ (pb (96 + q3) (by omega) 2 (by omega)).2.2 (by norm_num),
      upd_rec _ _ _ _ (pb (96 + q3) (by omega) 1 (by omega)).2.2 (by norm_num),
      upd_rec _ _ _ _ (pb (96 + q3) (by omega) 0 (by omega)).2.2 (by norm_num), q12 0x140 (by norm_num)]
  refine ⟨t, Steps.of_eq (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (t1.trans (t2.trans (t3.trans
    (t4.trans (t5.trans (t6.trans (k1.trans (k2.trans (k3.trans (k4.trans (k5.trans st))))))))))))))))) rfl rfl,
    pt, x10t, ?_, ?_⟩
  · exact ((((((((((((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans rv1).trans rv2).trans rv3).trans
      rv4).trans rv5).trans rv6).trans rw1).trans rw2).trans rw3).trans rw4).trans (rw5.trans rt)).mono (by decide)
  · intro A
    rw [mt, show (0x700140 : Nat) = 0x700000 + 0x140 from rfl, q17, hw5, f6, e6]
    rfl

theorem pad_pre (s : MachineState) (hpc : s.pc = pcOf 44961) :
    ∃ t, Steps OuterImages.expandImage s 66 66 t ∧ t.pc = pcOf 45015 ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30] ∧
      ∀ A, t.getMem A = padMem s.getMem A := by
  obtain ⟨u, su, up, u28, u29, u30, ru, mu⟩ := p1_spec s hpc
  have hA : leafW s.getMem % 64 < 128 := by omega
  obtain ⟨v, sv, vp, v11, v12, v13, v15, v16, rv, mv⟩ := row_spec _ hA u up
  rw [if_pos (Nat.mod_lt _ (by decide))] at vp
  have bA := fun i (hi : i < 5) => offR_bounds _ hA i hi
  have rv' := ru.trans rv
  obtain ⟨w, sw, wp, w28, w30, rw', mw⟩ := s1_spec v vp _ _ _ _ _
    ⟨(bA 0 (by decide)).1, (bA 0 (by decide)).2.2⟩ ⟨(bA 1 (by decide)).1, (bA 1 (by decide)).2.2⟩
    ⟨(bA 2 (by decide)).1, (bA 2 (by decide)).2.2⟩ ⟨(bA 3 (by decide)).1, (bA 3 (by decide)).2.2⟩
    ⟨(bA 4 (by decide)).1, (bA 4 (by decide)).2.2⟩ (s.getMem (BitVec.ofNat 64 0x66758))
    v11 v12 v13 v15 v16
    (by rw [rv .x28 (by simp)]; exact u28) (by rw [rv .x29 (by simp)]; exact u29)
    (by rw [rv .x30 (by simp)]; exact u30)
  have hB : 64 + leafW s.getMem / 64 % 64 < 128 := by omega
  obtain ⟨x, sx, xp, x11, x12, x13, x15, x16, rx, mx⟩ := row_spec _ hB w wp
  rw [if_neg (by omega)] at xp
  have bB := fun i (hi : i < 5) => offR_bounds _ hB i hi
  obtain ⟨t, st, tp, rt, mt⟩ := s2_spec x xp _ _ _ _ _
    ⟨(bB 0 (by decide)).1, (bB 0 (by decide)).2.2⟩ ⟨(bB 1 (by decide)).1, (bB 1 (by decide)).2.2⟩
    ⟨(bB 2 (by decide)).1, (bB 2 (by decide)).2.2⟩ ⟨(bB 3 (by decide)).1, (bB 3 (by decide)).2.2⟩
    ⟨(bB 4 (by decide)).1, (bB 4 (by decide)).2.2⟩
    x11 x12 x13 x15 x16 (by rw [rx .x28 (by simp)]; exact w28) (by rw [rx .x30 (by simp)]; exact w30)
  refine ⟨t, Steps.of_eq (su.trans (sv.trans (sw.trans (sx.trans st)))) rfl rfl, tp, ?_, ?_⟩
  · exact (((ru.trans rv).trans rw').trans (rx.trans rt)).mono (by simp)
  · intro A
    have hx' : x.getMem = w.getMem := funext mx
    have hv : ∀ B, v.getMem B = s.getMem B := fun B => (mv B).trans (mu B)
    have hv' : v.getMem = s.getMem := funext hv
    have b0 := (offR_bounds _ hA 0 (by decide)).2.2
    have b1 := (offR_bounds _ hA 1 (by decide)).2.2
    have b2 := (offR_bounds _ hA 2 (by decide)).2.2
    have b3 := (offR_bounds _ hA 3 (by decide)).2.2
    have b4 := (offR_bounds _ hA 4 (by decide)).2.2
    have hn : ∀ k, k < 11 → w.getMem (nonceAddr k) = s.getMem (nonceAddr k) := by
      intro k hk
      rw [mw, upd_nonce _ _ _ _ (by omega) hk, upd_nonce _ _ _ _ (by omega) hk, upd_nonce _ _ _ _ (by omega) hk,
        upd_nonce _ _ _ _ (by omega) hk, upd_nonce _ _ _ _ (by omega) hk, upd_nonce _ _ _ _ (by omega) hk, hv]
    have hw : w.getMem = upd (upd (upd (upd (upd (upd s.getMem (offA (leafW s.getMem % 64) 0 + 11920)
        (s.getMem (nonceAddr 0))) (offA (leafW s.getMem % 64) 1 + 11920) (s.getMem (nonceAddr 1)))
        (offA (leafW s.getMem % 64) 2 + 11920) (s.getMem (nonceAddr 2)))
        (offA (leafW s.getMem % 64) 3 + 11920) (s.getMem (nonceAddr 3)))
        (offA (leafW s.getMem % 64) 4 + 11920) (s.getMem (nonceAddr 4))) (11920 + 368)
        (s.getMem (nonceAddr 5)) := by
      funext B
      rw [mw, hv']
      rfl
    rw [mt, hx', hn 6 (by decide), hn 7 (by decide), hn 8 (by decide), hn 9 (by decide), hn 10 (by decide), hw]
    rfl

/-- The pad writer leaves the grind-stub record table (`0x700000 ..`) alone. -/

theorem pad_spec (s : MachineState) (hpc : s.pc = pcOf 44961) (q1 q2 q3 : Nat) (hq1 : q1 < 64) (hq2 : q2 < 32)
    (hq3 : q3 < 32) (h1 : s.getMem (BitVec.ofNat 64 0x700018) = BitVec.ofNat 64 (64 + q1))
    (h2 : s.getMem (BitVec.ofNat 64 0x700038) = BitVec.ofNat 64 (32 + q2))
    (h3 : s.getMem (BitVec.ofNat 64 0x700058) = BitVec.ofNat 64 (32 + q3)) :
    ∃ t, Steps OuterImages.expandImage s 168 168 t ∧ t.pc = pcOf 61050 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x28, .x29, .x30, .x31] ∧
      (∀ A, t.getMem A = postMem (padMem s.getMem) q1 q2 q3 A) := by
  obtain ⟨u, su, up, ru, mu⟩ := pad_pre s hpc
  have hu : u.getMem = padMem s.getMem := funext mu
  have sj := symRun_sound eJ45015 code_J45015 u up trivial
  have hm : (eJ45015.res.toState u).getMem = padMem s.getMem := by rw [← hu]; rfl
  have rj : RegsExcept u (eJ45015.res.toState u) [] := by
    intro r hr
    cases r <;> first | (simp only [rv_simp, eJ45015.res]; done) | rfl
  obtain ⟨t, st, tp, t10, rt, mt⟩ := post_spec (eJ45015.res.toState u)
    (by simp only [rv_simp, eJ45015.res] <;> decide) q1 q2 q3 hq1 hq2 hq3
    (by rw [hm, padMem_far _ 0x700018 (by norm_num) (by norm_num)]; exact h1)
    (by rw [hm, padMem_far _ 0x700038 (by norm_num) (by norm_num)]; exact h2)
    (by rw [hm, padMem_far _ 0x700058 (by norm_num) (by norm_num)]; exact h3)
  refine ⟨t, Steps.of_eq (su.trans (sj.trans st)) rfl rfl, tp, t10, ?_, fun A => (mt A).trans (by rw [hm])⟩
  exact ((ru.trans rj).trans rt).mono (by decide)

/-- From the exit hook `54174: jal 44961`: 168 steps to the `ecall` at 60732. -/

theorem pad_hook (s : MachineState) (hpc : s.pc = pcOf 54174) (q1 q2 q3 : Nat) (hq1 : q1 < 64) (hq2 : q2 < 32)
    (hq3 : q3 < 32) (h1 : s.getMem (BitVec.ofNat 64 0x700018) = BitVec.ofNat 64 (64 + q1))
    (h2 : s.getMem (BitVec.ofNat 64 0x700038) = BitVec.ofNat 64 (32 + q2))
    (h3 : s.getMem (BitVec.ofNat 64 0x700058) = BitVec.ofNat 64 (32 + q3)) :
    ∃ t, Steps OuterImages.expandImage s 169 169 t ∧ t.pc = pcOf 61050 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x28, .x29, .x30, .x31] ∧
      (∀ A, t.getMem A = postMem (padMem s.getMem) q1 q2 q3 A) := by
  have s1 := symRun_sound eHook code_hook s hpc trivial
  obtain ⟨t, st, tp, t10, rt, mt⟩ := pad_spec (eHook.res.toState s) (by simp only [rv_simp, eHook.res] <;> decide)
    q1 q2 q3 hq1 hq2 hq3 h1 h2 h3
  refine ⟨t, Steps.of_eq (s1.trans st) rfl rfl, tp, t10, ?_, fun A => (mt A).trans ?_⟩
  · intro r hr
    rw [rt r hr]
    cases r <;> first | (simp only [rv_simp, eHook.res]; done) | rfl
  · rfl




#print axioms pad_hook
end OuterPadWriter
