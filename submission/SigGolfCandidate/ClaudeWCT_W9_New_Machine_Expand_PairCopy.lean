import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_CompactLoop

/-! # Pairing stage 1: the lower-chain pair copy block (expand words 48000 .. 48017)

The witness constructor's lower-layer chain copy (`jal ra,48000` at 42241 / 42414 / 42563, with `a0` = the staging
chain area of the layer (43 blocks of 64 bytes, chain 42 first, value at block offset 48) and `a1` = the final paired
chain area) runs

```
48000  addi a2,zero,21
48001  ld t1,48(a0);  sd t1,88(a1)     -- F chain 2p+2's value  -> pair offset 88
       ld t1,56(a0);  sd t1,96(a1)
       ld t1,112(a0); sd t1,16(a1)     -- G chain 2p+1's value  -> pair offset 16
       ld t1,120(a0); sd t1,24(a1)
       addi a0,a0,128; addi a1,a1,104; addi a2,a2,-1; bne a2,zero,48001
48013  ld t1,48(a0); sd t1,48(a1); ld t1,56(a0); sd t1,56(a1)   -- chain 0's value at offset 48 of its F block
       jalr zero,0(ra)
```

It writes only value words; the pair gaps keep the constructor's zero fill. -/

namespace ClaudeWCT.W9.Machine.Expand.PairCopy
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC ofNat_sub_one)
set_option linter.unusedSimpArgs false

/-- The whole block at 48000 (18 words). -/
def cPCode : List (BitVec 32) := cPC0 ++ cPCL ++ cPCT
theorem cPCode_length : cPCode.length = 18 := rfl
sym_block RPC0 := symRun cfgC cPC0 (pcOf 48000) 40
sym_block RPCL := symRun cfgC cPCL (pcOf 48001) 40
sym_block RPCT := symRun cfgC cPCT (pcOf 48013) 40

/-- Source offset (in a 128-byte staging block pair) of a written pair offset. -/
def srcOff (r : Nat) : Nat := if r = 16 then 112 else if r = 24 then 120 else if r = 88 then 48 else 56
def isVal (r : Nat) : Prop := r = 16 ∨ r = 24 ∨ r = 88 ∨ r = 96
instance (r : Nat) : Decidable (isVal r) := by unfold isVal; infer_instance
/-- Memory after `i` loop iterations. -/
def pcMem (M : Nat → Word) (src dst i A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 104 * i ∧ isVal ((A - dst) % 104) then
    M (src + 128 * ((A - dst) / 104) + srcOff ((A - dst) % 104)) else M A
/-- Memory after the whole block (21 pairs and chain 0's value). -/
def pairCopyMem (M : Nat → Word) (src dst A : Nat) : Word :=
  if A = dst + 104 * 21 + 48 then M (src + 128 * 21 + 48)
  else if A = dst + 104 * 21 + 56 then M (src + 128 * 21 + 56)
  else pcMem M src dst 21 A

section
variable {im : Image} (hc : Code im)
include hc
set_option maxRecDepth 20000 in
theorem pc_iter (s : MachineState) (hpc : s.pc = pcOf 48001) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1)) (hn : n + 1 < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 128 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 104 ≤ MEMORY_BYTES)
    (hov : dst + 104 ≤ src) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if n = 0 then pcOf 48013 else pcOf 48001) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src + 128) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst + 104) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst + 24 then s.getMem (BitVec.ofNat 64 (src + 120))
        else if A = dst + 16 then s.getMem (BitVec.ofNat 64 (src + 112))
        else if A = dst + 96 then s.getMem (BitVec.ofNat 64 (src + 56))
        else if A = dst + 88 then s.getMem (BitVec.ofNat 64 (src + 48))
        else s.getMem (BitVec.ofNat 64 A)) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RPCL hc.cL s hpc (by
    simp [RPCL.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RPCL.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RPCL.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RPCL.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RPCL.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    cases r <;> simp_all [rv_simp, RPCL.res] <;> rfl
  · intro A hA
    have k24 := ofNat_inj hA (show dst + 24 < 2 ^ 64 by omega)
    have k16 := ofNat_inj hA (show dst + 16 < 2 ^ 64 by omega)
    have k96 := ofNat_inj hA (show dst + 96 < 2 ^ 64 by omega)
    have k88 := ofNat_inj hA (show dst + 88 < 2 ^ 64 by omega)
    simp only [Result.toState_getMem, RPCL.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, h10, h11,
      ofNat_add_ofNat, k24, k16, k96, k88]

structure PCInv (s : MachineState) (src dst i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < 21 then pcOf 48001 else pcOf 48013)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (src + 128 * i)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 104 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (21 - i)
  regs : RegsExcept s t [.x6, .x10, .x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = pcMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst i A

theorem pc_loop (s : MachineState) (hpc : s.pc = pcOf 48001) (src dst : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 21)
    (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∀ i, i ≤ 21 → ∃ t, Steps im s (12 * i) (12 * i) t ∧ PCInv s src dst i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos (by omega)], by simpa using h10, by simpa using h11,
      by simpa using h12, fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold pcMem; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 48001 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u10, u11, u12, ru, mu⟩ := pc_iter hc t hpc' (src + 128 * i) (dst + 104 * i) (20 - i)
      hI.x10 hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : 20 - i = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u10, show src + 128 * i + 128 = src + 128 * (i + 1) by ring]
    · rw [u11, show dst + 104 * i + 104 = dst + 104 * (i + 1) by ring]
    · rw [u12, show 20 - i = 21 - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      have hsrc : ∀ x, x < 128 → t.getMem (BitVec.ofNat 64 (src + 128 * i + x)) =
          s.getMem (BitVec.ofNat 64 (src + 128 * i + x)) := fun x hx => by
        rw [hI.mem _ (by omega)]; unfold pcMem; rw [if_neg (by omega)]
      rw [mu A hA, hsrc 120 (by omega), hsrc 112 (by omega), hsrc 56 (by omega), hsrc 48 (by omega), hI.mem A hA]
      unfold pcMem
      by_cases hn : dst + 104 * i ≤ A ∧ A < dst + 104 * i + 104
      · have hq : (A - dst) / 104 = i := by omega
        have hr : (A - dst) % 104 = A - (dst + 104 * i) := by omega
        by_cases a24 : A = dst + 104 * i + 24
        · subst a24; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a24]
        by_cases a16 : A = dst + 104 * i + 16
        · subst a16; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a16]
        by_cases a96 : A = dst + 104 * i + 96
        · subst a96; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a96]
        by_cases a88 : A = dst + 104 * i + 88
        · subst a88; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a88, if_neg (fun h => by unfold isVal at h; omega), if_neg (fun h => by unfold isVal at h; omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        by_cases hin : dst ≤ A ∧ A < dst + 104 * i ∧ isVal ((A - dst) % 104)
        · rw [if_pos hin, if_pos ⟨hin.1, by omega, hin.2.2⟩]
        · rw [if_neg hin, if_neg (fun h => hin ⟨h.1, by omega, h.2.2⟩)]

set_option maxRecDepth 100000 in
/-- The whole pair copy block: from 48000 back to `ret` (`ra`), 1 + 12 * 21 + 5 = 258 steps. -/
theorem pairCopy_spec (s : MachineState) (hpc : s.pc = pcOf 48000) (src dst ret : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h1 : s.getReg .x1 = pcOf ret)
    (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∃ t, Steps im s 258 258 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = pairCopyMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u12, ur, uf⟩ : ∃ u, Steps im s 1 1 u ∧ u.pc = pcOf 48001 ∧
      u.getReg .x12 = BitVec.ofNat 64 21 ∧ RegsExcept s u [.x12] ∧ Frame s u (fun _ => False) := by
    refine ⟨_, symRun_sound RPC0 hc.c0 s hpc (by simp [RPC0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [RPC0.res, E.eval]
    · simp [RPC0.res, rv_simp] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [RPC0.res, rv_simp] <;> rfl
    · intro A _ _; simp [RPC0.res, rv_simp]
  obtain ⟨t, st, hI⟩ := pc_loop hc u pu src dst (by rw [ur.get (by simp)]; exact h10)
    (by rw [ur.get (by simp)]; exact h11) u12 hs hs' hd hov 21 le_rfl
  have tpc : t.pc = pcOf 48013 := by rw [hI.pc, if_neg (by omega)]
  have hobl : Oblig.all t RPCT.res.st.obl := by
    simp [RPCT.res, rv_simp, accessValid_iff, hI.x10, hI.x11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; omega
  have sT := symRun_sound RPCT hc.cT t tpc hobl
  have hmu : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => uf.get hA (by simp)
  refine ⟨_, ((su.trans st).trans sT).of_eq (by simp [RPCT.res]) (by simp [RPCT.res]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RPCT.res, E.eval]
    rw [hI.regs.get (by simp), ur.get (by simp), h1]
    exact pcOf_and_not1 ret
  · have r3 : RegsExcept t (RPCT.res.toState t) [.x6] := by
      intro r hr; simp at hr; cases r <;> simp_all [RPCT.res, rv_simp] <;> rfl
    exact ((ur.trans hI.regs).trans r3).mono (by simp)
  · intro A hA
    have k48 := ofNat_inj hA (show dst + 104 * 21 + 48 < 2 ^ 64 by omega)
    have k56 := ofNat_inj hA (show dst + 104 * 21 + 56 < 2 ^ 64 by omega)
    have e : ∀ x, x < 128 → t.getMem (BitVec.ofNat 64 (src + 128 * 21 + x)) =
        s.getMem (BitVec.ofNat 64 (src + 128 * 21 + x)) := fun x hx => by
      rw [hI.mem _ (by omega)]; unfold pcMem; rw [if_neg (by omega)]; exact hmu _ (by omega)
    simp only [Result.toState_getMem, RPCT.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, hI.x10,
      hI.x11, ofNat_add_ofNat, k48, k56]
    rw [show src + 128 * 21 + 56 = src + 128 * 21 + 56 from rfl, e 56 (by omega), e 48 (by omega), hI.mem A hA]
    unfold pairCopyMem pcMem
    have hso : srcOff ((A - dst) % 104) ≤ 120 := by unfold srcOff; split_ifs <;> omega
    split_ifs <;> first | rfl | (exact hmu _ (by omega)) | omega
end
end ClaudeWCT.W9.Machine.Expand.PairCopy
