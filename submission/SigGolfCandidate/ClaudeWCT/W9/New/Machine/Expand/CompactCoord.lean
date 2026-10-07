import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
def cfgC : Config := { noAlias := true }
def coordAt (k : Nat) : Nat := 41121 + 111 * k
def sibAt (k l : Nat) : Nat := coordAt k + 13 + 14 * l
def sibLen (l : Nat) : Nat := if l < 6 then 14 else 12
def cStart : List (BitVec 32) := [5431,0x84050513,2098615,361875,1591,0x48060613,0x7e1000ef]
def cRegs : List (BitVec 32) := [2098231,263187,5303,0x84048493,0xffa937,0xa0090913]
def cRow : List (BitVec 32) := [66712467,4428691,7932467]
def cStep : List (BitVec 32) := [0x40040413,939820179]
def cFinal : List (BitVec 32) := [13623,0xc4050513,9655,0x7c058593,1591,0x6b360613,16777455]
def cHalt : List (BitVec 32) := [1049235,1299,115]
def cCopy : List (BitVec 32) := [340739,6664227,8717587,8750483,0xfff60613,0xfe0616e3,32871]
def cZero : List (BitVec 32) := [372771,8750483,0xfff60613,0xfe061ae3,32871]
def cHeads : List (List (BitVec 32)) :=[[0x6003303,217875,0x7f37993,296339,41944595,0x7cd000ef],[0x6803303,217875,0x7f37993,296339,41944595,0x611000ef],[0x6803303,22237971,0x7f37993,296339,41944595,0x455000ef],[0x6803303,59986707,0x7f37993,296339,41944595,697303279],[0x7003303,217875,0x7f37993,296339,41944595,0xdd000ef],[0x7003303,22237971,0x7f37993,296339,41944595,0x720000ef],[0x7003303,59986707,0x7f37993,296339,41944595,0x564000ef],[0x7803303,217875,0x7f37993,296339,41944595,981467375],[0x7803303,22237971,0x7f37993,296339,41944595,515899631]]
def cHead (k : Nat) : List (BitVec 32) := cHeads.getD k []
def cMids : List (List (BitVec 32)) :=[[470025491,335840659,75499027,0x7a1000ef],[470025491,335840659,75499027,0x5e5000ef],[470025491,335840659,75499027,0x429000ef],[470025491,335840659,75499027,651165935],[470025491,335840659,75499027,0xb1000ef],[470025491,335840659,75499027,0x6f4000ef],[470025491,335840659,75499027,0x538000ef],[470025491,335840659,75499027,935330031],[470025491,335840659,75499027,469762287]]
def cMid (k : Nat) : List (BitVec 32) := cMids.getD k []
def cSibs : List (List (BitVec 32)) :=[[679427,29658675,647059,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,0xc06be83,0xc86bf03,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,0x806be83,0x886bf03,31338531,32388131],[0xaa5e03,29658675,5889939,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,67550851,75939587,31338531,32388131],[0xca5e03,29658675,6938515,2084755,6264467,5218195,0xdf8fb3,32769715,441987,8830723,31338531,32388131]]
def cSib (l : Nat) : List (BitVec 32) := cSibs.getD l []
section code
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem code_cStart : CodeAt im (pcOf 41108) cStart := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRegs : CodeAt im (pcOf 41115) cRegs := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cFinal : CodeAt im (pcOf 42120) cFinal := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHalt : CodeAt im (pcOf 42127) cHalt := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cCopy : CodeAt im (pcOf 42130) cCopy := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cZero : CodeAt im (pcOf 42137) cZero := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_copyRet : CodeAt im (pcOf 42136) [0x8067] := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_zeroRet : CodeAt im (pcOf 42141) [0x8067] := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHead (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k)) (cHead k) := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cMid (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 6)) (cMid k) := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRow (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 10)) cRow := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cStep (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 109)) cStep := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cSib (k l : Nat) (hk : k < 9) (hl : l < 7) : CodeAt im (pcOf (sibAt k l)) (cSib l) := by
  interval_cases k <;> interval_cases l <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
end code
sym_block RStart := symRun cfgC cStart (pcOf 41108) 40
sym_block RRegs := symRun cfgC cRegs (pcOf 41115) 40
sym_block RFinal := symRun cfgC cFinal (pcOf 42120) 40
sym_block RHalt := symRun cfgC cHalt (pcOf 42127) 40
sym_block RCopy := symRun cfgC cCopy (pcOf 42130) 40
sym_block RCopyRet := symRun cfgC [0x8067] (pcOf 42136) 40
sym_block RZero := symRun cfgC cZero (pcOf 42137) 40
sym_block RZeroRet := symRun cfgC [0x8067] (pcOf 42141) 40
sym_block RHead0 := symRun cfgC (cHead 0) (pcOf (coordAt 0)) 40
sym_block RMid0 := symRun cfgC (cMid 0) (pcOf (coordAt 0 + 6)) 40
sym_block RHead1 := symRun cfgC (cHead 1) (pcOf (coordAt 1)) 40
sym_block RMid1 := symRun cfgC (cMid 1) (pcOf (coordAt 1 + 6)) 40
sym_block RHead2 := symRun cfgC (cHead 2) (pcOf (coordAt 2)) 40
sym_block RMid2 := symRun cfgC (cMid 2) (pcOf (coordAt 2 + 6)) 40
sym_block RHead3 := symRun cfgC (cHead 3) (pcOf (coordAt 3)) 40
sym_block RMid3 := symRun cfgC (cMid 3) (pcOf (coordAt 3 + 6)) 40
sym_block RHead4 := symRun cfgC (cHead 4) (pcOf (coordAt 4)) 40
sym_block RMid4 := symRun cfgC (cMid 4) (pcOf (coordAt 4 + 6)) 40
sym_block RHead5 := symRun cfgC (cHead 5) (pcOf (coordAt 5)) 40
sym_block RMid5 := symRun cfgC (cMid 5) (pcOf (coordAt 5 + 6)) 40
sym_block RHead6 := symRun cfgC (cHead 6) (pcOf (coordAt 6)) 40
sym_block RMid6 := symRun cfgC (cMid 6) (pcOf (coordAt 6 + 6)) 40
sym_block RHead7 := symRun cfgC (cHead 7) (pcOf (coordAt 7)) 40
sym_block RMid7 := symRun cfgC (cMid 7) (pcOf (coordAt 7 + 6)) 40
sym_block RHead8 := symRun cfgC (cHead 8) (pcOf (coordAt 8)) 40
sym_block RMid8 := symRun cfgC (cMid 8) (pcOf (coordAt 8 + 6)) 40
sym_block RRow := symRun cfgC cRow (pcOf (coordAt 0 + 10)) 40
sym_block RStep := symRun cfgC cStep (pcOf (coordAt 0 + 109)) 40
sym_block RSib0 := symRun cfgC (cSib 0) (pcOf (sibAt 0 0)) 40
sym_block RSib1 := symRun cfgC (cSib 1) (pcOf (sibAt 0 1)) 40
sym_block RSib2 := symRun cfgC (cSib 2) (pcOf (sibAt 0 2)) 40
sym_block RSib3 := symRun cfgC (cSib 3) (pcOf (sibAt 0 3)) 40
sym_block RSib4 := symRun cfgC (cSib 4) (pcOf (sibAt 0 4)) 40
sym_block RSib5 := symRun cfgC (cSib 5) (pcOf (sibAt 0 5)) 40
sym_block RSib6 := symRun cfgC (cSib 6) (pcOf (sibAt 0 6)) 40
def rSib (l : Nat) : Result := [RSib0.res, RSib1.res, RSib2.res, RSib3.res, RSib4.res, RSib5.res, RSib6.res].getD l RSib0.res
theorem run_sib (k l : Nat) (hk : k < 9) (hl : l < 7) : symRun cfgC (cSib l) (pcOf (sibAt k l)) 40 =
    some ⟨(rSib l).st, .c (pcOf (sibAt k l + sibLen l)), .endOfCode, sibLen l, sibLen l⟩ := by
  interval_cases k <;> interval_cases l <;> kernel_rfl
theorem run_row (k : Nat) (hk : k < 9) : symRun cfgC cRow (pcOf (coordAt k + 10)) 40 =
    some ⟨RRow.res.st, .c (pcOf (coordAt k + 13)), .endOfCode, 3, 3⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_step (k : Nat) (hk : k < 9) : symRun cfgC cStep (pcOf (coordAt k + 109)) 40 =
    some ⟨RStep.res.st, .c (pcOf (coordAt k + 111)), .endOfCode, 2, 2⟩ := by
  interval_cases k <;> kernel_rfl
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
def copied (s0 : MachineState) (src dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then s0.getMem (BitVec.ofNat 64 (src + (A - dst)))
  else s0.getMem (BitVec.ofNat 64 A)
def zeroed (s0 : MachineState) (dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then 0 else s0.getMem (BitVec.ofNat 64 A)
theorem ofNat_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) + 18446744073709551615#64 = BitVec.ofNat 64 n := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, ofNat_add_ofNat,
    show n + 1 + (2 ^ 64 - 1) = n + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]
macro "c_regs" res:ident : tactic =>
  `(tactic| (intro r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             cases r <;> simp_all [rv_simp, $res:ident] <;> rfl))
section
variable {im : Image} (hc : NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem copy_iter (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1)) (hn : n + 1 < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if n = 0 then pcOf 42136 else pcOf 42130) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src + 8) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst then s.getMem (BitVec.ofNat 64 src) else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RCopy (code_cCopy hc) s hpc (by
    simp [RCopy.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopy.res, E.eval, CmpOp.eval, BinOp.eval, h12]
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
  · simp [RCopy.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RCopy.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RCopy.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RCopy.res
  · intro A hA
    simp only [Result.toState_getMem, RCopy.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h10, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem copy_ret (s : MachineState) (hpc : s.pc = pcOf 42136) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RCopyRet (code_copyRet hc) s hpc (by simp [RCopyRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopyRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RCopyRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure CopyInv (s : MachineState) (src dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42130 else pcOf 42136)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (src + 8 * i)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x6, .x10, .x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst i A
theorem copy_loop (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∀ i, i ≤ n → ∃ t, Steps im s (6 * i) (6 * i) t ∧ CopyInv s src dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h10, by simpa using h11,
      by simpa using h12, fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold copied; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42130 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u10, u11, u12, ru, mu⟩ := copy_iter hc t hpc' (src + 8 * i) (dst + 8 * i) (n - i - 1)
      hI.x10 hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u10, show src + 8 * i + 8 = src + 8 * (i + 1) by ring]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (src + 8 * i)) = s.getMem (BitVec.ofNat 64 (src + 8 * i)) := by
        rw [hI.mem _ (by omega)]; unfold copied; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold copied
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show dst + 8 * i - dst = 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem copy_spec (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n ret : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (6 * n + 1) (6 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst n A) := by
  obtain ⟨t, st, hI⟩ := copy_loop hc s hpc src dst n h10 h11 h12 hn hn' hs hs' hd hd' hov n le_rfl
  have hpc' : t.pc = pcOf 42136 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := copy_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
set_option maxRecDepth 20000 in
theorem zero_iter (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1))
    (hn : n + 1 < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if n = 0 then pcOf 42141 else pcOf 42137) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧
      RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = if A = dst then 0 else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RZero (code_cZero hc) s hpc (by
    simp [RZero.res, rv_simp, accessValid_iff, h11, BitVec.toNat_ofNat]
    refine ⟨?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZero.res, E.eval, CmpOp.eval, BinOp.eval, h12]
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
  · simp [RZero.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RZero.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RZero.res
  · intro A hA
    simp only [Result.toState_getMem, RZero.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem zero_ret (s : MachineState) (hpc : s.pc = pcOf 42141) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RZeroRet (code_zeroRet hc) s hpc (by simp [RZeroRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZeroRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RZeroRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure ZeroInv (s : MachineState) (dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42137 else pcOf 42141)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst i A
theorem zero_loop (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hn' : n < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (4 * i) (4 * i) t ∧ ZeroInv s dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h11, by simpa using h12,
      fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold zeroed; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42137 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u11, u12, ru, mu⟩ := zero_iter hc t hpc' (dst + 8 * i) (n - i - 1)
      hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      rw [mu A hA, hI.mem A hA]
      unfold zeroed
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem zero_spec (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n ret : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n)
    (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32) (hd : dst % 8 = 0)
    (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∃ t, Steps im s (4 * n + 1) (4 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst n A) := by
  obtain ⟨t, st, hI⟩ := zero_loop hc s hpc dst n h11 h12 hn hn' hd hd' n le_rfl
  have hpc' : t.pc = pcOf 42141 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := zero_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt planBytes)
open ClaudeWCT.W9.T3M (authBase authRoot authSibOff)
set_option linter.unusedSimpArgs false
def bitE (l : Nat) : E :=
  if l < 6 then .bin .and (.bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))) (.c 1#64)
  else .bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))
def nbE (l : Nat) : E := .bin .xor (bitE l) (.c 1#64)
def t6E (l : Nat) : E := .bin .add (.bin .sll (nbE l) (.c 4#64)) (.bin .sll (nbE l) (.c 5#64))
def hwE (l : Nat) : E :=
  .un (.ld .hu (2 * (l % 4))) (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld)
def dstE (l : Nat) : E :=
  if l < 6 then .bin .add (.bin .add (.reg .x9) (hwE l)) (t6E l) else .bin .add (.reg .x9) (hwE l)
def a3E (l : Nat) : E := .bin .add (.reg .x8) (t6E l)
def srcE (l o : Nat) : E :=
  if 64 * (6 - l) + o = 0 then a3E l else .bin .add (a3E l) (.c (BitVec.ofNat 64 (64 * (6 - l) + o)))
def sibRegs (l : Nat) : RegFile :=
  ((((RegFile.init.set .x13 (a3E l)).set .x28 (dstE l)).set .x29 (srcE l 0).ld).set .x30 (srcE l 8).ld).set .x31
    (t6E l)
def sibMem (l : Nat) : SymMem :=
  [(⟨some (dstE l), 8#64⟩, (srcE l 8).ld), (⟨some (dstE l), 0#64⟩, (srcE l 0).ld)]
def sibObl (l : Nat) : List Oblig :=
  [.valid ⟨some (dstE l), 8#64⟩ 8, .valid ⟨some (dstE l), 0#64⟩ 8,
    .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l) + 8)⟩ 8, .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l))⟩ 8,
    .align8 (.reg .x20), .valid ⟨some (.reg .x20), BitVec.ofNat 64 (2 * l)⟩ 2]
theorem rSib_st (l : Nat) (hl : l < 7) : (rSib l).st = ⟨sibRegs l, sibMem l, sibObl l⟩ := by
  interval_cases l <;> kernel_rfl
def srcOff (c l : Nat) : Nat := 64 * (6 - l) + 48 * (1 - c / 2 ^ l % 2)
def planHW (c l : Nat) : Nat := if l < 6 then authBase c l else authRoot c
set_option maxRecDepth 100000 in
theorem planHW_ok : ∀ r < 64, ∀ l < 7,
    LoadKind.hu.fromWord (bytesToWordLE ((planBytes.drop (8 * (2 * r + l / 4))).take 8)) (2 * (l % 4)) =
      BitVec.ofNat 64 (planHW r l) := by
  decide +kernel
theorem authSibOff_ok : ∀ c < 128, ∀ l < 7, authSibOff c l % 16 = 0 ∧ authSibOff c l + 16 ≤ 320 := by
  decide +kernel
theorem planHW_mod (c l : Nat) : planHW (c % 64) l = planHW c l := by
  unfold planHW authBase authRoot; rw [Nat.mod_mod]
section eval
variable {s : MachineState} {c : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (hc : c < 128)
include h19 hc
theorem bitE_eval (l : Nat) (hl : l < 7) : (bitE l).eval s = BitVec.ofNat 64 (c / 2 ^ l % 2) := by
  apply BitVec.eq_of_toNat_eq
  unfold bitE
  split
  · simp only [E.eval, BinOp.eval, h19, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show l < 64 by omega), show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod,
      Nat.mod_eq_of_lt (show c / 2 ^ l % 2 < 2 ^ 64 from lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))]
  · have hl6 : l = 6 := by omega
    subst hl6
    simp only [E.eval, BinOp.eval, h19, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
    norm_num
    omega
theorem nbE_eval (l : Nat) (hl : l < 7) : (nbE l).eval s = BitVec.ofNat 64 (1 - c / 2 ^ l % 2) := by
  have hb := bitE_eval h19 hc l hl
  simp only [nbE, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem t6E_eval (l : Nat) (hl : l < 7) : (t6E l).eval s = BitVec.ofNat 64 (48 * (1 - c / 2 ^ l % 2)) := by
  have hb := nbE_eval h19 hc l hl
  simp only [t6E, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem a3E_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) :
    (a3E l).eval s = BitVec.ofNat 64 (S + 48 * (1 - c / 2 ^ l % 2)) := by
  simp only [a3E, E.eval, BinOp.eval, h8, t6E_eval h19 hc l hl, ofNat_add_ofNat]
theorem srcE_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (o : Nat) :
    (srcE l o).eval s = BitVec.ofNat 64 (S + srcOff c l + o) := by
  unfold srcE srcOff
  split
  · rw [a3E_eval h19 hc l hl h8]; congr 1; omega
  · simp only [E.eval, BinOp.eval, a3E_eval h19 hc l hl h8, ofNat_add_ofNat]; congr 1; omega
end eval
theorem hwE_eval {s : MachineState} {c : Nat} (hc : c < 128)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s) (l : Nat) (hl : l < 7) :
    (hwE l).eval s = BitVec.ofNat 64 (planHW c l) := by
  have hr : c % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hw : (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld).eval s =
      bytesToWordLE ((planBytes.drop (8 * (2 * (c % 64) + l / 4))).take 8) := by
    split
    · simp only [E.eval, h20]
      rw [show l / 4 = 0 by omega, show PLAN + 16 * (c % 64) = PLAN + 8 * (2 * (c % 64) + 0) by ring]
      exact hp _ (by omega)
    · simp only [E.eval, BinOp.eval, h20, ofNat_add_ofNat]
      rw [show l / 4 = 1 by omega, show PLAN + 16 * (c % 64) + 8 = PLAN + 8 * (2 * (c % 64) + 1) by ring]
      exact hp _ (by omega)
  simp only [hwE, E.eval, UnOp.eval]
  rw [hw, planHW_ok (c % 64) hr l hl, planHW_mod]
theorem authSibOff_eq (c l : Nat) (hl : l < 7) :
    authSibOff c l = if l < 6 then planHW c l + 48 * (1 - c / 2 ^ l % 2) else planHW c l := by
  unfold authSibOff planHW SigGolfCandidate.T3M.sibOff
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  split_ifs <;> omega
theorem dstE_eval {s : MachineState} {c D : Nat} (hc : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (l : Nat) (hl : l < 7) :
    (dstE l).eval s = BitVec.ofNat 64 (D + authSibOff c l) := by
  rw [authSibOff_eq c l hl]
  unfold dstE
  split
  · simp only [E.eval, BinOp.eval, h9, hwE_eval hc h20 hp l hl, t6E_eval h19 hc l hl, ofNat_add_ofNat]
    rw [Nat.add_assoc]
  · simp only [E.eval, BinOp.eval, h9, hwE_eval hc h20 hp l hl, ofNat_add_ofNat]
theorem srcOff_bound (c l : Nat) : srcOff c l + 16 ≤ 448 ∧ srcOff c l % 16 = 0 := by
  unfold srcOff
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  constructor <;> omega
theorem sibRegs_get (l : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x13, .x28, .x29, .x30, .x31]) :
    ((sibRegs l).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h13, h28, h29, h30, h31⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
section
variable {im : Image} (hc : NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sib_spec (k l : Nat) (hk : k < 9) (hl : l < 7) (s : MachineState) (hpc : s.pc = pcOf (sibAt k l))
    (c S D : Nat) (hcl : c < 128) (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)))
    (hp : PlanAt s) (hS : S % 16 = 0) (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0)
    (hD' : D + 320 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s (sibLen l) (sibLen l) t ∧ t.pc = pcOf (sibAt k l + sibLen l) ∧
      RegsExcept s t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = D + authSibOff c l + 8 then s.getMem (BitVec.ofNat 64 (S + srcOff c l + 8))
        else if A = D + authSibOff c l then s.getMem (BitVec.ofNat 64 (S + srcOff c l))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have ha := authSibOff_ok c hcl l hl
  have hso := srcOff_bound c l
  have hd := dstE_eval hcl h19 h20 hp h9 l hl
  have hs0 := srcE_eval h19 hcl l hl h8 0
  have hs8 := srcE_eval h19 hcl l hl h8 8
  have ha3 := a3E_eval h19 hcl l hl h8
  have hrun := run_sib k l hk hl
  rw [rSib_st l hl] at hrun
  have hobl : Oblig.all s (sibObl l) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [sibObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hd, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, hd, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + (64 * (6 - l) + 8) = S + srcOff c l + 8 by unfold srcOff; omega]
      omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + 64 * (6 - l) = S + srcOff c l by unfold srcOff; omega]
      omega
    · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold PLAN; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold PLAN; omega
  refine ⟨_, symRun_sound hrun (code_cSib hc k l hk hl) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    rw [Result.toState_getReg]
    exact sibRegs_get l s r hr
  · intro A hA
    simp only [Result.toState_getMem, sibMem, memEval_cons, memEval_nil, Addr.eval, E.eval, hd, hs0, hs8,
      ofNat_add_ofNat, BitVec.add_zero]
    have hbig : D + authSibOff c l + 8 < 2 ^ 64 := by omega
    by_cases h1 : A = D + authSibOff c l + 8
    · subst h1; simp
    · rw [if_neg (fun h => h1 ((ofNat_inj hA hbig).mp h)), if_neg h1]
      by_cases h2 : A = D + authSibOff c l
      · subst h2; simp
      · rw [if_neg (fun h => h2 ((ofNat_inj hA (by omega)).mp h)), if_neg h2]
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt child_bits)
set_option linter.unusedSimpArgs false
def SNAP : Nat := 0x200000
def rHead (k : Nat) : Result :=
  [RHead0.res, RHead1.res, RHead2.res, RHead3.res, RHead4.res, RHead5.res, RHead6.res, RHead7.res, RHead8.res].getD k
    RHead0.res
def rMid (k : Nat) : Result :=
  [RMid0.res, RMid1.res, RMid2.res, RMid3.res, RMid4.res, RMid5.res, RMid6.res, RMid7.res, RMid8.res].getD k RMid0.res
theorem run_head (k : Nat) (hk : k < 9) : symRun cfgC (cHead k) (pcOf (coordAt k)) 40 = some (rHead k) := by
  interval_cases k
  exacts [RHead0, RHead1, RHead2, RHead3, RHead4, RHead5, RHead6, RHead7, RHead8]
theorem run_mid (k : Nat) (hk : k < 9) : symRun cfgC (cMid k) (pcOf (coordAt k + 6)) 40 = some (rMid k) := by
  interval_cases k
  exacts [RMid0, RMid1, RMid2, RMid3, RMid4, RMid5, RMid6, RMid7, RMid8]
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem start_spec (s : MachineState) (hpc : s.pc = pcOf 41108) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 0x840 ∧
      t.getReg .x11 = BitVec.ofNat 64 SNAP ∧ t.getReg .x12 = BitVec.ofNat 64 1152 ∧ t.getReg .x1 = pcOf 41115 ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RStart (code_cStart hc) s hpc (by simp [RStart.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RStart.res, E.eval]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]; rfl
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · c_regs RStart.res
  · intro A _ _; rfl
theorem regs_spec (s : MachineState) (hpc : s.pc = pcOf 41115) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (coordAt 0) ∧ t.getReg .x8 = BitVec.ofNat 64 SNAP ∧
      t.getReg .x9 = BitVec.ofNat 64 0x840 ∧ t.getReg .x18 = BitVec.ofNat 64 PLAN ∧
      RegsExcept s t [.x8, .x9, .x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RRegs (code_cRegs hc) s hpc (by simp [RRegs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RRegs.res, E.eval, coordAt]
  · simp [RRegs.res, rv_simp]; rfl
  · simp [RRegs.res, rv_simp]
  · simp [RRegs.res, rv_simp]; rfl
  · c_regs RRegs.res
  · intro A _ _; rfl
theorem final_spec (s : MachineState) (hpc : s.pc = pcOf 42120) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (0x800 + 9280) ∧
      t.getReg .x11 = BitVec.ofNat 64 (0x800 + 8128) ∧ t.getReg .x12 = BitVec.ofNat 64 1715 ∧
      t.getReg .x1 = pcOf 42127 ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RFinal (code_cFinal hc) s hpc (by simp [RFinal.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RFinal.res, E.eval]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · c_regs RFinal.res
  · intro A _ _; rfl
theorem halt_spec (s : MachineState) (hpc : s.pc = pcOf 42127) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 42129 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ fetch im t = some (.base .ECALL) ∧
      RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  have hcode : CodeAt im (pcOf 42129) [0x73] := codeAt_of_window hc (by decide) (by decide +kernel)
  refine ⟨_, symRun_sound RHalt (code_cHalt hc) s hpc (by simp [RHalt.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RHalt.res, E.eval]
  · simp [RHalt.res, rv_simp]
  · simp [RHalt.res, rv_simp]
  · rw [hcode.fetch _ (by simp [Result.toState_pc, RHalt.res, E.eval])]; rfl
  · c_regs RHalt.res
  · intro A _ _; rfl
end
def headX6 (k : Nat) : E :=
  .bin .srl (E.c (BitVec.ofNat 64 (0x60 + 8 * (WCT9.childBase k / 64)))).ld (.c (BitVec.ofNat 64 (WCT9.childBase k % 64)))
def headRegs (k : Nat) : RegFile :=
  ((((RegFile.init.set .x6 (headX6 k)).set .x19 (.bin .and (headX6 k) (.c 127#64))).set .x11 (.reg .x9)).set .x12
    (.c 40#64)).set .x1 (.c (pcOf (coordAt k + 6)))
def midRegs (k : Nat) : RegFile :=
  (((RegFile.init.set .x10 (.bin .add (.reg .x8) (.c 448#64))).set .x11 (.bin .add (.reg .x9) (.c 320#64))).set .x12
    (.c 72#64)).set .x1 (.c (pcOf (coordAt k + 10)))
theorem rHead_eq (k : Nat) (hk : k < 9) : rHead k = ⟨⟨headRegs k, [], []⟩, .c (pcOf 42137), .jump, 6, 6⟩ := by
  interval_cases k <;> kernel_rfl
theorem rMid_eq (k : Nat) (hk : k < 9) : rMid k = ⟨⟨midRegs k, [], []⟩, .c (pcOf 42130), .jump, 4, 4⟩ := by
  interval_cases k <;> kernel_rfl
theorem headRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x6, .x11, .x12, .x19]) :
    ((headRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h6, h11, h12, h19⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem midRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x10, .x11, .x12]) :
    ((midRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h10, h11, h12⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem childBase_shift (k : Nat) (hk : k < 9) : WCT9.childBase k % 64 + 7 ≤ 64 ∧ WCT9.childBase k / 64 < 4 := by
  interval_cases k <;> decide
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem head_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (D : Nat) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42137 ∧
      t.getReg .x19 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase k % 128) ∧
      t.getReg .x11 = BitVec.ofNat 64 D ∧ t.getReg .x12 = BitVec.ofNat 64 40 ∧ t.getReg .x1 = pcOf (coordAt k + 6) ∧
      RegsExcept s t [.x1, .x6, .x11, .x12, .x19] ∧ Frame s t (fun _ => False) := by
  have hrun := run_head k hk
  rw [rHead_eq k hk] at hrun
  obtain ⟨hsh, hw⟩ := childBase_shift k hk
  refine ⟨_, symRun_sound hrun (code_cHead hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, headRegs, headX6, RegFile.set, RegFile.get, E.eval, BinOp.eval]
    have hm := hN (WCT9.childBase k / 64) hw
    rw [hm]
    apply BitVec.eq_of_toNat_eq
    have := child_bits N (WCT9.childBase k / 64) (WCT9.childBase k % 64) hsh
    rw [Nat.div_add_mod] at this
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 64 by omega)]
    rw [this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num) : N.toNat / 2 ^ WCT9.childBase k % 128 < 2 ^ 64)]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval, h9]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact headRegs_get k s r hr
  · intro A _ _; rfl
theorem mid_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 6)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (S + 448) ∧
      t.getReg .x11 = BitVec.ofNat 64 (D + 320) ∧ t.getReg .x12 = BitVec.ofNat 64 72 ∧
      t.getReg .x1 = pcOf (coordAt k + 10) ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  have hrun := run_mid k hk
  rw [rMid_eq k hk] at hrun
  refine ⟨_, symRun_sound hrun (code_cMid hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact midRegs_get k s r hr
  · intro A _ _; rfl
theorem row_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 10)) (c : Nat)
    (hcl : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (coordAt k + 13) ∧ t.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)) ∧
      RegsExcept s t [.x7, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_row k hk) (code_cRow hc k hk) s hpc (by simp [RRow.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RRow.res, RegFile.get, E.eval, BinOp.eval, h19, h18]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl, SigGolfCandidate.T3M.Search.ofNat_and_mask c 6 (by norm_num)]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; ring
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h20⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem step_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 109)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (coordAt k + 111) ∧ t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧
      t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧ RegsExcept s t [.x8, .x9] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_step k hk) (code_cStep hc k hk) s hpc (by simp [RStep.res, rv_simp]), ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8', h9'⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
open ClaudeWCT.W9.T3M (authSibOff)
set_option linter.unusedSimpArgs false
def sibLev (c j : Nat) : Option Nat :=
  (List.range 7).find? fun l => authSibOff c l = 8 * j ∨ authSibOff c l + 8 = 8 * j
def sibSrc (c j : Nat) : Option Nat :=
  (sibLev c j).map fun l => if authSibOff c l = 8 * j then srcOff c l else srcOff c l + 8
def coordMem (M : Nat → Word) (c S D : Nat) (A : Nat) : Word :=
  if D ≤ A ∧ A < D + 896 ∧ (A - D) % 8 = 0 then
    if A - D < 320 then
      match sibSrc c ((A - D) / 8) with
      | some o => M (S + o)
      | none => 0
    else M (S + 448 + (A - D - 320))
  else M A
def sibsMem (M : Nat → Word) (c S D L : Nat) (A : Nat) : Word :=
  match (List.range L).find? (fun l => A = D + authSibOff c l ∨ A = D + authSibOff c l + 8) with
  | some l => if A = D + authSibOff c l then M (S + srcOff c l) else M (S + srcOff c l + 8)
  | none => M A
theorem find_range_succ (p : Nat → Bool) (L : Nat) :
    (List.range (L + 1)).find? p = match (List.range L).find? p with
      | some l => some l
      | none => if p L then some L else none := by
  rw [List.range_succ, List.find?_append]
  cases h : (List.range L).find? p with
  | some l => rfl
  | none => simp only [List.find?_cons, List.find?_nil, Option.none_or]; cases hp : p L <;> simp [hp]
theorem find_some {p : Nat → Bool} {L l : Nat} (h : (List.range L).find? p = some l) : l < L ∧ p l = true :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), List.find?_some h⟩
theorem find_none {p : Nat → Bool} {L : Nat} (h : (List.range L).find? p = none) (l : Nat) (hl : l < L) :
    p l = false := by
  have := List.find?_eq_none.mp h l (List.mem_range.mpr hl)
  simpa using this
theorem auth_disj (c : Nat) (hc : c < 128) (l l' : Nat) (hl : l < 7) (hl' : l' < 7) (hne : l ≠ l') :
    authSibOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authSibOff c l :=
  ClaudeWCT.W9.T3M.auth_sib_disjoint c hc l hl l' hl' hne
theorem sibsMem_succ (M : Nat → Word) (c S D L : Nat) (hc : c < 128) (hL : L < 7) (A : Nat) :
    sibsMem M c S D (L + 1) A =
      if A = D + authSibOff c L + 8 then M (S + srcOff c L + 8)
      else if A = D + authSibOff c L then M (S + srcOff c L) else sibsMem M c S D L A := by
  unfold sibsMem
  rw [find_range_succ]
  cases h : (List.range L).find? (fun l => decide (A = D + authSibOff c l ∨ A = D + authSibOff c l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have hd := auth_disj c hc l L (by omega) hL (by omega)
    simp only
    rw [if_neg (show ¬ A = D + authSibOff c L + 8 by omega), if_neg (show ¬ A = D + authSibOff c L by omega)]
  | none =>
    simp only
    by_cases h1 : A = D + authSibOff c L + 8
    · have h2 : ¬ A = D + authSibOff c L := by omega
      rw [if_pos (show decide (A = D + authSibOff c L ∨ A = D + authSibOff c L + 8) = true by simp [h1]),
        if_pos h1]
      simp only
      rw [if_neg h2]
    · by_cases h2 : A = D + authSibOff c L
      · rw [if_pos (show decide (A = D + authSibOff c L ∨ A = D + authSibOff c L + 8) = true by simp [h2]),
          if_neg h1, if_pos h2]
        simp only
        rw [if_pos h2]
      · rw [if_neg (show ¬ decide (A = D + authSibOff c L ∨ A = D + authSibOff c L + 8) = true by simp [h1, h2]),
          if_neg h1, if_neg h2]
theorem sibLev_eq (c D A : Nat) (hDA : D ≤ A) (hal : (A - D) % 8 = 0) :
    sibLev c ((A - D) / 8) =
      (List.range 7).find? (fun l => decide (A = D + authSibOff c l ∨ A = D + authSibOff c l + 8)) := by
  unfold sibLev
  congr 1
  funext l
  apply Bool.decide_congr
  omega
def zcMem (M : Nat → Word) (S D : Nat) (A : Nat) : Word :=
  if D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0 then M (S + 448 + (A - D - 320))
  else if D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0 then 0 else M A
theorem sibsMem_seven (M : Nat → Word) (c S D : Nat) (hc : c < 128) (hD : D % 16 = 0) (hS : D + 896 ≤ S)
    (A : Nat) : sibsMem (zcMem M S D) c S D 7 A = coordMem M c S D A := by
  have hzS : ∀ o, o < 448 → zcMem M S D (S + o) = M (S + o) := by
    intro o ho; unfold zcMem; rw [if_neg (by omega), if_neg (by omega)]
  unfold sibsMem coordMem
  cases h : (List.range 7).find? (fun l => decide (A = D + authSibOff c l ∨ A = D + authSibOff c l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    obtain ⟨ha16, ha⟩ := authSibOff_ok c hc l hl
    have hso := srcOff_bound c l
    have hDA : D ≤ A ∧ A < D + 896 ∧ (A - D) % 8 = 0 := by omega
    rw [if_pos hDA, if_pos (by omega), sibSrc, sibLev_eq c D A hDA.1 hDA.2.2, h]
    simp only [Option.map_some]
    by_cases h0 : A = D + authSibOff c l
    · rw [if_pos h0, if_pos (by omega), hzS _ (by omega)]
    · rw [if_neg h0, if_neg (by omega), Nat.add_assoc, hzS _ (by omega)]
  | none =>
    simp only
    unfold zcMem
    by_cases hDA : D ≤ A ∧ A < D + 896 ∧ (A - D) % 8 = 0
    · rw [if_pos hDA]
      by_cases h3 : A - D < 320
      · rw [if_pos h3, sibSrc, sibLev_eq c D A hDA.1 hDA.2.2, h, if_neg (by omega), if_pos (by omega)]
        rfl
      · rw [if_neg h3, if_pos (by omega)]
    · rw [if_neg hDA, if_neg (by omega), if_neg (by omega)]
theorem sibsMem_out (M : Nat → Word) (c S D L : Nat) (hc : c < 128) (hL : L ≤ 7) (A : Nat)
    (hA : A < D ∨ D + 320 ≤ A) : sibsMem M c S D L A = M A := by
  unfold sibsMem
  cases h : (List.range L).find? (fun l => decide (A = D + authSibOff c l ∨ A = D + authSibOff c l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have := authSibOff_ok c hc l (by omega)
    omega
  | none => rfl
def sibsCyc (L : Nat) : Nat := 14 * L - 2 * (L / 7)
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem sibs_spec (k : Nat) (hk : k < 9) (c S D : Nat) (hcl : c < 128) (hS : S % 16 = 0)
    (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0) (hDS : D + 320 ≤ S) (hDP : D + 320 ≤ PLAN)
    (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (coordAt k + 13)) (h8 : u.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : u.getReg .x9 = BitVec.ofNat 64 D) (h19 : u.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : u.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt u) :
    ∀ L ≤ 7, ∃ t, Steps im u (sibsCyc L) (sibsCyc L) t ∧ t.pc = pcOf (coordAt k + 13 + sibsCyc L) ∧
      RegsExcept u t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = sibsMem M0 c S D L A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  intro L hL
  induction L with
  | zero => exact ⟨u, Steps.refl u, by simpa [sibsCyc] using hpc, RegsExcept.refl u _, fun A hA => hM A hA⟩
  | succ L ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hpL : t.pc = pcOf (sibAt k L) := by
      rw [pt, show coordAt k + 13 + sibsCyc L = sibAt k L by unfold sibAt sibsCyc; omega]
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega), sibsMem_out M0 c S D L hcl (by omega) _ (by omega), ← hM _ (by omega)]
      exact hp j hj
    obtain ⟨t', st', pt', rt', mt'⟩ := sib_spec hc k L hk (by omega) t hpL c S D hcl
      (by rw [rt.get (by decide), h8]) (by rw [rt.get (by decide), h9]) (by rw [rt.get (by decide), h19])
      (by rw [rt.get (by decide), h20]) hpt hS hS' hD (by omega)
    have hcyc : sibsCyc L + sibLen L = sibsCyc (L + 1) := by unfold sibsCyc sibLen; split <;> omega
    refine ⟨t', (st.trans st').of_eq hcyc hcyc, ?_, (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    · rw [pt', show sibAt k L + sibLen L = coordAt k + 13 + sibsCyc (L + 1) by
        unfold sibAt; rw [← hcyc]; unfold sibsCyc; omega]
    · have hso := srcOff_bound c L
      rw [mt' A hA, sibsMem_succ M0 c S D L hcl (by omega) A, mt (S + srcOff c L + 8) (by omega),
        mt (S + srcOff c L) (by omega), mt A hA,
        sibsMem_out M0 c S D L hcl (by omega) (S + srcOff c L + 8) (Or.inr (by omega)),
        sibsMem_out M0 c S D L hcl (by omega) (S + srcOff c L) (Or.inr (by omega))]
set_option maxRecDepth 20000 in
theorem coord_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (hp : PlanAt s) (S D : Nat) (h8 : s.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN)
    (hS : S % 16 = 0) (hD : D % 16 = 0) (hDS : D + 896 ≤ S) (hS' : S + 1024 ≤ MEMORY_BYTES)
    (hDP : D + 896 ≤ PLAN) :
    ∃ t, Steps im s 705 705 t ∧ t.pc = pcOf (coordAt k + 111) ∧
      t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧ t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        coordMem (fun B => s.getMem (BitVec.ofNat 64 B)) (N.toNat / 2 ^ WCT9.childBase k % 128) S D A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  obtain ⟨c, hcdef⟩ : ∃ c, c = N.toNat / 2 ^ WCT9.childBase k % 128 := ⟨_, rfl⟩
  rw [← hcdef]
  have hcl : c < 128 := by rw [hcdef]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨t1, s1, p1, r19, r11, r12, r1, g1, f1⟩ := head_spec hc k hk s hpc N hN D h9
  rw [← hcdef] at r19
  obtain ⟨t2, s2, p2, g2, m2⟩ := zero_spec hc t1 p1 D 40 (coordAt k + 6) r11 r12 r1 (by norm_num) (by norm_num)
    (by omega) (by omega)
  obtain ⟨t3, s3, p3, q10, q11, q12, q1, g3, f3⟩ := mid_spec hc k hk t2 p2 S D
    (by rw [g2.get (by decide), g1.get (by decide), h8]) (by rw [g2.get (by decide), g1.get (by decide), h9])
  obtain ⟨t4, s4, p4, g4, m4⟩ := copy_spec hc t3 p3 (S + 448) (D + 320) 72 (coordAt k + 10) q10 q11 q12 q1
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨t5, s5, p5, w20, g5, f5⟩ := row_spec hc k hk t4 p4 c hcl
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), r19])
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h18])
  have hz : ∀ X < 2 ^ 64, t3.getMem (BitVec.ofNat 64 X) = zeroed t1 D 40 X := fun X hX => by
    rw [f3 X hX (fun h => h), m2 X hX]
  have hM5 : ∀ A < 2 ^ 64, t5.getMem (BitVec.ofNat 64 A) =
      zcMem (fun B => s.getMem (BitVec.ofNat 64 B)) S D A := by
    intro A hA
    rw [f5 A hA (fun h => h), m4 A hA]
    unfold copied zcMem
    by_cases h1 : D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0
    · rw [if_pos (show D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0 by omega), if_pos h1,
        hz _ (by omega)]
      unfold zeroed
      rw [if_neg (by omega), f1 _ (by omega) (fun h => h),
        show S + 448 + (A - (D + 320)) = S + 448 + (A - D - 320) by omega]
    · rw [if_neg (show ¬ (D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0) by omega), if_neg h1,
        hz A hA]
      unfold zeroed
      by_cases h2 : D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0
      · rw [if_pos (show D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0 by omega), if_pos h2]
      · rw [if_neg (show ¬ (D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0) by omega), if_neg h2,
          f1 A hA (fun h => h)]
  have hp5 : PlanAt t5 := fun j hj => by
    rw [hM5 _ (by omega)]
    unfold zcMem
    rw [if_neg (show ¬ (D + 320 ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 896 ∧ (PLAN + 8 * j - D - 320) % 8 = 0) by omega),
      if_neg (show ¬ (D ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 320 ∧ (PLAN + 8 * j - D) % 8 = 0) by omega)]
    exact hp j hj
  have e8 : t5.getReg .x8 = BitVec.ofNat 64 S := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h8]
  have e9 : t5.getReg .x9 = BitVec.ofNat 64 D := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h9]
  have e19 : t5.getReg .x19 = BitVec.ofNat 64 c := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), r19]
  obtain ⟨t6, s6, p6, g6, m6⟩ := sibs_spec hc k hk c S D hcl hS (by omega) hD (by omega) (by omega) t5 _ hM5
    p5 e8 e9 e19 w20 hp5 7 le_rfl
  obtain ⟨t7, s7, p7, w8, w9, g7, f7⟩ := step_spec hc k hk t6
    (by rw [p6, show coordAt k + 13 + sibsCyc 7 = coordAt k + 109 by unfold sibsCyc; omega]) S D
    (by rw [g6.get (by decide), e8]) (by rw [g6.get (by decide), e9])
  refine ⟨t7, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).of_eq
    (by unfold sibsCyc; omega) (by unfold sibsCyc; omega), p7, w8, w9,
    ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).mono (by decide), fun A hA => ?_⟩
  rw [f7 A hA (fun h => h), m6 A hA, sibsMem_seven _ c S D hcl hD hDS A]
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
