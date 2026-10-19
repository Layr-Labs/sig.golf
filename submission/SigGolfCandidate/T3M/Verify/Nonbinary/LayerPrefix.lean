import SigGolfCandidate.Rv
import SigGolfCandidate.T3M.Mem

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
/-- Configuration (1)+(2), e7b head: the top-half selector (7 words at `h+6..h+12`).
`lb gp,528(tp); bge gp,zero,L` (hint byte at abs 25216: bit 7 clear = LOW, 4 cycles);
`lbu gp,15(a2); bltu gp,a1,L` (LOW forced when its top byte is `< 64`, i.e. LOW `< 2^126`: 6 cycles);
`addi a2,a2,16` (HIGH, 7 cycles); `L: ld a7,8(a2); ld a6,0(a2)`. -/
def prefixHint : List (BitVec 32) := [0x21020183,0x1d863]
def prefixHead : List (BitVec 32) := [0xf64183,0xb1e463]
def prefixHigh : List (BitVec 32) := [0x1060613]
def prefixLoad : List (BitVec 32) := [0x863883,0x63803]
/-- R6 prologue tail, 8 words at `h+7..h+14` (verify image RC_T153_g804):
`blt a7,zero,+32` (spare bit 127 set: jump to the zero word at `h+15`, fetch faults);
`ld t1,232(s1)` (r5 mask 0x7F000); `ld t4,-288(s1)` (r6 mask 0xFF00 = data word 16); `lui s2,209` (s2 = 856064);
`addi s0,a0,-(a-13432)`; `slli a4,a6,56; srli a4,a4,45; jalr -744(a4)` (g0 dispatch into the column
`512 (raw - 3) + 326`, see `ChainsDispatchArith.g0_target`). -/
def prefixSpare : List (BitVec 32) := [0x208c063]
def prefixRestWordsOf (a : Nat) : List (BitVec 32) :=
  [0x0e84b303,0xee04be83,0xd1937,
   BitVec.ofNat 32 ((4096 - (a - 13432)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13),
   0x3881713,0x2d75713,0xd1870067]
def prefixTailWordsOf (a : Nat) : List (BitVec 32) := prefixSpare ++ prefixRestWordsOf a
/-! Top-half selector parameters. The head of every top copy is `prefixSel` (at `h+6`) followed by the 6-word
dispatch tail. To swap the selector, change `prefixSel`/`selLen`/`selHintBit` here and `selCost` + the proof of
`prefix_select_spec` (Nonbinary/LayerContext.lean); `topTransition` and `Compose.top_after_hash` only use the spec
(exact cost `selCost high a ≤ selMax`). -/
def prefixSel : List (BitVec 32) := prefixHint ++ prefixHead ++ prefixHigh ++ prefixLoad
def selLen : Nat := 7
theorem prefixSel_length : prefixSel.length = selLen := rfl
/-- The bit of the witness choice byte (abs 25216) that requests HIGH. -/
def selHintBit : Nat := 7
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  prefixSel ++ prefixTailWordsOf a
def aVals : List Nat := [15288,15304,15336,15352,15384,15400,15432,15448,15480]
-- The 7 words after the spare-bit branch (a-independent except the `addi s0`, patched in `prefixRegs`).
sym_block prefixBase := symRun { noAlias := true } (prefixRestWordsOf 15384) (BitVec.ofNat 64 (0x1000 + 4 * 1078)) 200
sym_block prefixSpareBase := symRun { noAlias := true } prefixSpare (BitVec.ofNat 64 (0x1000 + 4 * 1077)) 200
def prefixRegs (a : Nat) : RegFile :=
  prefixBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 13432)))))
def prefixRes (a : Nat) : Result :=
  { prefixBase.res with st := { prefixBase.res.st with regs := prefixRegs a } }
sym_block prefixHintBase := symRun { noAlias := true } prefixHint (BitVec.ofNat 64 (0x1000 + 4*1070)) 200
sym_block prefixHeadBase := symRun { noAlias := true } prefixHead (BitVec.ofNat 64 (0x1000 + 4*1072)) 200
sym_block prefixHighBase := symRun { noAlias := true } prefixHigh (BitVec.ofNat 64 (0x1000 + 4*1074)) 200
sym_block prefixLoadBase := symRun { noAlias := true } prefixLoad (BitVec.ofNat 64 (0x1000 + 4*1075)) 200
def hintByte : E := .un (.ld .b 0) (.ld (.bin .add (.reg .x4) (.c 528)))
def headByte : E := .un (.ld .bu 7) (.ld (.bin .add (.reg .x12) (.c 8)))
def prefixHintRes (p : Word) : Result :=
  {prefixHintBase.res with pc := (E.ite .ge hintByte (.c 0) (.c (p+4+16)) (.c (p+4+4)))}
def prefixHeadRes (p : Word) : Result :=
  {prefixHeadBase.res with pc := (E.ite .ltu headByte (.reg .x11) (.c (p+4+8)) (.c (p+4+4)))}
def prefixHighRes (p : Word) : Result := {prefixHighBase.res with pc := .c (p+4)}
def prefixLoadRes (p : Word) : Result := {prefixLoadBase.res with pc := .c (p+4+4)}
/-- `blt a7,zero,+32`: spare bit 127 set (a7 negative) goes to the zero word 8 words ahead. -/
def prefixSpareRes (p : Word) : Result :=
  {prefixSpareBase.res with pc := (E.ite .lt (.reg .x17) (.c 0) (.c (p+32)) (.c (p+4)))}
theorem prefixHint_run (p : Word) :
    symRun {noAlias := true} prefixHint p 200 = some (prefixHintRes p) := by rfl
theorem prefixHead_run (p : Word) :
    symRun {noAlias := true} prefixHead p 200 = some (prefixHeadRes p) := by rfl
theorem prefixHigh_run (p : Word) :
    symRun {noAlias := true} prefixHigh p 200 = some (prefixHighRes p) := by rfl
theorem prefixLoad_run (p : Word) :
    symRun {noAlias := true} prefixLoad p 200 = some (prefixLoadRes p) := by rfl
theorem prefixSpare_run (p : Word) :
    symRun {noAlias := true} prefixSpare p 200 = some (prefixSpareRes p) := by rfl
theorem prefix_rest_run (a : Nat) (ha : a ∈ aVals) (pc : Word) :
    symRun { noAlias := true } (prefixRestWordsOf a) pc 200 = some (prefixRes a) := by
  simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
/-- The spare-bit branch: with a7 = the high word of the selected half `V`, it goes 8 words ahead (to a zero word)
iff bit 127 of `V` is set. -/
theorem prefixSpare_pc (s : MachineState) (p : Word) (V : BitVec 128)
    (h17 : s.getReg .x17 = V.extractLsb' 64 64) :
    (prefixSpareRes p).pc.eval s = if V.toNat / 2 ^ 127 % 2 = 1 then p + 32 else p + 4 := by
  simp only [prefixSpareRes, E.eval, h17]
  have hb : V.getLsbD 127 = decide (V.toNat / 2 ^ 127 % 2 = 1) := by
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  have hs : CmpOp.eval .lt (V.extractLsb' 64 64) 0 = decide (V.toNat / 2 ^ 127 % 2 = 1) := by
    have hz : (0 : BitVec 64) = 0#64 := rfl
    simp only [CmpOp.eval]
    rw [hz, BitVec.slt_zero_eq_msb, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb', hb]
    simp
  rw [hs]
  by_cases h : V.toNat / 2 ^ 127 % 2 = 1 <;> simp [h]
/-- The g0 dispatch target of the prologue (`slli a4,a6,56; srli a4,a4,45; jalr -744(a4)`), see
`Nonbinary.NCtx.g0_group`. -/
def g0Target (V : BitVec 128) : Word :=
  ((((V.extractLsb' 0 64) <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64
theorem spare_regs (p : Word) (s : MachineState) : T3M.RegsExcept s ((prefixSpareRes p).toState s) [] := by
  intro r _; cases r <;> simp [prefixSpareRes, prefixSpareBase.res, rv_simp] <;> rfl
theorem spare_frame (p : Word) (s : MachineState) : T3M.Frame s ((prefixSpareRes p).toState s) (fun _ => False) := by
  intro A _ _; simp [prefixSpareRes, prefixSpareBase.res, rv_simp]
theorem rest_pc (a : Nat) (u : MachineState) (V : BitVec 128) (h16 : u.getReg .x16 = V.extractLsb' 0 64) :
    ((prefixRes a).toState u).pc = g0Target V := by
  have e1 : (56#64 : Word).toNat % 64 = 56 := rfl
  have e2 : (45#64 : Word).toNat % 64 = 45 := rfl
  have e3 : (18446744073709550872#64 : Word) = BitVec.ofNat 64 (2^64-744) := rfl
  have e4 : (18446744073709551614#64 : Word) = ~~~1#64 := by decide
  simp only [Result.toState_pc, prefixRes, prefixRegs, prefixBase.res, E.eval, BinOp.eval, h16]
  rw [e1, e2, e3, e4]; rfl
theorem rest_regs (a : Nat) (ha : a ∈ aVals) (u : MachineState) (h10 : u.getReg .x10 = BitVec.ofNat 64 a) :
    ((prefixRes a).toState u).getReg .x8 = 13432#64 ∧ ((prefixRes a).toState u).getReg .x18 = 856064#64 ∧
    ((prefixRes a).toState u).getReg .x6 = u.getMem (u.getReg .x9 + 232#64) ∧
    ((prefixRes a).toState u).getReg .x29 = u.getMem (u.getReg .x9 + 18446744073709551328#64) ∧
    ((prefixRes a).toState u).getReg .x16 = u.getReg .x16 ∧ ((prefixRes a).toState u).getReg .x17 = u.getReg .x17 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, RegFile.get, RegFile.set, E.eval, BinOp.eval, h10]
    simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  all_goals simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval]
  all_goals rfl
theorem rest_except (a : Nat) (u : MachineState) :
    T3M.RegsExcept u ((prefixRes a).toState u) [.x29,.x6,.x18,.x8,.x14] := by
  intro r hr
  cases r <;> simp at hr <;> simp [prefixRes, prefixRegs, prefixBase.res, rv_simp] <;> rfl
theorem rest_frame (a : Nat) (u : MachineState) : T3M.Frame u ((prefixRes a).toState u) (fun _ => False) := by
  intro A _ _
  simp [prefixRes, prefixRegs, prefixBase.res, rv_simp, memEval]
theorem rest_obl (a : Nat) (u : MachineState) (h9 : u.getReg .x9 = 0xffbf10#64) :
    ∀ o ∈ (prefixRes a).st.obl, o.holds u := by
  intro o ho
  simp [prefixRes, prefixRegs, prefixBase.res] at ho
  rcases ho with rfl | rfl
  all_goals simp [Oblig.holds, rv_simp, accessValid_iff, MEMORY_BYTES, h9]
/-- R6 prologue tail at word `p` of a top copy (8 words: `blt a7,zero,+32` at `p`, the 7 rest words at `p+1`), with
`s1 = 0xffbf10` (`TOPB9`), the r5 mask at `s1+232` and the r6 mask at `s1-288` (verify data word 16).
Spare bit 127 of `V` set: one step to `p+8` (a zero word in the image: `Nonbinary.spare_fault`). Otherwise 8 steps
to the g0 column with t4 = 0xFF00, s2 = 856064, t1 = 0x7F000, s0 = 13432 and a6/a7 unchanged. -/
theorem prefix_tail_spec6 {im : Image} (s : MachineState) (V : BitVec 128) (a p : Nat) (ha : a ∈ aVals)
    (hpc : s.pc = T3M.pcOf p) (hsp : CodeAt im (T3M.pcOf p) prefixSpare)
    (hrest : CodeAt im (T3M.pcOf (p+1)) (prefixRestWordsOf a))
    (h0 : s.getReg .x16 = V.extractLsb' 0 64) (h1 : s.getReg .x17 = V.extractLsb' 64 64)
    (hra : s.getReg .x9 = 0xffbf10#64)
    (hmask5 : s.getMem 0xffbff8#64 = 520192#64) (hmask6 : s.getMem 0xffbdf0#64 = 65280#64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 a) :
    (V.toNat / 2^127 % 2 = 1 → ∃ t, Steps im s 1 1 t ∧ t.pc = T3M.pcOf (p+8) ∧
        T3M.RegsExcept s t [] ∧ T3M.Frame s t (fun _ => False)) ∧
    (V.toNat / 2^127 % 2 = 0 → ∃ t, Steps im s 8 8 t ∧ t.pc = g0Target V ∧
        t.getReg .x16 = V.extractLsb' 0 64 ∧ t.getReg .x17 = V.extractLsb' 64 64 ∧
        t.getReg .x29 = 65280#64 ∧ t.getReg .x18 = 856064#64 ∧ t.getReg .x8 = 13432#64 ∧
        t.getReg .x6 = 520192#64 ∧ T3M.RegsExcept s t [.x29,.x6,.x18,.x8,.x14] ∧ T3M.Frame s t (fun _ => False)) := by
  have e1 := symRun_sound (prefixSpare_run (T3M.pcOf p)) hsp s hpc (by simp [prefixSpareRes, prefixSpareBase.res, rv_simp])
  have pu := prefixSpare_pc s (T3M.pcOf p) V h1
  have ru := spare_regs (T3M.pcOf p) s
  have fu := spare_frame (T3M.pcOf p) s
  set u := (prefixSpareRes (T3M.pcOf p)).toState s with hu
  refine ⟨fun hb => ⟨u, e1, ?_, ru, fu⟩, fun hb => ?_⟩
  · rw [hu, Result.toState_pc, pu, if_pos hb]
    unfold T3M.pcOf
    rw [show (32 : Word) = BitVec.ofNat 64 32 from rfl, BitVec.ofNat_add_ofNat,
      show 0x1000 + 4 * p + 32 = 0x1000 + 4 * (p + 8) by ring]
  have pu' : u.pc = T3M.pcOf (p+1) := by
    rw [hu, Result.toState_pc, pu, if_neg (by omega)]
    exact T3M.pcOf_add4 p
  have u9 : u.getReg .x9 = 0xffbf10#64 := (ru.get (by simp)).trans hra
  have hm5 : u.getMem (u.getReg .x9 + 232#64) = 520192#64 := by
    rw [u9, show (0xffbf10#64 : Word) + 232#64 = 0xffbff8#64 from rfl, fu.get (by norm_num) (by simp)]; exact hmask5
  have hm6 : u.getMem (u.getReg .x9 + 18446744073709551328#64) = 65280#64 := by
    rw [u9, show (0xffbf10#64 : Word) + 18446744073709551328#64 = 0xffbdf0#64 from rfl, fu.get (by norm_num) (by simp)]
    exact hmask6
  have e2 := symRun_sound (prefix_rest_run a ha (T3M.pcOf (p+1))) hrest u pu'
    ((Oblig.all_iff _ _).mpr (rest_obl a u u9))
  have u16 : u.getReg .x16 = V.extractLsb' 0 64 := (ru.get (by simp)).trans h0
  have u17 : u.getReg .x17 = V.extractLsb' 64 64 := (ru.get (by simp)).trans h1
  have u10 : u.getReg .x10 = BitVec.ofNat 64 a := (ru.get (by simp)).trans h10
  obtain ⟨r8, r18, r6, r29, r16, r17⟩ := rest_regs a ha u u10
  have rr := rest_except a u
  have fr := rest_frame a u
  refine ⟨_, e1.trans e2, rest_pc a u V u16, r16.trans u16, r17.trans u17, r29.trans hm6, r18, r8, r6.trans hm5,
    fun r hr => (rr r hr).trans (ru r (by simp)), (fu.trans fr).mono (by simp)⟩
end SigGolfCandidate.T3M.Verify.Nonbinary
