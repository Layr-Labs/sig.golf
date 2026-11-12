import SigGolfCandidate.SimCore
import SigGolfCandidate.Merge048
import SigGolfCandidate.Merge046
import SigGolfCandidate.FtsExpandSearch
import SigGolfCandidate.Merge055
set_option debug.skipKernelTC true
set_option linter.all false

/-! # FTS carrier grind: the sign stub (`SIGN_STUB`, 25308..25339) behind the nine site trampolines

The FTS tree-node `ecall` at sign site `k` becomes `jal zero, SIGN_TRAMP + 5 k`; the trampoline calls the stub
with `jal a6`. On heaps `8..15` the stub grinds the node for `ftsWidth k` zero bits (it reads `r = 2 - b` off the
return address: 1 for trampolines 0 and 1), with the nonce pad at `a0 + 32` and the answer at `a2`; it then
clears the pad. On other heaps it is one plain `ecall`. `sign_tramp_node` shows the round trip refines
`signNode`. -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash nonceBytes pad64)
open SphincsSecurity (bytesLE bytesLE_length)

attribute [local rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop
  SymState.regs SymState.mem SymState.obl BitVec.ofNat_eq_ofNat

/-- `n` stub words from word `a`. -/
def gw (a b : Nat) : List (BitVec 32) := (signStubWords.drop (a - SIGN_STUB)).take (b - a)

sym_block sE := symRun cfgS (gw 25308 25312) (pcOf 25308) 20
sym_block sE2 := symRun cfgS (gw 25312 25314) (pcOf 25312) 20
sym_block sG := symRun cfgS (gw 25314 25319) (pcOf 25314) 20
sym_block sL := symRun cfgS (gw 25319 25321) (pcOf 25319) 20
sym_block sC := symRun cfgS (gw 25321 25325) (pcOf 25321) 20
sym_block sN := symRun cfgS (gw 25325 25328) (pcOf 25325) 20
sym_block sJ := symRun cfgS (gw 25328 25330) (pcOf 25328) 20
sym_block sD := symRun cfgS (gw 25330 25338) (pcOf 25330) 20
sym_block sP := symRun cfgS (gw 25338 25339) (pcOf 25338) 20
sym_block sQ := symRun cfgS (gw 25339 25340) (pcOf 25339) 20
sym_block sR := symRun cfgS (gw 25333 25338) (pcOf 25333) 20

theorem ult_ofNat' (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  simp [BitVec.ult, toNat_ofNat_lt hx, toNat_ofNat_lt hy]

theorem code_gw {im : Image} (hS : CodeAt im (pcOf SIGN_STUB) signStubWords) (a b : Nat) (ha : SIGN_STUB ≤ a)
    (hb : b ≤ SIGN_STUB + 32) (hab : a ≤ b) : CodeAt im (pcOf a) (gw a b) := by
  have := codeAt_sub (a - SIGN_STUB) hS (seg := gw a b) (by simp [gw, signStubWords_length]; omega) (by simp [gw])
  rwa [show SIGN_STUB + (a - SIGN_STUB) = a by omega] at this

/-- The width selector: NBZ5R (NB) `r = 0` on every trampoline (25317 `addi t6,zero,0`; was `r = 1` iff entered from
trampoline 0 or 1; if-shape kept so signR_lt's split_ifs replays). -/
def signR (tb : Nat) : Nat := if tb + 2 < SIGN_TRAMP + 8 then 0 else 0

theorem signR_width (k : Nat) (hk : k < 9) : 2 - signR (SIGN_TRAMP + 5 * k) = ftsWidth k := by
  interval_cases k <;> decide

/-- The sign FTS tree node at heap `heap` with block `pre ‖ mid ‖ right`: a ground heap-8..15 node is ground for
`b` zero bits (the pad `mid` is zero there); every other node is the plain hash. -/
def signNode (b heap : Nat) (pre mid right : List UInt8) : M (Nat × HashOutput) :=
  if 8 ≤ heap ∧ heap < 16 then groundFold b pre right else (fun a => (0, a)) <$> publicHash (pre ++ mid ++ right)

/-- S5185 (FTS16): the sign grind of a heap-16..31 node of coordinate `0..7` (appended loop 25998..: nonce in pad bytes
32..39, first `n < 256` whose USED half (`ftsHighHeap`) has top bit 0, else the last trial). `signNode` keeps the
heap-8..15 rule; the trampoline round trip dispatches on (coordinate, heap) (`sign_tramp_node`, stub). -/
def signNode16 (heap : Nat) (pre right : List UInt8) : M (Nat × HashOutput) :=
  groundFold 1 pre right
/-- S5185 (FTS16, tier T18): the coordinate-aware sign node: heaps 8..15 width `b`; heaps 16..31 of coordinates 0..7
the half-aware width-1 loop (25998..); every other node plain. The half-aware form replaces `signNode16`'s low-half
`groundFold` (the 25998 loop selects the half by heap parity). -/
def signNodeC (coord b heap : Nat) (pre mid right : List UInt8) : M (Nat × HashOutput) :=
  if 8 ≤ heap ∧ heap < 16 then groundFold b pre right
  else if 16 ≤ heap ∧ heap < 32 ∧ coord ≤ 7 then groundFoldH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 pre right
  else (fun a => (0, a)) <$> publicHash (pre ++ mid ++ right)
/-- Cycles of one sign trampoline round trip. S5185 (FTS16): heaps `>= 16` now pass the 25998 dispatch (2 more words;
5 more for coordinate 8's heaps 16..31) and heaps 16..31 of coordinates 0..7 run the FTS16 loop; `signW` must take the
coordinate (design stub, see stubs.tsv) -- unchanged here. -/
def signW (b heap : Nat) : Nat := if 8 ≤ heap ∧ heap < 16 then 18 * FUEL b + 40 else 25

/-! ### S5185 (FTS16, TIER2 S11): the heap-16..31 grind (sign words 25998..26018, `signCode_88`)

Decoded (A70 `sign.code`): 25998 `addi a7,zero,32`; 25999 `bgeu s2,a7,@25338` (heap >= 32: plain); 26000-26001
`a7 := 105624` (= `pcOf (SIGN_TRAMP + 42)`); 26002 `bgeu a6,a7,@25338` (trampoline 8 = coordinate 8: plain);
26003 `sd t6,1128(zero)`; 26004 `a7 := 0`; trial 26005 `sd a7,32(a0)`, 26006 `ecall`; 26007 `andi a4,s2,1`,
26008 `bne a4,zero,@26011`, 26009 `ld a4,24(a2)` (even heap: high half), 26010 `jal zero,@26012`, 26011
`ld a4,8(a2)` (odd: low half); 26012 `srli a4,a4,63`, 26013 `beq a4,zero,@26018`; 26014 `addi a4,zero,255`,
26015 `beq a7,a4,@26018`; 26016 `addi a7,a7,1`, 26017 `jal zero,@26005`; 26018 `jal zero,@25330` (the common exit:
clear the pad word `a0+32`, restore and clear `t6 a4 a7`, `jalr zero,0(a6)`). Entered from 25313
`bgeu s2,16,@25998` (`e2_spec`). -/

/-- The 21 words at `SIGN16`. -/
def sign16Words : List (BitVec 32) := Images.signCode_88.take 21
/-- The coordinate of the sign trampoline at word `tb` (`SIGN_TRAMP + 5 k`). -/
def signCoord (tb : Nat) : Nat := (tb - SIGN_TRAMP) / 5
/-- The ground sign nodes: heaps 8..15, and heaps 16..31 of coordinates 0..7 (`WCT9.ftsGround`). -/
def isG (coord heap : Nat) : Prop := (8 ≤ heap ∧ heap < 16) ∨ (16 ≤ heap ∧ heap < 32 ∧ coord ≤ 7)
instance (coord heap : Nat) : Decidable (isG coord heap) := by unfold isG; infer_instance
/-- Cycles of one sign trampoline round trip (S5185 FTS16; COMPUTED, 1 cycle per instruction and 8 per one-block
`ecall`): heaps 8..15 as `signW`; the FTS16 loop `15 + 19 n + 17 + 1 + 8 + 3` (`n = FUEL 1` failed trials, even
heap; odd heaps 18 per trial); plain at most 30 (coordinate 8 heaps 16..31: 2 + 6 + 5 + 17). -/
def signWC (coord b heap : Nat) : Nat :=
  if 8 ≤ heap ∧ heap < 16 then 18 * FUEL b + 40
  else if 16 ≤ heap ∧ heap < 32 ∧ coord ≤ 7 then 19 * FUEL 1 + 44 else 30

theorem signWC_le (c h : Nat) : signWC c (ftsWidth c) h ≤ 18 * 511 + 40 := by
  unfold signWC ftsWidth FUEL
  split_ifs <;> norm_num

theorem sign16Words_shape : sign16Words.length = 21 ∧ sign16Words[8]? = some 0x73 ∧
    sign16Words[11]? = some 0x1863703 ∧ sign16Words[13]? = some 0x863703 ∧ sign16Words[20]? = some 0xd40ff06f := by
  decide +kernel

section blocks
variable {im : Image} (hS : CodeAt im (pcOf SIGN_STUB) signStubWords) (s : MachineState)
include hS

theorem e_spec (hpc : s.pc = pcOf 25308) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if heap < 8 then pcOf 25338 else pcOf 25312) ∧ RegsExcept s t [.x17] ∧
      t.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 ∧
      Frame s t (fun X => X = 1104 ∨ X = 1112) := by
  have hc := code_gw hS 25308 25312 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sE hc s hpc (by simp [sE.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sE.res, rv_simp, h18]
    rw [show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ult_ofNat' _ _ hh (by decide)]
    by_cases h : heap < 8 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [sE.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, sE.res]; t3n []
  · simp only [Result.toState_getMem, sE.res]; t3n []
  · intro A hA hn; simp only [Result.toState_getMem, sE.res]; t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem e2_spec (hpc : s.pc = pcOf 25312) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if 16 ≤ heap then pcOf 25998 else pcOf 25314) ∧ RegsExcept s t [.x17] ∧
      Frame s t (fun _ => False) := by
  have hc := code_gw hS 25312 25314 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sE2 hc s hpc (by simp [sE2.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sE2.res, rv_simp, h18]
    rw [show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ult_ofNat' _ _ hh (by decide)]
    by_cases h : 16 ≤ heap
    · simp [h]
    · simp [show heap < 16 by omega, h]
  · intro r hr; simp at hr; cases r <;> simp_all [sE2.res, rv_simp] <;> rfl
  · intro A _ _; simp [sE2.res, rv_simp]

theorem g_spec (hpc : s.pc = pcOf 25314) (tb : Nat) (h16 : s.getReg .x16 = pcOf (tb + 2)) (htb : tb < 2 ^ 18) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 25319 ∧ t.getReg .x31 = BitVec.ofNat 64 (signR tb) ∧
      t.getReg .x17 = 0 ∧ RegsExcept s t [.x17, .x31] ∧ t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧
      Frame s t (fun X => X = 1128) := by
  have hc := code_gw hS 25314 25319 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sG hc s hpc (by simp [sG.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sG.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, sG.res, rv_simp, h16]
    unfold signR; split_ifs <;> rfl
  · simp only [Result.toState_getReg, sG.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [sG.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, sG.res]; t3n []
  · intro A hA hn; simp only [Result.toState_getMem, sG.res]; t3n []; rw [if_neg (by omega)]

theorem sl_spec (hpc : s.pc = pcOf 25319) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 25320 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ Frame s t (fun X => X = A + 32) ∧
      fetch im t = some (.base .ECALL) := by
  have hc := code_gw hS 25319 25321 (by decide) (by decide) (by decide)
  have hob : sL.res.obligs s := by simp only [sL.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound sL hc s hpc hob, ?_, ?_, ?_, ?_, symRun_ecall sL hc s hob rfl⟩
  · simp [sL.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [sL.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, sL.res]; t3n [h10]
  · intro X hX hn; simp only [Result.toState_getMem, sL.res]; t3n [h10]; rw [if_neg (by omega)]

theorem sc_spec (hpc : s.pc = pcOf 25321) (D : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 D) (hD : D % 8 = 0)
    (hD' : D + 32 ≤ 2 ^ 24) (r : Nat) (h31 : s.getReg .x31 = BitVec.ofNat 64 r) (hr : r < 2) :
    ∃ t, Steps im s 4 4 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (D + 8))).toNat < 2 ^ (62 + r) then pcOf 25330 else pcOf 25325) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw hS 25321 25325 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sC hc s hpc (by simp only [sC.res]; t3n [h12]; omega), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sC.res, rv_simp, h12, ofNat_add_ofNat, beq_iff_eq]
    have e62 : ((62#64 : Word).toNat % 64) = 62 := rfl
    simp only [e62, h31]
    have hiff := shr_shr_eq_zero (s.getMem (BitVec.ofNat 64 (D + 8))) r (by omega)
    by_cases h1 : s.getMem (BitVec.ofNat 64 (D + 8)) >>> 62 >>> ((BitVec.ofNat 64 r).toNat % 64) = 0#64
    · rw [if_pos h1]; exact (if_pos (hiff.mp h1)).symm
    · rw [if_neg h1]; exact (if_neg (fun h => h1 (hiff.mpr h))).symm
  · intro r hr; simp at hr; cases r <;> simp_all [sC.res, rv_simp] <;> rfl
  · intro A _ _; simp [sC.res, rv_simp]

theorem sn_spec (hpc : s.pc = pcOf 25325) (r : Nat) (h31 : s.getReg .x31 = BitVec.ofNat 64 r) (hr : r < 2) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getReg .x17 = BitVec.ofNat 64 (511 / 2 ^ r) then pcOf 25330 else pcOf 25328) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw hS 25325 25328 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sN hc s hpc (by simp [sN.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sN.res, rv_simp, h31, beq_iff_eq]
    rw [show (511#64 : Word) = BitVec.ofNat 64 511 from rfl, ofNat_shr' 511 r]
    rw [show r % 2 ^ 64 % 64 = r by omega, show 511 % 2 ^ 64 = 511 from rfl]
  · intro r hr; simp at hr; cases r <;> simp_all [sN.res, rv_simp] <;> rfl
  · intro A _ _; simp [sN.res, rv_simp]

theorem sj_spec (hpc : s.pc = pcOf 25328) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 25319 ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw hS 25328 25330 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sJ hc s hpc (by simp [sJ.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [sJ.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, sJ.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [sJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [sJ.res, rv_simp]

/-- 25330..25337: clear the pad, restore `t6 a4 a7`, clear their saves, return through `a6`. -/
theorem d_spec (hpc : s.pc = pcOf 25330) (A R : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA1 : 1144 ≤ A) (hA' : A + 64 ≤ 2 ^ 24) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf R ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧
      RegsExcept s t [.x14, .x17, .x31] ∧ t.getMem (BitVec.ofNat 64 (A + 32)) = 0 ∧
      t.getMem (BitVec.ofNat 64 1104) = 0 ∧ t.getMem (BitVec.ofNat 64 1112) = 0 ∧
      t.getMem (BitVec.ofNat 64 1128) = 0 ∧
      Frame s t (fun X => X = A + 32 ∨ X = 1104 ∨ X = 1112 ∨ X = 1128) := by
  have hc := code_gw hS 25330 25338 (by decide) (by decide) (by decide)
  have hob : sD.res.obligs s := by simp only [sD.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound sD hc s hpc hob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sD.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, sD.res]; t3n []
  · simp only [Result.toState_getReg, sD.res]; t3n []
  · simp only [Result.toState_getReg, sD.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [sD.res, rv_simp] <;> rfl
  all_goals try (simp only [Result.toState_getMem, sD.res]; t3n [h10]
                 try simp (disch := first | decide | omega) only [if_pos, if_neg, if_true, if_false]
                 done)
  · intro X hX hn; simp only [Result.toState_getMem, sD.res]; t3n [h10]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

/-- 25339: `jal zero, 25333`. -/
theorem q_spec (hpc : s.pc = pcOf 25339) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 25333 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw hS 25339 25340 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sQ hc s hpc (by simp [sQ.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [sQ.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [sQ.res, rv_simp] <;> rfl
  · intro A _ _; simp [sQ.res, rv_simp]

/-- 25333..25337: restore `a4 a7`, clear their saves, return through `a6`. -/
theorem r_spec (hpc : s.pc = pcOf 25333) (R : Nat) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf R ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ RegsExcept s t [.x14, .x17] ∧
      t.getMem (BitVec.ofNat 64 1104) = 0 ∧ t.getMem (BitVec.ofNat 64 1112) = 0 ∧
      Frame s t (fun X => X = 1104 ∨ X = 1112) := by
  have hc := code_gw hS 25333 25338 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sR hc s hpc (by simp [sR.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sR.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, sR.res]; t3n []
  · simp only [Result.toState_getReg, sR.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [sR.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, sR.res]; t3n []
  · simp only [Result.toState_getMem, sR.res]; t3n []
  · intro X hX hn; simp only [Result.toState_getMem, sR.res]; t3n []; rw [if_neg (by omega), if_neg (by omega)]

end blocks


/-! ## The sign trampoline round trip -/

theorem fuelR (r : Nat) (hr : r < 2) : FUEL (2 - r) = 511 / 2 ^ r := by
  have : r = 0 ∨ r = 1 := by omega
  rcases this with rfl | rfl <;> rfl

/-- A sign site trampoline call at word `tb` returning to `ret`: node block `pre ‖ mid ‖ right` at `A`, heap in
`s2`, answer at `D` (disjoint from the block). -/
structure SignIn (tb ret heap A D : Nat) (pre mid right : List UInt8) (s : MachineState) : Prop where
  pc : s.pc = pcOf tb
  x5 : s.getReg .x5 = 0
  x10 : s.getReg .x10 = BitVec.ofNat 64 A
  x11 : s.getReg .x11 = BitVec.ofNat 64 64
  x12 : s.getReg .x12 = BitVec.ofNat 64 D
  x18 : s.getReg .x18 = BitVec.ofNat 64 heap
  hheap : heap < 2 ^ 64
  lpre : pre.length = 32
  lmid : mid.length = 16
  lright : right.length = 16
  mpre : s.readWords (BitVec.ofNat 64 A) 4 = wordsOf pre
  mmid : s.readWords (BitVec.ofNat 64 (A + 32)) 2 = wordsOf mid
  mright : s.readWords (BitVec.ofNat 64 (A + 48)) 2 = wordsOf right
  ground : 8 ≤ heap ∧ heap < 16 → s.getMem (BitVec.ofNat 64 (A + 32)) = 0 ∧ s.getMem (BitVec.ofNat 64 (A + 40)) = 0
  hA : A % 8 = 0
  hA1 : 1144 ≤ A
  hA2 : A + 64 ≤ 2 ^ 24
  hD : D % 8 = 0
  hD1 : 1144 ≤ D
  hD2 : D + 32 ≤ 2 ^ 24
  hAD : A + 64 ≤ D ∨ D + 32 ≤ A
  hb : tb + 5 < 2 ^ 18
  hret : ret < 2 ^ 18

/-- Words a sign stub call may write. -/
def SignW (D : Nat) (X : Nat) : Prop := (D ≤ X ∧ X < D + 32) ∨ X = 1104 ∨ X = 1112 ∨ X = 1128 ∨ X = 1136

/-- Back at `ret` with the node's answer at `D`; the block is unchanged. -/
structure SignOut (s : MachineState) (ret heap D b : Nat) (res : Nat × HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf ret
  regs : RegsExcept s t []
  ans : ∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = res.2.extractLsb' (64 * k) 64
  sv0 : t.getMem (BitVec.ofNat 64 1104) = 0
  sv1 : t.getMem (BitVec.ofNat 64 1112) = 0
  sv4 : t.getMem (BitVec.ofNat 64 1136) = 0
  sv3 : 8 ≤ heap ∧ heap < 16 → t.getMem (BitVec.ofNat 64 1128) = 0
  sv3p : ¬ (8 ≤ heap ∧ heap < 16) → t.getMem (BitVec.ofNat 64 1128) = s.getMem (BitVec.ofNat 64 1128)
  nonce : (8 ≤ heap ∧ heap < 16 → res.1 ≤ FUEL b) ∧ (¬ (8 ≤ heap ∧ heap < 16) → res.1 = 0)
  frame : Frame s t (SignW D)

/-- S5185 (FTS16, TIER2 S11): `SignOut` with the coordinate: heaps 16..31 of coordinates 0..7 are ground too
(the 25998 loop saves `t6` at 1128 and the common exit clears it; nonce `<= FUEL 1`). -/
structure SignOutC (s : MachineState) (ret coord heap D b : Nat) (res : Nat × HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf ret
  regs : RegsExcept s t []
  ans : ∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = res.2.extractLsb' (64 * k) 64
  sv0 : t.getMem (BitVec.ofNat 64 1104) = 0
  sv1 : t.getMem (BitVec.ofNat 64 1112) = 0
  sv4 : t.getMem (BitVec.ofNat 64 1136) = 0
  sv3 : isG coord heap → t.getMem (BitVec.ofNat 64 1128) = 0
  sv3p : ¬ isG coord heap → t.getMem (BitVec.ofNat 64 1128) = s.getMem (BitVec.ofNat 64 1128)
  nonce : (8 ≤ heap ∧ heap < 16 → res.1 ≤ FUEL b) ∧ (16 ≤ heap ∧ heap < 32 ∧ coord ≤ 7 → res.1 ≤ FUEL 1) ∧
    (¬ isG coord heap → res.1 = 0)
  frame : Frame s t (SignW D)

/-- Off the new level-2 ground nodes, `SignOut` is `SignOutC` (so `gexit` / `plain_run` serve the old cases). -/
theorem SignOut.toC {s t : MachineState} {ret coord heap D b : Nat} {res : Nat × HashOutput}
    (h : SignOut s ret heap D b res t) (h2 : ¬ (16 ≤ heap ∧ heap < 32 ∧ coord ≤ 7)) :
    SignOutC s ret coord heap D b res t := by
  have hI : isG coord heap ↔ (8 ≤ heap ∧ heap < 16) := by
    unfold isG; constructor
    · rintro (h | h)
      · exact h
      · exact absurd h h2
    · exact Or.inl
  exact { pc := h.pc, regs := h.regs, ans := h.ans, sv0 := h.sv0, sv1 := h.sv1, sv4 := h.sv4,
          sv3 := fun g => h.sv3 (hI.mp g), sv3p := fun g => h.sv3p (fun g' => g (hI.mpr g')),
          nonce := ⟨h.nonce.1, fun g => absurd g h2, fun g => h.nonce.2 (fun g' => g (hI.mpr g'))⟩,
          frame := h.frame }

/-- Words `a..b` of the FTS16 sign segment. -/
def gw16 (a b : Nat) : List (BitVec 32) := (sign16Words.drop (a - SIGN16)).take (b - a)

theorem code_gw16 {im : Image} (hS : CodeAt im (pcOf SIGN16) sign16Words) (a b : Nat) (ha : SIGN16 ≤ a)
    (hb : b ≤ SIGN16 + 21) (hab : a ≤ b) : CodeAt im (pcOf a) (gw16 a b) := by
  have := codeAt_sub (a - SIGN16) hS (seg := gw16 a b) (by simp [gw16, sign16Words_shape.1]; omega) (by simp [gw16])
  rwa [show SIGN16 + (a - SIGN16) = a by omega] at this

sym_block s16A := symRun cfgS (gw16 25998 26000) (pcOf 25998) 20
sym_block s16B := symRun cfgS (gw16 26000 26003) (pcOf 26000) 20
sym_block s16C := symRun cfgS (gw16 26003 26005) (pcOf 26003) 20
sym_block s16T := symRun cfgS (gw16 26005 26007) (pcOf 26005) 20
sym_block s16c1 := symRun cfgS (gw16 26007 26009) (pcOf 26007) 20
sym_block s16c2 := symRun cfgS (gw16 26009 26011) (pcOf 26009) 20
sym_block s16c3 := symRun cfgS (gw16 26011 26012) (pcOf 26011) 20
sym_block s16c4 := symRun cfgS (gw16 26012 26014) (pcOf 26012) 20
sym_block s16n1 := symRun cfgS (gw16 26014 26016) (pcOf 26014) 20
sym_block s16n2 := symRun cfgS (gw16 26016 26018) (pcOf 26016) 20
sym_block s16X := symRun cfgS (gw16 26018 26019) (pcOf 26018) 20

/-- `x >>> 63 = 0` iff `x < 2^63` (the sign-bit test of the half's top dword). -/
theorem shr63_eq_zerog (x : Word) : x >>> ((63#64 : Word).toNat % 64) = 0#64 ↔ x.toNat < 2 ^ 63 := by
  have e : ((63#64 : Word).toNat % 64) = 63 := rfl
  rw [e]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero, Nat.div_eq_zero_iff] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact h
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero]
    exact Nat.div_eq_of_lt h

section blocks16
variable {im : Image} (hS16 : CodeAt im (pcOf SIGN16) sign16Words) (s : MachineState)
include hS16

theorem gA_spec (hpc : s.pc = pcOf 25998) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if heap < 32 then pcOf 26000 else pcOf 25338) ∧ RegsExcept s t [.x17] ∧
      Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 25998 26000 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16A hc s hpc (by simp [s16A.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, s16A.res, rv_simp, h18]
    rw [show (32#64 : Word) = BitVec.ofNat 64 32 from rfl, ult_ofNat' _ _ hh (by decide)]
    by_cases h : heap < 32
    · simp [h]
    · simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [s16A.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16A.res, rv_simp]

theorem gB_spec (hpc : s.pc = pcOf 26000) (tb : Nat) (h16 : s.getReg .x16 = pcOf (tb + 2)) (htb : tb < 2 ^ 18) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if SIGN_TRAMP + 40 ≤ tb then pcOf 25338 else pcOf 26003) ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26000 26003 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16B hc s hpc (by simp [s16B.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, s16B.res, rv_simp, h16]
    rw [show (105624#64 : Word) = BitVec.ofNat 64 105624 from rfl, ult_ofNat' _ _ (by norm_num at htb ⊢; omega) (by decide)]
    by_cases h : SIGN_TRAMP + 40 ≤ tb
    · have hn : ¬ (0x1000 + 4 * (tb + 2) < 105624) := by unfold SIGN_TRAMP at h; omega
      rw [if_pos h]; simp only [hn, decide_false, Bool.not_false, if_true]
    · have hn : (0x1000 + 4 * (tb + 2) < 105624) := by unfold SIGN_TRAMP at h; omega
      rw [if_neg h]; simp only [hn, decide_true, Bool.not_true]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [s16B.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16B.res, rv_simp]

theorem gC_spec (hpc : s.pc = pcOf 26003) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 26005 ∧ t.getReg .x17 = 0 ∧
      t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧ RegsExcept s t [.x17] ∧
      Frame s t (fun X => X = 1128) := by
  have hc := code_gw16 hS16 26003 26005 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16C hc s hpc (by simp [s16C.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [s16C.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, s16C.res]; simp [rv_simp]
  · simp only [Result.toState_getMem, s16C.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [s16C.res, rv_simp] <;> rfl
  · intro A hA hn; simp only [Result.toState_getMem, s16C.res]; t3n []; rw [if_neg (by omega)]

/-- 25998..26004, strengthened: on the two plain exits no word is written. -/
theorem g16_core (hpc : s.pc = pcOf 25998) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) (tb : Nat) (h16 : s.getReg .x16 = pcOf (tb + 2)) (htb : tb < 2 ^ 18) :
    ∃ t n, Steps im s n n t ∧
      (32 ≤ heap → n = 2 ∧ t.pc = pcOf 25338) ∧
      (heap < 32 → SIGN_TRAMP + 40 ≤ tb → n = 5 ∧ t.pc = pcOf 25338) ∧
      (heap < 32 → tb < SIGN_TRAMP + 40 → n = 7 ∧ t.pc = pcOf 26005 ∧ t.getReg .x17 = 0 ∧
        t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31) ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun X => X = 1128) ∧
      ((32 ≤ heap ∨ SIGN_TRAMP + 40 ≤ tb) → Frame s t (fun _ => False)) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := gA_spec hS16 s hpc heap h18 hh
  by_cases h32 : 32 ≤ heap
  · rw [if_neg (by omega)] at p1
    exact ⟨t1, 2, s1, fun _ => ⟨rfl, p1⟩, fun h => by omega, fun h => by omega, r1, f1.mono (fun _ _ h => h.elim),
      fun _ => f1⟩
  rw [if_pos (by omega)] at p1
  have h16' : t1.getReg .x16 = pcOf (tb + 2) := by rw [r1.get (by decide)]; exact h16
  obtain ⟨t2, s2, p2, r2, f2⟩ := gB_spec hS16 t1 p1 tb h16' htb
  by_cases hc8 : SIGN_TRAMP + 40 ≤ tb
  · rw [if_pos hc8] at p2
    exact ⟨t2, 2 + 3, s1.trans s2, fun h => by omega, fun _ _ => ⟨rfl, p2⟩, fun _ h => by omega,
      (r1.trans r2).mono (by decide), (f1.trans f2).mono (fun _ _ h => by rcases h with h | h <;> exact h.elim),
      fun _ => (f1.trans f2).mono (fun _ _ h => by rcases h with h | h <;> exact h.elim)⟩
  rw [if_neg hc8] at p2
  obtain ⟨t3, s3, p3, x17, m28, r3, f3⟩ := gC_spec hS16 t2 p2
  have x31 : t2.getReg .x31 = s.getReg .x31 := by
    rw [r2.get (by decide), r1.get (by decide)]
  refine ⟨t3, 2 + 3 + 2, s1.trans (s2.trans s3), fun h => by omega, fun _ h => by omega,
    fun _ _ => ⟨rfl, p3, x17, by rw [m28, x31]⟩, ((r1.trans r2).trans r3).mono (by decide), ?_, fun h => by omega⟩
  exact (((f1.trans f2).trans f3)).mono (fun _ _ h => by rcases h with (h | h) | h <;> first | exact h | exact h.elim)

/-- 25998..26004: the FTS16 dispatch. Heap `>= 32`: 2 steps to the plain `ecall` 25338; coordinate 8 (`a6 =
pcOf (tb + 2) >= 105624`, i.e. `tb >= SIGN_TRAMP + 40`): 5 steps to 25338; else save `t6`, `a7 := 0`, 7 steps to the
trial at 26005. -/
theorem g16_spec (hpc : s.pc = pcOf 25998) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) (tb : Nat) (h16 : s.getReg .x16 = pcOf (tb + 2)) (htb : tb < 2 ^ 18) :
    ∃ t n, Steps im s n n t ∧
      (32 ≤ heap → n = 2 ∧ t.pc = pcOf 25338) ∧
      (heap < 32 → SIGN_TRAMP + 40 ≤ tb → n = 5 ∧ t.pc = pcOf 25338) ∧
      (heap < 32 → tb < SIGN_TRAMP + 40 → n = 7 ∧ t.pc = pcOf 26005 ∧ t.getReg .x17 = 0 ∧
        t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31) ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun X => X = 1128) := by
  obtain ⟨t, n, h1, h2, h3, h4, h5, h6, -⟩ := g16_core hS16 s hpc heap h18 hh tb h16 htb
  exact ⟨t, n, h1, h2, h3, h4, h5, h6⟩

/-- 26005..26006: the nonce into pad word `A + 32`, then the trial `ecall`. -/
theorem t16_spec (hpc : s.pc = pcOf 26005) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 26006 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ Frame s t (fun X => X = A + 32) ∧
      fetch im t = some (.base .ECALL) := by
  have hc := code_gw16 hS16 26005 26007 (by decide) (by decide) (by decide)
  have hob : s16T.res.obligs s := by simp only [s16T.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound s16T hc s hpc hob, ?_, ?_, ?_, ?_, symRun_ecall s16T hc s hob rfl⟩
  · simp [s16T.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [s16T.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, s16T.res]; t3n [h10]
  · intro X hX hn; simp only [Result.toState_getMem, s16T.res]; t3n [h10]; rw [if_neg (by omega)]

theorem c1_spec (hpc : s.pc = pcOf 26007) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if heap % 2 = 0 then pcOf 26009 else pcOf 26011) ∧ RegsExcept s t [.x14] ∧
      Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26007 26009 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16c1 hc s hpc (by simp [s16c1.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, s16c1.res, rv_simp, h18]
    rw [ofNat_and1]
    by_cases he : heap % 2 = 0
    · rw [if_pos he]; simp [he]; try rfl
    · have h1 : heap % 2 = 1 := by omega
      rw [if_neg he]; simp [h1]; try rfl
  · intro r hr; simp at hr; cases r <;> simp_all [s16c1.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16c1.res, rv_simp]

theorem c2_spec (hpc : s.pc = pcOf 26009) (D : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 D) (hD : D % 8 = 0)
    (hD' : D + 32 ≤ 2 ^ 24) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 26012 ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 (D + 24)) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26009 26011 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16c2 hc s hpc (by simp only [s16c2.res]; t3n [h12]; omega), ?_, ?_, ?_, ?_⟩
  · simp [s16c2.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, s16c2.res]; t3n [h12]
  · intro r hr; simp at hr; cases r <;> simp_all [s16c2.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16c2.res, rv_simp]

theorem c3_spec (hpc : s.pc = pcOf 26011) (D : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 D) (hD : D % 8 = 0)
    (hD' : D + 32 ≤ 2 ^ 24) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 26012 ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 (D + 8)) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26011 26012 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16c3 hc s hpc (by simp only [s16c3.res]; t3n [h12]; omega), ?_, ?_, ?_, ?_⟩
  · simp [s16c3.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, s16c3.res]; t3n [h12]
  · intro r hr; simp at hr; cases r <;> simp_all [s16c3.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16c3.res, rv_simp]

theorem c4_spec (hpc : s.pc = pcOf 26012) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if (s.getReg .x14).toNat < 2 ^ 63 then pcOf 26018 else pcOf 26014) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26012 26014 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16c4 hc s hpc (by simp [s16c4.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, s16c4.res, rv_simp]
    by_cases hlt : (s.getReg .x14).toNat < 2 ^ 63
    · rw [if_pos hlt]; simp only [beq_iff_eq, shr63_eq_zerog, hlt, if_true]; try rfl
    · rw [if_neg hlt]; simp only [beq_iff_eq, shr63_eq_zerog, hlt, if_false]; try rfl
  · intro r hr; simp at hr; cases r <;> simp_all [s16c4.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16c4.res, rv_simp]

/-- 26007..26013: the half test by heap parity (even heap: the high half's top dword at `D + 24`; odd: `D + 8`),
top bit 0 exits to 26018, else 26014. -/
theorem c16_spec (hpc : s.pc = pcOf 26007) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) (D : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 D) (hD : D % 8 = 0)
    (hD' : D + 32 ≤ 2 ^ 24) :
    ∃ t, Steps im s (if heap % 2 = 0 then 6 else 5) (if heap % 2 = 0 then 6 else 5) t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (D + if heap % 2 = 0 then 24 else 8))).toNat < 2 ^ 63
        then pcOf 26018 else pcOf 26014) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := c1_spec hS16 s hpc heap h18 hh
  have h12' : t1.getReg .x12 = BitVec.ofNat 64 D := by rw [r1.get (by decide)]; exact h12
  have fm : ∀ X, X < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) :=
    fun X hX => f1.get hX (fun h => h)
  by_cases he : heap % 2 = 0
  · rw [if_pos he] at p1
    rw [if_pos he, if_pos he]
    obtain ⟨t2, s2, p2, x14, r2, f2⟩ := c2_spec hS16 t1 p1 D h12' hD hD'
    obtain ⟨t3, s3, p3, r3, f3⟩ := c4_spec hS16 t2 p2
    have hm : t2.getMem (BitVec.ofNat 64 (D + 24)) = s.getMem (BitVec.ofNat 64 (D + 24)) := by
      rw [f2.get (by omega) (fun h => h), fm _ (by omega)]
    have x14' : t2.getReg .x14 = s.getMem (BitVec.ofNat 64 (D + 24)) := by rw [x14, fm _ (by omega)]
    refine ⟨t3, s1.trans (s2.trans s3), ?_, ((r1.trans r2).trans r3).mono (by decide),
      ((f1.trans f2).trans f3).mono (fun _ _ h => by rcases h with (h | h) | h <;> exact h.elim)⟩
    rw [p3, x14']
  · rw [if_neg he] at p1
    rw [if_neg he, if_neg he]
    obtain ⟨t2, s2, p2, x14, r2, f2⟩ := c3_spec hS16 t1 p1 D h12' hD hD'
    obtain ⟨t3, s3, p3, r3, f3⟩ := c4_spec hS16 t2 p2
    have x14' : t2.getReg .x14 = s.getMem (BitVec.ofNat 64 (D + 8)) := by rw [x14, fm _ (by omega)]
    refine ⟨t3, s1.trans (s2.trans s3), ?_, ((r1.trans r2).trans r3).mono (by decide),
      ((f1.trans f2).trans f3).mono (fun _ _ h => by rcases h with (h | h) | h <;> exact h.elim)⟩
    rw [p3, x14']

theorem n1_spec (hpc : s.pc = pcOf 26014) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if s.getReg .x17 = BitVec.ofNat 64 255 then pcOf 26018 else pcOf 26016) ∧
      t.getReg .x17 = s.getReg .x17 ∧ RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26014 26016 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16n1 hc s hpc (by simp [s16n1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, s16n1.res, rv_simp]
    by_cases h : s.getReg .x17 = BitVec.ofNat 64 255
    · simp [h]; try rfl
    · simp [h]; try rfl
  · simp only [Result.toState_getReg, s16n1.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [s16n1.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16n1.res, rv_simp]

theorem n2_spec (hpc : s.pc = pcOf 26016) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 26005 ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26016 26018 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16n2 hc s hpc (by simp [s16n2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [s16n2.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, s16n2.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [s16n2.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16n2.res, rv_simp]

/-- 26014..26017: stop after nonce 255, else the next nonce and back to 26005. -/
theorem n16_spec (hpc : s.pc = pcOf 26014) :
    ∃ t n, Steps im s n n t ∧
      (s.getReg .x17 = BitVec.ofNat 64 255 → n = 2 ∧ t.pc = pcOf 26018 ∧ t.getReg .x17 = s.getReg .x17) ∧
      (s.getReg .x17 ≠ BitVec.ofNat 64 255 → n = 4 ∧ t.pc = pcOf 26005 ∧ t.getReg .x17 = s.getReg .x17 + 1#64) ∧
      RegsExcept s t [.x14, .x17] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, x17, r1, f1⟩ := n1_spec hS16 s hpc
  by_cases h : s.getReg .x17 = BitVec.ofNat 64 255
  · rw [if_pos h] at p1
    exact ⟨t1, 2, s1, fun _ => ⟨rfl, p1, x17⟩, fun h' => absurd h h', r1.mono (by decide), f1⟩
  · rw [if_neg h] at p1
    obtain ⟨t2, s2, p2, x17', r2, f2⟩ := n2_spec hS16 t1 p1
    refine ⟨t2, 2 + 2, s1.trans s2, fun h' => absurd h' h, fun _ => ⟨rfl, p2, by rw [x17', x17]⟩,
      (r1.trans r2).mono (by decide), (f1.trans f2).mono (fun _ _ h => by rcases h with h | h <;> exact h.elim)⟩

/-- 26018: `jal zero, 25330` into the common exit (`d_spec`). -/
theorem x16_spec (hpc : s.pc = pcOf 26018) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 25330 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw16 hS16 26018 26019 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound s16X hc s hpc (by simp [s16X.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [s16X.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [s16X.res, rv_simp] <;> rfl
  · intro A _ _; simp [s16X.res, rv_simp]

end blocks16

def sgRegs : List Reg := [.x14, .x16, .x17, .x31]
def GW (A D : Nat) (X : Nat) : Prop := X = A + 32 ∨ SignW D X

/-- In the ground loop at word `pcw` with nonce `n`. -/
structure AtG (s : MachineState) (tb A D pcw n : Nat) (u : MachineState) : Prop where
  pc : u.pc = pcOf pcw
  regs : RegsExcept s u sgRegs
  x16 : u.getReg .x16 = pcOf (tb + 2)
  x17 : u.getReg .x17 = BitVec.ofNat 64 n
  x31 : u.getReg .x31 = BitVec.ofNat 64 (signR tb)
  sv0 : u.getMem (BitVec.ofNat 64 1104) = s.getReg .x14
  sv1 : u.getMem (BitVec.ofNat 64 1112) = s.getReg .x17
  sv3 : u.getMem (BitVec.ofNat 64 1128) = s.getReg .x31
  sv4 : u.getMem (BitVec.ofNat 64 1136) = s.getReg .x16
  frame : Frame s u (GW A D)
  hn : n ≤ FUEL (2 - signR tb)

structure HashedS (u : MachineState) (A D n : Nat) (a : HashOutput) : Prop where
  ans : ∀ k < 4, u.getMem (BitVec.ofNat 64 (D + 8 * k)) = a.extractLsb' (64 * k) 64
  p32 : u.getMem (BitVec.ofNat 64 (A + 32)) = BitVec.ofNat 64 n

theorem signR_lt (tb : Nat) : signR tb < 2 := by unfold signR; split_ifs <;> decide

/-! ### S5185 (FTS16, TIER2 S11): the level-2 grind loop (26005..26017) -/

/-- What follows the trial-`n` hash in `searchH` (fuel = trials left). -/
def sTailHg (hi : Bool) (b : Nat) (pre right : List UInt8) : Nat → Nat → HashOutput → M (Nat × HashOutput)
  | 0, n, a => pure (n, a)
  | fuel + 1, n, a => if zeroOkH hi b a then pure (n, a) else searchH hi b pre right fuel (n + 1)

theorem searchH_eqg (hi : Bool) (b : Nat) (pre right : List UInt8) (fuel n : Nat) :
    searchH hi b pre right fuel n = publicHash (trialInput pre n right) >>= sTailHg hi b pre right fuel n := by
  cases fuel <;> rfl

/-- A 128-bit window at bit `o` is below `2^127` iff its top dword (at `o + 64`) is below `2^63`. -/
theorem half_lt (a : HashOutput) (o : Nat) :
    (a.extractLsb' o 128).toNat < 2 ^ 127 ↔ (a.extractLsb' (o + 64) 64).toNat < 2 ^ 63 := by
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have e : a.toNat / 2 ^ (o + 64) % 2 ^ 64 = a.toNat / 2 ^ o % 2 ^ 128 / 2 ^ 64 := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num,
      Nat.mod_mul_right_div_self]
  rw [e, Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num

/-- On heaps `>= 16` the half-aware trial test reads the top dword of the used half: the high half (word 3) on even
heaps, the low half (word 1) on odd heaps. -/
theorem zeroOkH_iff16 (heap : Nat) (h16 : 16 ≤ heap) (a : HashOutput) :
    zeroOkH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 a = true ↔
      (a.extractLsb' (if heap % 2 = 0 then 192 else 64) 64).toNat < 2 ^ 63 := by
  by_cases he : heap % 2 = 0
  · have hh : ClaudeWCT.WCT9.ftsHighHeap heap = true := by
      simp [ClaudeWCT.WCT9.ftsHighHeap]; omega
    rw [hh, if_pos he]
    unfold zeroOkH
    simp only [if_true, decide_eq_true_eq]
    exact half_lt a 128
  · have hh : ClaudeWCT.WCT9.ftsHighHeap heap = false := by
      simp [ClaudeWCT.WCT9.ftsHighHeap]; omega
    rw [hh, if_neg he]
    unfold zeroOkH
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq]
    exact half_lt a 0

/-- In the level-2 grind loop at word `pcw` with nonce `n` (`<= 255`). -/
structure AtH (s : MachineState) (tb A D pcw n : Nat) (u : MachineState) : Prop where
  pc : u.pc = pcOf pcw
  regs : RegsExcept s u sgRegs
  x16 : u.getReg .x16 = pcOf (tb + 2)
  x17 : u.getReg .x17 = BitVec.ofNat 64 n
  sv0 : u.getMem (BitVec.ofNat 64 1104) = s.getReg .x14
  sv1 : u.getMem (BitVec.ofNat 64 1112) = s.getReg .x17
  sv3 : u.getMem (BitVec.ofNat 64 1128) = s.getReg .x31
  sv4 : u.getMem (BitVec.ofNat 64 1136) = s.getReg .x16
  frame : Frame s u (GW A D)
  hn : n ≤ 255

theorem AtH.move {s : MachineState} {tb A D pcw pcw' n n' : Nat} {u w : MachineState} (h : AtH s tb A D pcw n u)
    (hpc : w.pc = pcOf pcw') (hr : RegsExcept u w [.x14, .x17]) (hf : Frame u w (fun _ => False))
    (h17 : w.getReg .x17 = BitVec.ofNat 64 n') (hn : n' ≤ 255) : AtH s tb A D pcw' n' w where
  pc := hpc
  regs := (h.regs.trans hr).mono (by decide)
  x16 := by rw [hr.get (by decide)]; exact h.x16
  x17 := h17
  sv0 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv0
  sv1 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv1
  sv3 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv3
  sv4 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv4
  frame := (h.frame.trans hf).mono (fun _ _ h => by rcases h with h | h; exact h; exact h.elim)
  hn := hn

section run
variable {im : Image} {sk : BitVec 256} {tb ret heap A D : Nat} {pre mid right : List UInt8} {s : MachineState}
  (hS : CodeAt im (pcOf SIGN_STUB) signStubWords) (hT : CodeAt im (pcOf tb) (trampWords tb SIGN_STUB ret))
  (F : SignIn tb ret heap A D pre mid right s)
include hS hT F

omit hS hT F in
theorem AtG.move {pcw pcw' n n' : Nat} {u w : MachineState} (h : AtG s tb A D pcw n u) (hpc : w.pc = pcOf pcw')
    (hr : RegsExcept u w [.x14, .x17]) (hf : Frame u w (fun _ => False)) (h17 : w.getReg .x17 = BitVec.ofNat 64 n')
    (hn : n' ≤ FUEL (2 - signR tb)) : AtG s tb A D pcw' n' w where
  pc := hpc
  regs := (h.regs.trans hr).mono (by decide)
  x16 := by rw [hr.get (by decide)]; exact h.x16
  x17 := h17
  x31 := by rw [hr.get (by decide)]; exact h.x31
  sv0 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv0
  sv1 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv1
  sv3 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv3
  sv4 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv4
  frame := (h.frame.trans hf).mono (fun _ _ h => by rcases h with h | h; exact h; exact h.elim)
  hn := hn

omit hS hT in
theorem HashedS.move {n : Nat} {a : HashOutput} {u w : MachineState} (h : HashedS u A D n a)
    (hf : Frame u w (fun _ => False)) : HashedS w A D n a where
  ans k hk := by rw [hf.get (by have := F.hD2; omega) (fun h => h)]; exact h.ans k hk
  p32 := by rw [hf.get (by have := F.hA2; omega) (fun h => h)]; exact h.p32

/-- The ground exit 25330 -> `ret`. -/
theorem gexit {n : Nat} {a : HashOutput} {v : MachineState} (hg : 8 ≤ heap ∧ heap < 16)
    (hv : AtG s tb A D 25330 n v) (hh : HashedS v A D n a) :
    TBSim im sk v 11 (pure (n, a)) (SignOut s ret heap D (2 - signR tb)) := by
  have hb := F.hb; have hret := F.hret; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1
  have hD2 := F.hD2; have hAD := F.hAD
  obtain ⟨t1, s1, p1, x14, x17, x31, r1, m32, m04, m12, m28, f1⟩ :=
    d_spec hS v hv.pc A (tb + 2) (by rw [hv.regs.get (by decide)]; exact F.x10) F.hA hA1 hA2 hv.x16
  obtain ⟨t2, s2, p2, x16, r2, m36, f2⟩ := tramp_tail hT hb hret t1 p1
  have t2m : ∀ X, X < 2 ^ 64 → X ≠ 1136 → t2.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => f2.get hX h
  have t1m : ∀ X, X < 2 ^ 64 → X ≠ A + 32 → X ≠ 1104 → X ≠ 1112 → X ≠ 1128 →
      t1.getMem (BitVec.ofNat 64 X) = v.getMem (BitVec.ofNat 64 X) := fun X hX a b c d =>
    f1.get hX (by rintro (h | h | h | h) <;> contradiction)
  refine tb_pure_steps (s1.trans s2) ⟨p2, ?_, ?_, ?_, ?_, m36, fun _ => ?_, fun h => absurd hg h, ⟨fun _ => hv.hn, fun h => absurd hg h⟩, ?_⟩
  · intro r _
    by_cases h16 : r = .x16
    · subst h16; rw [x16, t1m _ (by decide) (by omega) (by decide) (by decide) (by decide), hv.sv4]
    rw [r2.get (by simpa using h16)]
    by_cases hr : r ∈ [Reg.x14, .x17, .x31]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [x14, hv.sv0]
      · rw [x17, hv.sv1]
      · rw [x31, hv.sv3]
    · have hr' : r ∉ sgRegs := by
        simp only [sgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
      rw [r1.get hr, hv.regs.get hr']
  · intro k hk
    rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by omega) (by omega) (by omega), hh.ans k hk]
  · rw [t2m _ (by decide) (by decide)]; exact m04
  · rw [t2m _ (by decide) (by decide)]; exact m12
  · rw [t2m _ (by decide) (by decide)]; exact m28
  · intro X hX hn
    by_cases hp : X = A + 32
    · subst hp
      rw [t2m _ hX (by omega), m32, (F.ground hg).1]
    · have h1 : ¬ GW A D X := by unfold GW; exact fun h => h.elim hp hn
      rw [t2m _ hX (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h))))),
        t1m _ hX hp (fun h => hn (Or.inr (Or.inl h))) (fun h => hn (Or.inr (Or.inr (Or.inl h))))
          (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h))))), hv.frame.get hX h1]

/-- One ground trial: pad `n`, then the hash of the trial block into `D`. -/
theorem gtrial {β : Type} {n : Nat} {u : MachineState} (hg : 8 ≤ heap ∧ heap < 16)
    (hu : AtG s tb A D 25319 n u) {W : Nat} {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (h : ∀ a w, AtG s tb A D 25321 n w → HashedS w A D n a → TBSim im sk w W (f a) Q) :
    TBSim im sk u (1 + (8 + W)) (publicHash (trialInput pre n right) >>= f) Q := by
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1; have hD2 := F.hD2
  have hAD := F.hAD
  have hnF : n < 2 ^ 64 := by
    have h1 := hu.hn
    rw [fuelR _ (signR_lt tb)] at h1
    have := Nat.div_le_self 511 (2 ^ signR tb)
    omega
  have g10 : u.getReg .x10 = BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)]; exact F.x10
  obtain ⟨u1, s1, p1, r1, m32, f1, fe1⟩ := sl_spec hS u hu.pc A g10 hA hA2
  rw [hu.x17] at m32
  have fs1 : Frame s u1 (GW A D) := (hu.frame.trans f1).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inl h)
  have g1 : ∀ x, x ∉ sgRegs → u1.getReg x = s.getReg x := fun x hx => by
    rw [r1.get (by simp), hu.regs.get hx]
  have h12 : u1.getReg .x12 = BitVec.ofNat 64 D := by rw [g1 _ (by decide)]; exact F.x12
  have hl := trialInput_length pre right n F.lpre F.lright
  have notW : ∀ X, A ≤ X → X < A + 64 → X ≠ A + 32 → ¬ GW A D X := fun X h1 h2 h3 hw => by
    unfold GW SignW at hw; omega
  have m40 : u1.getMem (BitVec.ofNat 64 (A + 40)) = 0 := by
    rw [fs1.get (by omega) (notW _ (by omega) (by omega) (by omega))]; exact (F.ground hg).2
  have hq : hashInput u1 = toQ (pad64 (trialInput pre n right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u1 _ 0 A hl (by rw [g1 _ (by decide)]; exact F.x10) hA (by omega)
      (by rw [g1 _ (by decide)]; exact F.x11) (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_add, readWords_add,
      frame_readWordsG fs1 A 4 (by omega) (fun i hi => notW _ (by omega) (by omega) (by omega)),
      show A + 8 * 4 = A + 32 by ring, readWords_two, m32, m40, show A + 32 + 8 * 2 = A + 48 by ring,
      frame_readWordsG fs1 (A + 48) 2 (by omega) (fun i hi => notW _ (by omega) (by omega) (by omega)),
      F.mpre, F.mright, trialInput, wordsOf_append _ _ (by rw [List.length_append, F.lpre]; simp [nonceBytes,
        bytesLE_length]), wordsOf_append _ _ (by rw [F.lpre]), nonce_words n hnF]
  have hv : hashArgumentsValid u1 = true := hashArgs_const u1 A 64 D (by rw [g1 _ (by decide)]; exact F.x10)
    (by rw [g1 _ (by decide)]; exact F.x11) h12 hA (by norm_num) hA2 F.hD hD2
  have h5 : u1.getReg .x5 = 0 := by rw [g1 _ (by decide)]; exact F.x5
  have e := tb_pub (sk := sk) (W := W) (f := f) (Q := Q) fe1 h5 hv hq (fun a => ?_)
  · have := TBSim.steps s1 e
    rwa [trial_blocks pre right n F.lpre F.lright] at this
  have hwf := Frame.writeHash u1 a D h12 (by omega)
  have fw : Frame s (writeHash u1 a) (GW A D) := (fs1.trans hwf).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inl h))
  have keep : ∀ X, X < 2 ^ 64 → ¬ (D ≤ X ∧ X < D + 32) →
      (writeHash u1 a).getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) := fun X hX h => hwf.get hX h
  have keepu : ∀ X, X < 2 ^ 64 → X ≠ A + 32 →
      u1.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := fun X hX h1 => f1.get hX h1
  refine h a (writeHash u1 a) ⟨by rw [pc_writeHash, p1, pcOf_add4], fun x hx => by rw [getReg_writeHash, g1 x hx],
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x16, by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x17,
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x31,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv0,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv1,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv3,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv4,
    fw, hu.hn⟩ ⟨fun k hk => ?_, by rw [keep _ (by omega) (by omega)]; exact m32⟩
  rw [getMem_writeHash u1 a D _ h12 (by omega) (by omega)]
  interval_cases k <;> simp

theorem gloop (hg : 8 ≤ heap ∧ heap < 16) : ∀ fuel n u, AtG s tb A D 25319 n u →
    n + fuel = FUEL (2 - signR tb) →
    TBSim im sk u (18 * fuel + 27) (search (2 - signR tb) pre right fuel n) (SignOut s ret heap D (2 - signR tb)) := by
  have hr := signR_lt tb
  have hF := fuelR _ hr
  have hFl : FUEL (2 - signR tb) < 2 ^ 64 := by rw [hF]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)
  have hD := F.hD; have hD2 := F.hD2
  have test : ∀ n a w, AtG s tb A D 25321 n w → HashedS w A D n a → ∃ w1, Steps im w 4 4 w1 ∧
      AtG s tb A D (if zeroOk (2 - signR tb) a = true then 25330 else 25325) n w1 ∧ HashedS w1 A D n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := sc_spec hS w hw.pc D (by rw [hw.regs.get (by decide)]; exact F.x12) hD
      (by omega) _ hw.x31 hr
    have e : (w.getMem (BitVec.ofNat 64 (D + 8))).toNat < 2 ^ (62 + signR tb) ↔
        zeroOk (2 - signR tb) a = true := by
      rw [zeroOk_iff a _ hr]
      have := hh.ans 1 (by decide)
      simp only [Nat.mul_one] at this
      rw [this]
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move F f1⟩
    rw [p1]; by_cases hz : zeroOk (2 - signR tb) a = true
    · rw [if_pos (e.mpr hz), if_pos hz]
    · rw [if_neg (fun h => hz (e.mp h)), if_neg hz]
  have capT : ∀ n a w, AtG s tb A D 25325 n w → HashedS w A D n a → ∃ w1, Steps im w 3 3 w1 ∧
      AtG s tb A D (if n = FUEL (2 - signR tb) then 25330 else 25328) n w1 ∧ HashedS w1 A D n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := sn_spec hS w hw.pc _ hw.x31 hr
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move F f1⟩
    have hnl : n < 2 ^ 64 := by have := hw.hn; omega
    rw [p1, hw.x17]
    by_cases hz : n = FUEL (2 - signR tb)
    · rw [if_pos (by rw [hz, hF]), if_pos hz]
    · rw [if_neg (fun h => hz ((ofNat_inj hnl hFl).mp (h.trans (congrArg _ hF.symm)))), if_neg hz]
  intro fuel
  induction fuel with
  | zero =>
    intro n u hu hn
    simp only [Nat.add_zero] at hn
    rw [search_eq]
    refine (gtrial hS hT F hg hu (W := 18) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOk (2 - signR tb) a = true
    · rw [if_pos hz] at hw1
      exact (TBSim.steps s1 (gexit hS hT F hg hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_pos hn] at hw2
      exact TBSim.steps s1 (TBSim.steps s2 (gexit hS hT F hg hw2 hh2))
  | succ fuel ih =>
    intro n u hu hn
    rw [search_eq]
    refine (gtrial hS hT F hg hu (W := 18 * fuel + 36) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOk (2 - signR tb) a = true
    · rw [if_pos hz] at hw1
      simp only [sTail, hz, if_true]
      exact (TBSim.steps s1 (gexit hS hT F hg hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      simp only [sTail, hz, Bool.false_eq_true, if_false]
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_neg (by omega)] at hw2
      obtain ⟨w3, s3, p3, x17, r3, f3⟩ := sj_spec hS w2 hw2.pc
      have hw3 : AtG s tb A D 25319 (n + 1) w3 := hw2.move p3 (r3.mono (by decide)) f3
        (by rw [x17, hw2.x17, ofNat_add_ofNat]) (by omega)
      have := TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 (ih (n + 1) w3 hw3 (by omega))))
      exact this.mono (by omega) (fun _ _ h => h)

/-- The plain path from the `ecall` at 25338: one hash, `jal`, restore, trampoline tail. -/
theorem plain_run {u : MachineState} (hng : ¬ (8 ≤ heap ∧ heap < 16)) (hpc : u.pc = pcOf 25338)
    (hr : RegsExcept s u [.x16, .x17]) (h16 : u.getReg .x16 = pcOf (tb + 2))
    (sv0 : u.getMem (BitVec.ofNat 64 1104) = s.getReg .x14) (sv1 : u.getMem (BitVec.ofNat 64 1112) = s.getReg .x17)
    (sv4 : u.getMem (BitVec.ofNat 64 1136) = s.getReg .x16)
    (hf : Frame s u (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136)) :
    TBSim im sk u 17 ((fun a => (0, a)) <$> publicHash (pre ++ mid ++ right))
      (SignOut s ret heap D (2 - signR tb)) := by
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1; have hD2 := F.hD2
  have hAD := F.hAD; have hb := F.hb; have hret := F.hret
  have fe : fetch im u = some (.base .ECALL) := by
    have hc := code_gw hS 25338 25339 (by decide) (by decide) (by decide)
    have e : gw 25338 25339 = [0x73] := by decide
    rw [e] at hc
    exact (hc.fetch u hpc).trans rfl
  have g : ∀ x, x ≠ .x16 → x ≠ .x17 → u.getReg x = s.getReg x := fun x h1 h2 => hr.get (by simp [h1, h2])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 D := by rw [g _ (by decide) (by decide)]; exact F.x12
  have hl : (pre ++ mid ++ right).length = 64 := by simp [F.lpre, F.lmid, F.lright]
  have nb : ∀ X, A ≤ X → X < A + 64 → ¬ (X = 1104 ∨ X = 1112 ∨ X = 1136) := fun X h1 _ h => by omega
  have hq : hashInput u = toQ (pad64 (pre ++ mid ++ right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u _ 0 A hl (by rw [g _ (by decide) (by decide)]; exact F.x10) hA (by omega)
      (by rw [g _ (by decide) (by decide)]; exact F.x11) (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_add, readWords_add,
      frame_readWordsG hf A 4 (by omega) (fun i hi => nb _ (by omega) (by omega)),
      show A + 8 * 4 = A + 32 by ring,
      frame_readWordsG hf (A + 32) 2 (by omega) (fun i hi => nb _ (by omega) (by omega)),
      show A + 32 + 8 * 2 = A + 48 by ring,
      frame_readWordsG hf (A + 48) 2 (by omega) (fun i hi => nb _ (by omega) (by omega)),
      F.mpre, F.mmid, F.mright, wordsOf_append _ _ (by rw [List.length_append, F.lpre, F.lmid]),
      wordsOf_append _ _ (by rw [F.lpre])]
  have hv : hashArgumentsValid u = true := hashArgs_const u A 64 D (by rw [g _ (by decide) (by decide)]; exact F.x10)
    (by rw [g _ (by decide) (by decide)]; exact F.x11) h12 hA (by norm_num) hA2 F.hD hD2
  have h5 : u.getReg .x5 = 0 := by rw [g _ (by decide) (by decide)]; exact F.x5
  have hbl : (toQ (pad64 (pre ++ mid ++ right))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; omega, by rw [hl]⟩, hl]
  rw [map_eq_bind_pure_comp]
  have := tb_pub (sk := sk) (W := 9) (f := pure ∘ fun a => ((0 : Nat), a))
    (Q := SignOut s ret heap D (2 - signR tb)) fe h5 hv hq (fun a => ?_)
  · rwa [hbl] at this
  have hwf := Frame.writeHash u a D h12 (by omega)
  obtain ⟨w1, s1, p1, r1, f1⟩ := q_spec hS (writeHash u a) (by rw [pc_writeHash, hpc, pcOf_add4])
  obtain ⟨w2, s2, p2, x14, x17, r2, m04, m12, f2⟩ := r_spec hS w1 p1 (tb + 2)
    (by rw [r1.get (by simp), getReg_writeHash]; exact h16)
  obtain ⟨w3, s3, p3, x16, r3, m36, f3⟩ := tramp_tail hT hb hret w2 p2
  have mm : ∀ X, X < 2 ^ 64 → X ≠ 1104 → X ≠ 1112 → X ≠ 1136 →
      w3.getMem (BitVec.ofNat 64 X) = (writeHash u a).getMem (BitVec.ofNat 64 X) := fun X hX a1 a2 a3 => by
    rw [f3.get hX a3, f2.get hX (by rintro (h | h) <;> contradiction), f1.get hX (fun h => h)]
  have w1m : ∀ X, X < 2 ^ 64 → w1.getMem (BitVec.ofNat 64 X) = (writeHash u a).getMem (BitVec.ofNat 64 X) :=
    fun X hX => f1.get hX (fun h => h)
  refine tb_pure_steps (s1.trans (s2.trans s3)) ⟨p3, ?_, ?_, ?_, ?_, m36, fun h => absurd h hng, fun _ => ?_,
    ⟨fun h => absurd h hng, fun _ => rfl⟩, ?_⟩
  · intro r _
    by_cases h16' : r = .x16
    · subst h16'
      rw [x16, f2.get (by decide) (by omega), w1m _ (by decide), hwf.get (by decide) (by omega), sv4]
    rw [r3.get (by simpa using h16')]
    by_cases h14 : r = .x14
    · subst h14; rw [x14, w1m _ (by decide), hwf.get (by decide) (by omega), sv0]
    by_cases h17 : r = .x17
    · subst h17; rw [x17, w1m _ (by decide), hwf.get (by decide) (by omega), sv1]
    rw [r2.get (by simp [h14, h17]), r1.get (by simp), getReg_writeHash, g _ h16' h17]
  · intro k hk
    rw [mm _ (by omega) (by omega) (by omega) (by omega), getMem_writeHash u a D _ h12 (by omega) (by omega)]
    interval_cases k <;> simp
  · rw [f3.get (by decide) (by decide)]; exact m04
  · rw [f3.get (by decide) (by decide)]; exact m12
  · rw [mm _ (by decide) (by decide) (by decide) (by decide), hwf.get (by decide) (by omega),
      hf.get (by decide) (by decide)]
  · intro X hX hn
    have hn' : ¬ (D ≤ X ∧ X < D + 32) := fun h => hn (Or.inl h)
    have h1 : X ≠ 1104 := fun h => hn (Or.inr (Or.inl h))
    have h2 : X ≠ 1112 := fun h => hn (Or.inr (Or.inr (Or.inl h)))
    have h4 : X ≠ 1136 := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h))))
    rw [mm _ hX h1 h2 h4, hwf.get hX hn', hf.get hX (by rintro (h | h | h) <;> contradiction)]

/-- The level-2 ground exit 25330 -> `ret` (`SignOutC`: the loop's nonce is `<= 255`). -/
theorem gexit16 {n : Nat} {a : HashOutput} {v : MachineState} (hg : 16 ≤ heap ∧ heap < 32 ∧ signCoord tb ≤ 7)
    (hp32 : s.getMem (BitVec.ofNat 64 (A + 32)) = 0)
    (hv : AtH s tb A D 25330 n v) (hh : HashedS v A D n a) :
    TBSim im sk v 11 (pure (n, a)) (SignOutC s ret (signCoord tb) heap D (2 - signR tb)) := by
  have hb := F.hb; have hret := F.hret; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1
  have hD2 := F.hD2; have hAD := F.hAD
  have hisG : isG (signCoord tb) heap := Or.inr hg
  obtain ⟨t1, s1, p1, x14, x17, x31, r1, m32, m04, m12, m28, f1⟩ :=
    d_spec hS v hv.pc A (tb + 2) (by rw [hv.regs.get (by decide)]; exact F.x10) F.hA hA1 hA2 hv.x16
  obtain ⟨t2, s2, p2, x16, r2, m36, f2⟩ := tramp_tail hT hb hret t1 p1
  have t2m : ∀ X, X < 2 ^ 64 → X ≠ 1136 → t2.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => f2.get hX h
  have t1m : ∀ X, X < 2 ^ 64 → X ≠ A + 32 → X ≠ 1104 → X ≠ 1112 → X ≠ 1128 →
      t1.getMem (BitVec.ofNat 64 X) = v.getMem (BitVec.ofNat 64 X) := fun X hX a b c d =>
    f1.get hX (by rintro (h | h | h | h) <;> contradiction)
  have hF1 : FUEL 1 = 255 := rfl
  refine tb_pure_steps (s1.trans s2) ⟨p2, ?_, ?_, ?_, ?_, m36, fun _ => ?_, fun h => absurd hisG h,
    ⟨fun h => by omega, fun _ => by rw [hF1]; exact hv.hn, fun h => absurd hisG h⟩, ?_⟩
  · intro r _
    by_cases h16 : r = .x16
    · subst h16; rw [x16, t1m _ (by decide) (by omega) (by decide) (by decide) (by decide), hv.sv4]
    rw [r2.get (by simpa using h16)]
    by_cases hr : r ∈ [Reg.x14, .x17, .x31]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [x14, hv.sv0]
      · rw [x17, hv.sv1]
      · rw [x31, hv.sv3]
    · have hr' : r ∉ sgRegs := by
        simp only [sgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
      rw [r1.get hr, hv.regs.get hr']
  · intro k hk
    rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by omega) (by omega) (by omega), hh.ans k hk]
  · rw [t2m _ (by decide) (by decide)]; exact m04
  · rw [t2m _ (by decide) (by decide)]; exact m12
  · rw [t2m _ (by decide) (by decide)]; exact m28
  · intro X hX hn
    by_cases hp : X = A + 32
    · subst hp
      rw [t2m _ hX (by omega), m32, hp32]
    · have h1 : ¬ GW A D X := by unfold GW; exact fun h => h.elim hp hn
      rw [t2m _ hX (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h))))),
        t1m _ hX hp (fun h => hn (Or.inr (Or.inl h))) (fun h => hn (Or.inr (Or.inr (Or.inl h))))
          (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h))))), hv.frame.get hX h1]

/-- One level-2 trial: pad `n` (`26005`, `ecall`), then the hash of the trial block into `D`. -/
theorem gtrial16 (hS16 : CodeAt im (pcOf SIGN16) sign16Words) {β : Type} {n : Nat} {u : MachineState}
    (hz40 : s.getMem (BitVec.ofNat 64 (A + 40)) = 0)
    (hu : AtH s tb A D 26005 n u) {W : Nat} {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (h : ∀ a w, AtH s tb A D 26007 n w → HashedS w A D n a → TBSim im sk w W (f a) Q) :
    TBSim im sk u (1 + (8 + W)) (publicHash (trialInput pre n right) >>= f) Q := by
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1; have hD2 := F.hD2
  have hAD := F.hAD
  have hnF : n < 2 ^ 64 := by have := hu.hn; omega
  have g10 : u.getReg .x10 = BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)]; exact F.x10
  obtain ⟨u1, s1, p1, r1, m32, f1, fe1⟩ := t16_spec hS16 u hu.pc A g10 hA hA2
  rw [hu.x17] at m32
  have fs1 : Frame s u1 (GW A D) := (hu.frame.trans f1).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inl h)
  have g1 : ∀ x, x ∉ sgRegs → u1.getReg x = s.getReg x := fun x hx => by
    rw [r1.get (by simp), hu.regs.get hx]
  have h12 : u1.getReg .x12 = BitVec.ofNat 64 D := by rw [g1 _ (by decide)]; exact F.x12
  have hl := trialInput_length pre right n F.lpre F.lright
  have notW : ∀ X, A ≤ X → X < A + 64 → X ≠ A + 32 → ¬ GW A D X := fun X h1 h2 h3 hw => by
    unfold GW SignW at hw; omega
  have m40 : u1.getMem (BitVec.ofNat 64 (A + 40)) = 0 := by
    rw [fs1.get (by omega) (notW _ (by omega) (by omega) (by omega))]; exact hz40
  have hq : hashInput u1 = toQ (pad64 (trialInput pre n right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u1 _ 0 A hl (by rw [g1 _ (by decide)]; exact F.x10) hA (by omega)
      (by rw [g1 _ (by decide)]; exact F.x11) (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_add, readWords_add,
      frame_readWordsG fs1 A 4 (by omega) (fun i hi => notW _ (by omega) (by omega) (by omega)),
      show A + 8 * 4 = A + 32 by ring, readWords_two, m32, m40, show A + 32 + 8 * 2 = A + 48 by ring,
      frame_readWordsG fs1 (A + 48) 2 (by omega) (fun i hi => notW _ (by omega) (by omega) (by omega)),
      F.mpre, F.mright, trialInput, wordsOf_append _ _ (by rw [List.length_append, F.lpre]; simp [nonceBytes,
        bytesLE_length]), wordsOf_append _ _ (by rw [F.lpre]), nonce_words n hnF]
  have hv : hashArgumentsValid u1 = true := hashArgs_const u1 A 64 D (by rw [g1 _ (by decide)]; exact F.x10)
    (by rw [g1 _ (by decide)]; exact F.x11) h12 hA (by norm_num) hA2 F.hD hD2
  have h5 : u1.getReg .x5 = 0 := by rw [g1 _ (by decide)]; exact F.x5
  have e := tb_pub (sk := sk) (W := W) (f := f) (Q := Q) fe1 h5 hv hq (fun a => ?_)
  · have := TBSim.steps s1 e
    rwa [trial_blocks pre right n F.lpre F.lright] at this
  have hwf := Frame.writeHash u1 a D h12 (by omega)
  have fw : Frame s (writeHash u1 a) (GW A D) := (fs1.trans hwf).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inl h))
  have keep : ∀ X, X < 2 ^ 64 → ¬ (D ≤ X ∧ X < D + 32) →
      (writeHash u1 a).getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) := fun X hX h => hwf.get hX h
  have keepu : ∀ X, X < 2 ^ 64 → X ≠ A + 32 →
      u1.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := fun X hX h1 => f1.get hX h1
  refine h a (writeHash u1 a) ⟨by rw [pc_writeHash, p1, pcOf_add4], fun x hx => by rw [getReg_writeHash, g1 x hx],
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x16, by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x17,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv0,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv1,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv3,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv4,
    fw, hu.hn⟩ ⟨fun k hk => ?_, by rw [keep _ (by omega) (by omega)]; exact m32⟩
  rw [getMem_writeHash u1 a D _ h12 (by omega) (by omega)]
  interval_cases k <;> simp

/-- The level-2 grind loop from the trial at 26005: `fuel` further trials (`n + fuel = 255`), the half-aware test,
each failing trial `1 + 8 + 6 + 4 = 19` cycles, the last `<= 29`. -/
theorem gloop16 (hS16 : CodeAt im (pcOf SIGN16) sign16Words) (hg : 16 ≤ heap ∧ heap < 32 ∧ signCoord tb ≤ 7)
    (hp32 : s.getMem (BitVec.ofNat 64 (A + 32)) = 0) (hz40 : s.getMem (BitVec.ofNat 64 (A + 40)) = 0) :
    ∀ fuel n u, AtH s tb A D 26005 n u → n + fuel = 255 →
    TBSim im sk u (19 * fuel + 29) (searchH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 pre right fuel n)
      (SignOutC s ret (signCoord tb) heap D (2 - signR tb)) := by
  have hD := F.hD; have hD2 := F.hD2
  have hhh : heap < 2 ^ 64 := F.hheap
  have test : ∀ n a w, AtH s tb A D 26007 n w → HashedS w A D n a → ∃ w1 c, Steps im w c c w1 ∧ c ≤ 6 ∧
      AtH s tb A D (if zeroOkH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 a = true then 26018 else 26014) n w1 ∧
      HashedS w1 A D n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := c16_spec hS16 w hw.pc heap
      (by rw [hw.regs.get (by decide)]; exact F.x18) hhh D (by rw [hw.regs.get (by decide)]; exact F.x12) hD
      (by omega)
    have e : (w.getMem (BitVec.ofNat 64 (D + if heap % 2 = 0 then 24 else 8))).toNat < 2 ^ 63 ↔
        zeroOkH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 a = true := by
      rw [zeroOkH_iff16 heap hg.1]
      by_cases he : heap % 2 = 0
      · rw [if_pos he, if_pos he]
        have := hh.ans 3 (by decide)
        rw [show D + 8 * 3 = D + 24 by ring, show 64 * 3 = 192 by norm_num] at this
        rw [this]
      · rw [if_neg he, if_neg he]
        have := hh.ans 1 (by decide)
        rw [show D + 8 * 1 = D + 8 by ring, show 64 * 1 = 64 by norm_num] at this
        rw [this]
    refine ⟨w1, _, s1, ?_, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move F f1⟩
    · split_ifs <;> omega
    · rw [p1]; by_cases hz : zeroOkH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 a = true
      · rw [if_pos (e.mpr hz), if_pos hz]
      · rw [if_neg (fun h => hz (e.mp h)), if_neg hz]
  -- from 26018: `jal` to the exit, then the exit
  have fin : ∀ n a w, AtH s tb A D 26018 n w → HashedS w A D n a →
      TBSim im sk w 12 (pure (n, a)) (SignOutC s ret (signCoord tb) heap D (2 - signR tb)) := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := x16_spec hS16 w hw.pc
    have hw1 : AtH s tb A D 25330 n w1 :=
      hw.move p1 (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn
    exact TBSim.steps s1 (gexit16 hS hT F hg hp32 hw1 (hh.move F f1))
  have nstep : ∀ n a w, AtH s tb A D 26014 n w → HashedS w A D n a → ∃ w1 c, Steps im w c c w1 ∧
      (n = 255 → c = 2 ∧ AtH s tb A D 26018 n w1) ∧
      (n ≠ 255 → c = 4 ∧ AtH s tb A D 26005 (n + 1) w1) ∧ HashedS w1 A D n a := by
    intro n a w hw hh
    obtain ⟨w1, c, s1, h255, hne, r1, f1⟩ := n16_spec hS16 w hw.pc
    have hnl : n < 2 ^ 64 := by have := hw.hn; omega
    have hiff : w.getReg .x17 = BitVec.ofNat 64 255 ↔ n = 255 := by
      rw [hw.x17]; exact ⟨fun h => (ofNat_inj hnl (by norm_num)).mp h, fun h => by rw [h]⟩
    refine ⟨w1, c, s1, fun h => ?_, fun h => ?_, hh.move F f1⟩
    · obtain ⟨hc, p, x17⟩ := h255 (hiff.mpr h)
      exact ⟨hc, hw.move p r1 f1 (by rw [x17, hw.x17]) hw.hn⟩
    · obtain ⟨hc, p, x17⟩ := hne (fun h' => h (hiff.mp h'))
      refine ⟨hc, hw.move p r1 f1 (by rw [x17, hw.x17, ofNat_add_ofNat]) ?_⟩
      have := hw.hn
      omega
  intro fuel
  induction fuel with
  | zero =>
    intro n u hu hn
    simp only [Nat.add_zero] at hn
    rw [searchH_eqg]
    refine (gtrial16 hS hT F hS16 hz40 hu (W := 20) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, c1, s1, hc1, hw1, hh1⟩ := test n a w hw hh
    simp only [sTailHg]
    by_cases hz : zeroOkH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 a = true
    · rw [if_pos hz] at hw1
      exact (TBSim.steps s1 (fin n a w1 hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      obtain ⟨w2, c2, s2, h255, -, hh2⟩ := nstep n a w1 hw1 hh1
      obtain ⟨hc2, hw2⟩ := h255 (by omega)
      exact (TBSim.steps s1 (TBSim.steps s2 (fin n a w2 hw2 hh2))).mono (by omega) (fun _ _ h => h)
  | succ fuel ih =>
    intro n u hu hn
    rw [searchH_eqg]
    refine (gtrial16 hS hT F hS16 hz40 hu (W := 19 * fuel + 39) (fun a w hw hh => ?_)).mono (by omega)
      (fun _ _ h => h)
    obtain ⟨w1, c1, s1, hc1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOkH (ClaudeWCT.WCT9.ftsHighHeap heap) 1 a = true
    · simp only [sTailHg, hz, if_true]
      rw [if_pos hz] at hw1
      exact (TBSim.steps s1 (fin n a w1 hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · simp only [sTailHg, hz, Bool.false_eq_true, if_false]
      rw [if_neg hz] at hw1
      obtain ⟨w2, c2, s2, -, h254, hh2⟩ := nstep n a w1 hw1 hh1
      obtain ⟨hc2, hw2⟩ := h254 (by omega)
      have := TBSim.steps s1 (TBSim.steps s2 (ih (n + 1) w2 hw2 (by omega)))
      exact this.mono (by omega) (fun _ _ h => h)

/-- **The sign trampoline round trip refines `signNodeC`** (S5185 FTS16, TIER2 S11; was `signNode`, which modelled
heaps 16..31 as a plain hash with nonce 0): ground on heaps 8..15 (width `2 - signR tb`) and on heaps 16..31 of
coordinates 0..7 (the 25998 loop, `groundFoldH (ftsHighHeap heap) 1`); plain otherwise. The pad hypothesis `hg16`
covers the new ground nodes (the loop overwrites `a0+32` and clears it on exit; `a0+40` must be 0). -/
theorem sign_tramp_node (hS16 : CodeAt im (pcOf SIGN16) sign16Words)
    (hg16 : 16 ≤ heap ∧ heap < 32 ∧ signCoord tb ≤ 7 →
      s.getMem (BitVec.ofNat 64 (A + 32)) = 0 ∧ s.getMem (BitVec.ofNat 64 (A + 40)) = 0)
    (htb : ∃ c, c < 9 ∧ tb = SIGN_TRAMP + 5 * c) :
    TBSim im sk s (signWC (signCoord tb) (2 - signR tb) heap)
      (signNodeC (signCoord tb) (2 - signR tb) heap pre mid right)
      (SignOutC s ret (signCoord tb) heap D (2 - signR tb)) := by
  obtain ⟨c, hc9, htbc⟩ := htb
  have hcoord : signCoord tb = c := by unfold signCoord; omega
  have hc7 : signCoord tb ≤ 7 ↔ tb < SIGN_TRAMP + 40 := by omega
  have hbl := F.hb
  have hF1 : FUEL 1 = 255 := rfl
  obtain ⟨u0, s0, p0, x16, r0, m0, f0⟩ := tramp_head hT F.hb (by decide) s F.pc
  have g0 : ∀ x, x ≠ .x16 → u0.getReg x = s.getReg x := fun x h => r0.get (by simp [h])
  obtain ⟨u1, s1, p1, r1, sv0, sv1, f1⟩ := e_spec hS u0 p0 heap (by rw [g0 _ (by decide)]; exact F.x18) F.hheap
  have f01 : Frame s u1 (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136) := (f0.trans f1).mono (fun X _ h => by
    rcases h with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have r01 : RegsExcept s u1 [.x16, .x17] := (r0.trans r1).mono (by decide)
  have x16' : u1.getReg .x16 = pcOf (tb + 2) := by rw [r1.get (by decide)]; exact x16
  have sv0' : u1.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 := by rw [sv0, g0 _ (by decide)]
  have sv1' : u1.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 := by rw [sv1, g0 _ (by decide)]
  have sv4' : u1.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by
    rw [f1.get (by decide) (by omega)]; exact m0
  by_cases h8 : heap < 8
  · rw [if_pos h8] at p1
    have hng : ¬ (8 ≤ heap ∧ heap < 16) := by omega
    have hnC : ¬ (16 ≤ heap ∧ heap < 32 ∧ signCoord tb ≤ 7) := by omega
    unfold signNodeC signWC; simp only [if_neg hng, if_neg hnC]
    exact (TBSim.steps s0 (TBSim.steps s1 (plain_run hS hT F hng p1 r01 x16' sv0' sv1' sv4' f01))).mono
      (by omega) (fun _ _ h => SignOut.toC h hnC)
  rw [if_neg h8] at p1
  have h18 : u1.getReg .x18 = BitVec.ofNat 64 heap := by rw [r01.get (by decide)]; exact F.x18
  obtain ⟨u2, s2, p2, r2, f2⟩ := e2_spec hS u1 p1 heap h18 F.hheap
  have r02 : RegsExcept s u2 [.x16, .x17] := (r01.trans r2).mono (by decide)
  have fm : ∀ X, X < 2 ^ 64 → u2.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => f2.get hX (fun h => h)
  have x16'' : u2.getReg .x16 = pcOf (tb + 2) := by rw [r2.get (by decide)]; exact x16'
  have f012 : Frame s u2 (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136) :=
    (f01.trans f2).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  by_cases h16 : 16 ≤ heap
  · rw [if_pos h16] at p2
    have h18' : u2.getReg .x18 = BitVec.ofNat 64 heap := by rw [r02.get (by decide)]; exact F.x18
    obtain ⟨u3, n3, s3, hA32, hB, hC, r3, f3, fp⟩ :=
      g16_core hS16 u2 p2 heap h18' F.hheap tb x16'' (by omega)
    by_cases hgr : heap < 32 ∧ tb < SIGN_TRAMP + 40
    · -- the level-2 ground grind
      have hgC : 16 ≤ heap ∧ heap < 32 ∧ signCoord tb ≤ 7 := ⟨h16, hgr.1, hc7.mpr hgr.2⟩
      have hng : ¬ (8 ≤ heap ∧ heap < 16) := by omega
      obtain ⟨hn3, p3, x17, m28⟩ := hC hgr.1 hgr.2
      obtain ⟨hp32, hz40⟩ := hg16 hgC
      have fm3 : ∀ X, X < 2 ^ 64 → X ≠ 1128 → u3.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
        fun X hX h => (f3.get hX h).trans (fm X hX)
      have hu3 : AtH s tb A D 26005 0 u3 :=
        { pc := p3
          regs := (r02.trans r3).mono (by decide)
          x16 := by rw [r3.get (by decide)]; exact x16''
          x17 := x17
          sv0 := by rw [fm3 _ (by decide) (by decide)]; exact sv0'
          sv1 := by rw [fm3 _ (by decide) (by decide)]; exact sv1'
          sv3 := by rw [m28, r02.get (by decide)]
          sv4 := by rw [fm3 _ (by decide) (by decide)]; exact sv4'
          frame := ((f012).trans f3).mono (fun X _ h => by
            unfold GW SignW
            rcases h with (h | h | h) | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
          hn := Nat.zero_le _ }
      have hfin := gloop16 (sk := sk) hS hT F hS16 hgC hp32 hz40 255 0 u3 hu3 (by omega)
      unfold signNodeC signWC groundFoldH
      simp only [if_neg hng, if_pos hgC, hF1]
      exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 hfin)))).mono (by omega)
        (fun _ _ h => h)
    · -- plain: heap >= 32, or coordinate 8
      have hng : ¬ (8 ≤ heap ∧ heap < 16) := by omega
      have hnC : ¬ (16 ≤ heap ∧ heap < 32 ∧ signCoord tb ≤ 7) := by
        intro h; exact hgr ⟨h.2.1, hc7.mp h.2.2⟩
      have hpl : n3 ≤ 5 ∧ u3.pc = pcOf 25338 := by
        by_cases h32 : 32 ≤ heap
        · obtain ⟨a, b⟩ := hA32 h32; exact ⟨by omega, b⟩
        · obtain ⟨a, b⟩ := hB (by omega) (by omega); exact ⟨by omega, b⟩
      have fz := fp (by omega)
      have fu3 : Frame s u3 (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136) :=
        (f012.trans fz).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
      have fm3 : ∀ X, X < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 X) = u2.getMem (BitVec.ofNat 64 X) :=
        fun X hX => fz.get hX (fun h => h)
      unfold signNodeC signWC; simp only [if_neg hng, if_neg hnC]
      exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3
        (plain_run hS hT F hng hpl.2 ((r02.trans r3).mono (by decide))
          (by rw [r3.get (by decide)]; exact x16'') (by rw [fm3 _ (by decide), fm _ (by decide)]; exact sv0')
          (by rw [fm3 _ (by decide), fm _ (by decide)]; exact sv1')
          (by rw [fm3 _ (by decide), fm _ (by decide)]; exact sv4') fu3))))).mono
        (by omega) (fun _ _ h => SignOut.toC h hnC)
  rw [if_neg h16] at p2
  have hg : 8 ≤ heap ∧ heap < 16 := by omega
  have hnC : ¬ (16 ≤ heap ∧ heap < 32 ∧ signCoord tb ≤ 7) := by omega
  obtain ⟨u3, s3, p3, x31, x17, r3, m28, f3⟩ := g_spec hS u2 p2 tb x16'' (by omega)
  have fm3 : ∀ X, X < 2 ^ 64 → X ≠ 1128 → u3.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => (f3.get hX h).trans (fm X hX)
  have hu3 : AtG s tb A D 25319 0 u3 :=
    { pc := p3
      regs := (r02.trans r3).mono (by decide)
      x16 := by rw [r3.get (by decide)]; exact x16''
      x17 := x17
      x31 := x31
      sv0 := by rw [fm3 _ (by decide) (by decide)]; exact sv0'
      sv1 := by rw [fm3 _ (by decide) (by decide)]; exact sv1'
      sv3 := by rw [m28, r02.get (by decide)]
      sv4 := by rw [fm3 _ (by decide) (by decide)]; exact sv4'
      frame := (f012.trans f3).mono (fun X _ h => by
        unfold GW SignW
        rcases h with (h | h | h) | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      hn := Nat.zero_le _ }
  unfold signNodeC signWC groundFold; simp only [if_pos hg]
  exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3
    (gloop hS hT F hg (FUEL (2 - signR tb)) 0 u3 hu3 (by omega)))))).mono (by omega)
    (fun _ _ h => SignOut.toC h hnC)

end run

end SigGolfCandidate.FtsGrind

