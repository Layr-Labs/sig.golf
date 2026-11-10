import SigGolfCandidate.SimCore
import SigGolfCandidate.Merge048
import SigGolfCandidate.Merge046
import SigGolfCandidate.FtsExpandSearch
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

/-- The width selector: `r = 1` iff the stub was entered from trampoline 0 or 1 (`a6 < pcOf (SIGN_TRAMP + 8)`). -/
def signR (tb : Nat) : Nat := if tb + 2 < SIGN_TRAMP + 8 then 1 else 0

theorem signR_width (k : Nat) (hk : k < 9) : 2 - signR (SIGN_TRAMP + 5 * k) = ftsWidth k := by
  interval_cases k <;> decide

/-- The sign FTS tree node at heap `heap` with block `pre ‖ mid ‖ right`: a ground heap-8..15 node is ground for
`b` zero bits (the pad `mid` is zero there); every other node is the plain hash. -/
def signNode (b heap : Nat) (pre mid right : List UInt8) : M (Nat × HashOutput) :=
  if 8 ≤ heap ∧ heap < 16 then groundFold b pre right else (fun a => (0, a)) <$> publicHash (pre ++ mid ++ right)

/-- Cycles of one sign trampoline round trip. -/
def signW (b heap : Nat) : Nat := if 8 ≤ heap ∧ heap < 16 then 18 * FUEL b + 40 else 25

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
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if 16 ≤ heap then pcOf 25338 else pcOf 25314) ∧ RegsExcept s t [.x17] ∧
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
    rw [show (105488#64 : Word) = BitVec.ofNat 64 105488 from rfl, ult_ofNat' _ _ (by omega) (by decide)]
    unfold signR SIGN_TRAMP
    by_cases h : tb + 2 < 25340 + 8
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
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

/-- **The sign trampoline round trip refines `signNode`** at width `2 - signR tb`. -/
theorem sign_tramp_node :
    TBSim im sk s (signW (2 - signR tb) heap) (signNode (2 - signR tb) heap pre mid right)
      (SignOut s ret heap D (2 - signR tb)) := by
  have hA1 := F.hA1
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
    unfold signNode signW; rw [if_neg hng, if_neg hng]
    exact (TBSim.steps s0 (TBSim.steps s1 (plain_run hS hT F hng p1 r01 x16' sv0' sv1' sv4' f01))).mono
      (by omega) (fun _ _ h => h)
  rw [if_neg h8] at p1
  have h18 : u1.getReg .x18 = BitVec.ofNat 64 heap := by rw [r01.get (by decide)]; exact F.x18
  obtain ⟨u2, s2, p2, r2, f2⟩ := e2_spec hS u1 p1 heap h18 F.hheap
  have r02 : RegsExcept s u2 [.x16, .x17] := (r01.trans r2).mono (by decide)
  have fm : ∀ X, X < 2 ^ 64 → u2.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => f2.get hX (fun h => h)
  by_cases h16 : 16 ≤ heap
  · rw [if_pos h16] at p2
    have hng : ¬ (8 ≤ heap ∧ heap < 16) := by omega
    unfold signNode signW; rw [if_neg hng, if_neg hng]
    refine (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (plain_run hS hT F hng p2 r02
      (by rw [r2.get (by decide)]; exact x16') (by rw [fm _ (by decide)]; exact sv0')
      (by rw [fm _ (by decide)]; exact sv1') (by rw [fm _ (by decide)]; exact sv4')
      ((f01.trans f2).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)))))).mono
      (by omega) (fun _ _ h => h)
  rw [if_neg h16] at p2
  have hg : 8 ≤ heap ∧ heap < 16 := by omega
  obtain ⟨u3, s3, p3, x31, x17, r3, m28, f3⟩ := g_spec hS u2 p2 tb (by rw [r2.get (by decide)]; exact x16')
    (by have := F.hb; omega)
  have fm3 : ∀ X, X < 2 ^ 64 → X ≠ 1128 → u3.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => (f3.get hX h).trans (fm X hX)
  have hu3 : AtG s tb A D 25319 0 u3 :=
    { pc := p3
      regs := (r02.trans r3).mono (by decide)
      x16 := by rw [r3.get (by decide), r2.get (by decide)]; exact x16'
      x17 := x17
      x31 := x31
      sv0 := by rw [fm3 _ (by decide) (by decide)]; exact sv0'
      sv1 := by rw [fm3 _ (by decide) (by decide)]; exact sv1'
      sv3 := by rw [m28, r02.get (by decide)]
      sv4 := by rw [fm3 _ (by decide) (by decide)]; exact sv4'
      frame := ((f01.trans f2).trans f3).mono (fun X _ h => by
        unfold GW SignW
        rcases h with (h | h) | h
        · rcases h with h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
        · exact h.elim
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      hn := Nat.zero_le _ }
  unfold signNode signW groundFold; rw [if_pos hg, if_pos hg]
  exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3
    (gloop hS hT F hg (FUEL (2 - signR tb)) 0 u3 hu3 (by omega)))))).mono (by omega) (fun _ _ h => h)

end run

end SigGolfCandidate.FtsGrind

