import SigGolfCandidate.SimCore
import SigGolfCandidate.Merge048
import SigGolfCandidate.Merge046
import SigGolfCandidate.FtsCode
set_option debug.skipKernelTC true
set_option linter.all false

/-! # FTS carrier grind: shared helpers for the trampolines and stubs

Single steps of the five-word trampoline `sd a6,1136(zero); jal a6,target; ld a6,1136(zero);
sd zero,1136(zero); jal zero,ret`, the `jal` encoding `encJal`, sub-windows of checked code, and the hash
query rule for `publicHash`. -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash nonceBytes pad64)
open SphincsSecurity (bytesLE bytesLE_length)

/-- A sub-window of a checked code window. -/
theorem codeAt_sub {image : Image} {b : Nat} {code seg : List (BitVec 32)} (o : Nat)
    (hc : CodeAt image (pcOf b) code) (hlen : o + seg.length ≤ code.length)
    (h : (code.drop o).take seg.length = seg) :
    CodeAt image (pcOf (b + o)) seg := by
  have hsplit : code = code.take o ++ seg ++ (code.drop o).drop seg.length := by
    conv_lhs => rw [← List.take_append_drop o code, ← List.take_append_drop seg.length (code.drop o), h]
    simp only [List.append_assoc]
  rw [hsplit] at hc
  have := CodeAt.drop_prefix hc
  have hl : (code.take o).length = o := by rw [List.length_take]; omega
  rw [hl, ofNat_add_ofNat] at this
  rwa [pcOf, show 0x1000 + 4 * (b + o) = 0x1000 + 4 * b + 4 * o by ring]

theorem nonce_words (n : Nat) (hn : n < 2 ^ 64) : wordsOf (nonceBytes n) = [BitVec.ofNat 64 n, 0] := by
  unfold nonceBytes
  rw [wordsOf_bytesLE16]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    have h0 : n % 2 ^ 64 % 2 ^ 128 / 2 ^ 64 = 0 := by omega
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0, Nat.zero_mod]
    rfl

theorem micro_step {im : Image} {pc : Word} {w : BitVec 32} {i : Instruction} {m : Micro}
    (hc : CodeAt im pc [w]) (hd : decodeInstruction w = some i) (hcl : classify i = some m)
    {s t : MachineState} (hpc : s.pc = pc) (he : m.exec s = some t) :
    Steps im s 1 (instructionCycles i) t := by
  have hf : fetch im s = some i := (hc.fetch s hpc).trans hd
  have := Steps.step (image := im) hf ((classify_sound hcl s).trans he) (Steps.refl t)
  simpa using this

theorem tb_pure_steps {α : Type} {image : Image} {sk : BitVec 256} {s t : MachineState} {k c : Nat} {a : α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ

theorem tb_pub {im : Image} {sk : BitVec 256} {β : Type} {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h

/-! ## `jal` -/

theorem split_div_mod (N hi f lo k m : Nat) (hN : N = lo + 2 ^ k * (f + 2 ^ m * hi)) (hlo : lo < 2 ^ k)
    (hf : f < 2 ^ m) : N / 2 ^ k % 2 ^ m = f := by
  subst hN
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hf]
theorem jal_fields (N x y z w rd : Nat) (hx : x < 2 ^ 10) (hy : y < 2 ^ 1) (hz : z < 2 ^ 8) (hw : w < 2 ^ 1)
    (hrd : rd < 2 ^ 5) (hN : N = w * 2 ^ 31 + x * 2 ^ 21 + y * 2 ^ 20 + z * 2 ^ 12 + rd * 2 ^ 7 + 111) :
    N / 2 ^ 0 % 2 ^ 7 = 111 ∧ N / 2 ^ 7 % 2 ^ 5 = rd ∧ N / 2 ^ 31 % 2 ^ 1 = w ∧ N / 2 ^ 21 % 2 ^ 10 = x ∧
    N / 2 ^ 20 % 2 ^ 1 = y ∧ N / 2 ^ 12 % 2 ^ 8 = z :=
  ⟨split_div_mod _ (w * 2 ^ 24 + x * 2 ^ 14 + y * 2 ^ 13 + z * 2 ^ 5 + rd) 111 0 0 7 (by rw [hN]; ring) (by norm_num) (by norm_num),
   split_div_mod _ (w * 2 ^ 19 + x * 2 ^ 9 + y * 2 ^ 8 + z) rd 111 7 5 (by rw [hN]; ring) (by norm_num) hrd,
   split_div_mod _ 0 w (x * 2 ^ 21 + y * 2 ^ 20 + z * 2 ^ 12 + rd * 2 ^ 7 + 111) 31 1 (by rw [hN]; ring) (by omega) hw,
   split_div_mod _ w x (y * 2 ^ 20 + z * 2 ^ 12 + rd * 2 ^ 7 + 111) 21 10 (by rw [hN]; ring) (by omega) hx,
   split_div_mod _ (w * 2 ^ 10 + x) y (z * 2 ^ 12 + rd * 2 ^ 7 + 111) 20 1 (by rw [hN]; ring) (by omega) hy,
   split_div_mod _ (w * 2 ^ 11 + x * 2 + y) z (rd * 2 ^ 7 + 111) 12 8 (by rw [hN]; ring) (by omega) hz⟩
theorem off_fields (o x y z w : Nat) (hx : x < 2 ^ 10) (hy : y < 2 ^ 1) (hz : z < 2 ^ 8) (hw : w < 2 ^ 1)
    (ho : o = 2 * x + 2 ^ 11 * y + 2 ^ 12 * z + 2 ^ 20 * w) :
    o / 2 ^ 20 % 2 = w ∧ o / 2 % 1024 = x ∧ o / 2 ^ 11 % 2 = y ∧ o / 2 ^ 12 % 256 = z :=
  ⟨split_div_mod o 0 w (2 * x + 2 ^ 11 * y + 2 ^ 12 * z) 20 1 (by rw [ho]; ring) (by omega) hw,
   split_div_mod o (w * 2 ^ 9 + z * 2 ^ 1 + y) x 0 1 10 (by rw [ho]; ring) (by omega) hx,
   split_div_mod o (w * 2 ^ 8 + z) y (2 * x) 11 1 (by rw [ho]; ring) (by omega) hy,
   split_div_mod o w z (2 * x + 2 ^ 11 * y) 12 8 (by rw [ho]; ring) (by omega) hz⟩
theorem toNat_append' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
theorem decode_jal (w : BitVec 32) (h : (w.extractLsb' 0 7).toNat = 111) :
    decodeInstruction w = some (.base (.JAL (RiscvZkvm.Interpreter.regOfBits (w.extractLsb' 7 5))
      (RiscvZkvm.Interpreter.immJ w))) := by
  unfold decodeInstruction RiscvZkvm.Interpreter.decode
  simp only [h]
  rfl
theorem encJal_decode (rd o : Nat) (hrd : rd < 32) (ho : o < 2 ^ 21) (he : o % 2 = 0) :
    decodeInstruction (encJal rd o) =
      some (.base (.JAL (RiscvZkvm.Interpreter.regOfBits (BitVec.ofNat 5 rd)) (BitVec.ofNat 21 o))) := by
  obtain ⟨x, y, z, w, hx, hy, hz, hw, hox⟩ : ∃ x y z w, x < 2 ^ 10 ∧ y < 2 ^ 1 ∧ z < 2 ^ 8 ∧ w < 2 ^ 1 ∧
      o = 2 * x + 2 ^ 11 * y + 2 ^ 12 * z + 2 ^ 20 * w :=
    ⟨o / 2 % 1024, o / 2048 % 2, o / 4096 % 256, o / 1048576, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨f1, f2, f3, f4⟩ := off_fields o x y z w hx hy hz hw hox
  obtain ⟨g0, g7, g31, g21, g20, g12⟩ := jal_fields _ x y z w rd hx hy hz hw hrd rfl
  have ht : (encJal rd o).toNat = w * 2 ^ 31 + x * 2 ^ 21 + y * 2 ^ 20 + z * 2 ^ 12 + rd * 2 ^ 7 + 111 := by
    unfold encJal
    rw [f1, f2, f3, f4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx' : ∀ s n, ((encJal rd o).extractLsb' s n).toNat =
      (w * 2 ^ 31 + x * 2 ^ 21 + y * 2 ^ 20 + z * 2 ^ 12 + rd * 2 ^ 7 + 111) / 2 ^ s % 2 ^ n := fun s n => by
    rw [BitVec.extractLsb'_toNat, ht, Nat.shiftRight_eq_div_pow]
  have hop : ((encJal rd o).extractLsb' 0 7).toNat = 111 := by rw [hx', g0]
  have hrd' : (encJal rd o).extractLsb' 7 5 = BitVec.ofNat 5 rd := by
    apply BitVec.eq_of_toNat_eq; rw [hx', g7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrd]
  have himm : RiscvZkvm.Interpreter.immJ (encJal rd o) = BitVec.ofNat 21 o := by
    apply BitVec.eq_of_toNat_eq
    simp only [RiscvZkvm.Interpreter.immJ, toNat_append', hx', g31, g21, g20, g12, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt ho, hox]
    ring
  rw [decode_jal _ hop, hrd', himm]

theorem jal_target (a t : Nat) (ha : a < 2 ^ 18) (ht : t < 2 ^ 18) :
    pcOf a + signExtend21 (BitVec.ofNat 21 (jOff a t)) = pcOf t := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, signExtend21, BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  simp only [pcOf, BitVec.toNat_ofNat, jOff, Nat.reducePow, Nat.reduceSub, decide_eq_true_eq]
  split_ifs <;> omega

/-- `jal rd` from word `a` to word `t`. -/
theorem jal_step {im : Image} {a t rd : Nat} {r : Reg} (hrd : rd < 32)
    (hr : RiscvZkvm.Interpreter.regOfBits (BitVec.ofNat 5 rd) = r)
    (hc : CodeAt im (pcOf a) [encJal rd (jOff a t)]) (ha : a < 2 ^ 18) (ht : t < 2 ^ 18)
    (s : MachineState) (hpc : s.pc = pcOf a) :
    Steps im s 1 1 ((s.setReg r (pcOf (a + 1))).setPC (pcOf t)) := by
  have hdec := encJal_decode rd (jOff a t) hrd (by unfold jOff; omega) (by unfold jOff; omega)
  rw [hr] at hdec
  exact micro_step (m := .jal r (signExtend21 (BitVec.ofNat 21 (jOff a t)))) hc hdec rfl hpc
    (by simp only [Micro.exec, hpc, pcOf_add4, jal_target a t ha ht])

/-! ## The `a6` save slot 1136 -/

theorem sdA6_step {im : Image} {n : Nat} (hc : CodeAt im (pcOf n) [0x47003823]) (s : MachineState)
    (hpc : s.pc = pcOf n) :
    Steps im s 1 1 ((s.setMem (BitVec.ofNat 64 1136) (s.getReg .x16)).setPC (pcOf (n + 1))) := by
  have e : s.getReg .x0 + signExtend12 (1136 : BitVec 12) = BitVec.ofNat 64 1136 := by
    show (0#64 : Word) + signExtend12 1136 = _; decide
  exact micro_step (i := .base (.SD .x0 .x16 1136)) (m := .store .d .x0 .x16 (signExtend12 1136)) hc rfl rfl hpc
    (by simp only [Micro.exec, e, StoreKind.width, show accessValid (BitVec.ofNat 64 1136) 8 = true by decide,
      if_true, StoreKind.write, hpc, pcOf_add4])

theorem ldA6_step {im : Image} {n : Nat} (hc : CodeAt im (pcOf n) [0x47003803]) (s : MachineState)
    (hpc : s.pc = pcOf n) :
    Steps im s 1 1 ((s.setReg .x16 (s.getMem (BitVec.ofNat 64 1136))).setPC (pcOf (n + 1))) := by
  have e : s.getReg .x0 + signExtend12 (1136 : BitVec 12) = BitVec.ofNat 64 1136 := by
    show (0#64 : Word) + signExtend12 1136 = _; decide
  exact micro_step (i := .base (.LD .x16 .x0 1136)) (m := .load .d .x16 .x0 (signExtend12 1136)) hc rfl rfl hpc
    (by simp only [Micro.exec, e, LoadKind.width, show accessValid (BitVec.ofNat 64 1136) 8 = true by decide,
      if_true, LoadKind.read, hpc, pcOf_add4])

theorem sdZ_step {im : Image} {n : Nat} (hc : CodeAt im (pcOf n) [0x46003823]) (s : MachineState)
    (hpc : s.pc = pcOf n) :
    Steps im s 1 1 ((s.setMem (BitVec.ofNat 64 1136) 0).setPC (pcOf (n + 1))) := by
  have e : s.getReg .x0 + signExtend12 (1136 : BitVec 12) = BitVec.ofNat 64 1136 := by
    show (0#64 : Word) + signExtend12 1136 = _; decide
  exact micro_step (i := .base (.SD .x0 .x0 1136)) (m := .store .d .x0 .x0 (signExtend12 1136)) hc rfl rfl hpc
    (by simp only [Micro.exec, e, StoreKind.width, show accessValid (BitVec.ofNat 64 1136) 8 = true by decide,
      if_true, StoreKind.write, hpc, pcOf_add4]; rfl)

/-- The trampoline at `b` split into its five words. -/
theorem tramp_code {im : Image} {b target ret : Nat} (h : CodeAt im (pcOf b) (trampWords b target ret)) :
    CodeAt im (pcOf b) [0x47003823] ∧ CodeAt im (pcOf (b + 1)) [encJal 16 (jOff (b + 1) target)] ∧
      CodeAt im (pcOf (b + 2)) [0x47003803] ∧ CodeAt im (pcOf (b + 3)) [0x46003823] ∧
      CodeAt im (pcOf (b + 4)) [encJal 0 (jOff (b + 4) ret)] :=
  ⟨by simpa using codeAt_sub 0 h (by simp [trampWords]) rfl, codeAt_sub 1 h (by simp [trampWords]) rfl,
    codeAt_sub 2 h (by simp [trampWords]) rfl, codeAt_sub 3 h (by simp [trampWords]) rfl,
    codeAt_sub 4 h (by simp [trampWords]) rfl⟩

theorem getReg_setReg_ne (s : MachineState) (r r' : Reg) (v : Word) (h : r' ≠ r) :
    (s.setReg r v).getReg r' = s.getReg r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl

theorem getReg_setReg_eq (s : MachineState) (r : Reg) (v : Word) (h : r ≠ .x0) :
    (s.setReg r v).getReg r = v := by
  cases r <;> first | exact absurd rfl h | simp [MachineState.setReg, MachineState.getReg]

/-- Trampoline head (words `b`, `b + 1`): save `a6` at 1136, `jal a6, target`. -/
theorem tramp_head {im : Image} {b target ret : Nat} (h : CodeAt im (pcOf b) (trampWords b target ret))
    (hb : b + 5 < 2 ^ 18) (ht : target < 2 ^ 18) (s : MachineState) (hpc : s.pc = pcOf b) :
    ∃ u, Steps im s 2 2 u ∧ u.pc = pcOf target ∧ u.getReg .x16 = pcOf (b + 2) ∧ RegsExcept s u [.x16] ∧
      u.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 ∧ Frame s u (fun X => X = 1136) := by
  obtain ⟨c0, c1, -, -, -⟩ := tramp_code h
  have s1 := sdA6_step c0 s hpc
  have s2 := jal_step (r := .x16) (by decide) rfl c1 (by omega) ht ((s.setMem (BitVec.ofNat 64 1136) (s.getReg .x16)).setPC (pcOf (b + 1))) rfl
  refine ⟨_, s1.trans s2, rfl, by rw [MachineState.getReg_setPC]; exact getReg_setReg_eq _ _ _ (by decide),
    fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr
    rw [MachineState.getReg_setPC, getReg_setReg_ne _ _ _ _ hr, MachineState.getReg_setPC, getReg_setMem']
  · simp
  · intro A hA hn
    simp only [MachineState.getMem_setPC, MachineState.getMem_setReg]
    rw [getMem_setMem_ofNat _ _ _ _ (by decide) hA, if_neg hn]

/-- Trampoline tail (words `b + 2 .. b + 4`): restore `a6` from 1136, clear 1136, `jal zero, ret`. -/
theorem tramp_tail {im : Image} {b target ret : Nat} (h : CodeAt im (pcOf b) (trampWords b target ret))
    (hb : b + 5 < 2 ^ 18) (hr : ret < 2 ^ 18) (t : MachineState) (hpc : t.pc = pcOf (b + 2)) :
    ∃ u, Steps im t 3 3 u ∧ u.pc = pcOf ret ∧ u.getReg .x16 = t.getMem (BitVec.ofNat 64 1136) ∧
      RegsExcept t u [.x16] ∧ u.getMem (BitVec.ofNat 64 1136) = 0 ∧ Frame t u (fun X => X = 1136) := by
  obtain ⟨-, -, c2, c3, c4⟩ := tramp_code h
  have s2 := ldA6_step c2 t hpc
  have s3 := sdZ_step c3 ((t.setReg .x16 (t.getMem (BitVec.ofNat 64 1136))).setPC (pcOf (b + 2 + 1))) rfl
  have s4 := jal_step (r := .x0) (by decide) rfl c4 (by omega) hr
    (((t.setReg .x16 (t.getMem (BitVec.ofNat 64 1136))).setPC (pcOf (b + 2 + 1))).setMem (BitVec.ofNat 64 1136) 0 |>.setPC (pcOf (b + 3 + 1))) rfl
  refine ⟨_, s2.trans (s3.trans s4), rfl, ?_, fun r hr => ?_, ?_, ?_⟩
  · simp only [MachineState.getReg_setPC]
    rw [show ∀ (u : MachineState) (v : Word), u.setReg .x0 v = u from fun _ _ => rfl]
    simp only [MachineState.getReg_setPC, getReg_setMem']
    exact getReg_setReg_eq _ _ _ (by decide)
  · simp only [List.mem_singleton] at hr
    rw [show ∀ (u : MachineState) (v : Word), u.setReg .x0 v = u from fun _ _ => rfl]
    simp only [MachineState.getReg_setPC, getReg_setMem']
    exact getReg_setReg_ne _ _ _ _ hr
  · simp [MachineState.setReg]
  · intro A hA hn
    rw [show ∀ (u : MachineState) (v : Word), u.setReg .x0 v = u from fun _ _ => rfl]
    rw [MachineState.getMem_setPC, MachineState.getMem_setPC, getMem_setMem_ofNat _ _ _ _ (by decide) hA, if_neg hn]
    simp only [MachineState.getMem_setPC, MachineState.getMem_setReg]

end SigGolfCandidate.FtsGrind
