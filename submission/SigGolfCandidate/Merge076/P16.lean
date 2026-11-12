import SigGolfCandidate.ExpandLabel
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076.P1
import SigGolfCandidate.Merge076.P4
import SigGolfCandidate.Merge076.P5
import SigGolfCandidate.Merge076.P6
import SigGolfCandidate.Merge076.P7
import SigGolfCandidate.Merge076.P9
import SigGolfCandidate.Merge076.P13

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
section blocks
variable (s : MachineState)
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image} [Code im]
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
variable {im : Image} [Code im]
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Grind
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest nonceBytes pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (lowerZeroBits lowerNonceCap lowerZeroOk lowerNodeInputN lowerNodeHashN lowerNonceSearch
  lowerNodeAt)
section blocks
variable {im : Image} [Code im] (s : MachineState)

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

section cls
variable {im : Image} [Code im]

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image} [Code im]

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

section sim
variable {im : Image} {sk : BitVec 256}
end sim

section found
variable {im : Image} [Code im]

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

section loop
variable {im : Image} [Code im] (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image} [Code im] {sk : BitVec 256}

end pass

end Grind


end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
section tb
variable {image : Image} {sk : BitVec 256}
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
section chain
variable {sk : BitVec 256}
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im]                    [PackedBlocks.Code im] {sk : BitVec 256}
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [EntryCode im]
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
end blocks
section sort
variable {image : Image} {b : Nat}
end sort
theorem NAt.frame {s t : MachineState} {N : BitVec 256} (h : NAt s N) (hf : Frame s t SelW) : NAt t N := by
  intro j hj
  rw [hf.get (by simp only [NBUF]; omega) (by simp only [SelW, SEL, NBUF]; omega)]
  exact h j hj
section loop
variable {image : Image} {b : Nat}
structure SelInv (b : Nat) (s0 : MachineState) (N : BitVec 256) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 7)
  x20 : t.getReg .x20 = BitVec.ofNat 64 c
  x21 : t.getReg .x21 = BitVec.ofNat 64 (21 + selCost N c)
  x25 : t.getReg .x25 = BitVec.ofNat 64 (SEL + 24 * c)
  ok : ∀ c' < c, rowOk (selRow N c') = true
  rows : ∀ c' < c, RowAt t N c'
  regs : RegsExcept s0 t selRegs
  frame : Frame s0 t SelW
theorem sel_body (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) {c : Nat}
    (hc : c < 7) {t : MachineState} (hI : SelInv b s0 N c t) :
    ∃ k u, Steps image t k k u ∧ k ≤ 90 ∧
      (if rowOk (selRow N c) then SelInv b s0 N (c + 1) u
       else u.pc = pcOf (b + 101) ∧ RegsExcept s0 u selRegs ∧ Frame s0 u SelW) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := so7_spec hK t hI.pc c (by omega) hI.x20
  rw [if_pos hc] at p1
  have hN1 : NAt t1 N := (hN.frame hI.frame).frame (f1.mono (by simp))
  obtain ⟨t2, s2, p2, h28, r2, f2⟩ := so9_spec hK t1 p1 c hc (by rw [r1.get (by decide), hI.x20]) N hN1
  obtain ⟨k3, t3, s3, k3le, p3, h6, h22, h23, h24, r3, f3⟩ := sort_spec hK t2 p2 _ (selWin_lt N c) h28
  have hrow : ∀ j, (selRow N c).getD j 0 < 128 := selRow_lt N c
  have g22 : t3.getReg .x22 = BitVec.ofNat 64 ((selRow N c).getD 0 0) := h22
  have g23 : t3.getReg .x23 = BitVec.ofNat 64 ((selRow N c).getD 1 0) := h23
  have g24 : t3.getReg .x24 = BitVec.ofNat 64 ((selRow N c).getD 2 0) := h24
  obtain ⟨t4, s4, p4, r4, f4⟩ := so51_spec hK t3 p3 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) (by have := hrow 0; omega)
    (by have := hrow 1; omega) g22 g23
  have regs4 : RegsExcept s0 t4 selRegs :=
    regs_mono ((((hI.regs.trans r1).trans r2).trans r3).trans r4) (by decide)
  have frame4 : Frame s0 t4 SelW := ((((hI.frame.trans f1).trans f2).trans f3).trans f4).mono
    (by sel_frame)
  by_cases e1 : (selRow N c).getD 0 0 = (selRow N c).getD 1 0
  · rw [if_pos e1] at p4
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e1]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and]
    refine ⟨2 + 22 + k3 + 1, t4, ((s1.trans s2).trans s3).trans s4, by omega, ?_⟩
    rw [hok]; exact ⟨p4, regs4, frame4⟩
  rw [if_neg e1] at p4
  obtain ⟨t5, s5, p5, r5, f5⟩ := so52_spec hK t4 p4 ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (by have := hrow 1; omega)
    (by have := hrow 2; omega) (by rw [r4.get (by decide), g23]) (by rw [r4.get (by decide), g24])
  by_cases e2 : (selRow N c).getD 1 0 = (selRow N c).getD 2 0
  · rw [if_pos e2] at p5
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e2]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false]
    refine ⟨2 + 22 + k3 + 1 + 1, t5, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, ?_⟩
    rw [hok]
    exact ⟨p5, regs_mono (regs4.trans r5) (by decide),
      (frame4.trans f5).mono (by sel_frame)⟩
  rw [if_neg e2] at p5
  have hok : rowOk (selRow N c) = true := by
    rw [rowOk]; simp only [ne_eq, e1, e2, not_false_eq_true, decide_true, Bool.and_self]
  have hcost := selCost_le N c
  obtain ⟨t6, s6, p6, h21', m0, m8, m16, h25', h20', r6, f6⟩ :=
    so53_spec hK t5 p5 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (selBucket N c * 128) (21 + selCost N c) (SEL + 24 * c) c (by have := hrow 0; omega) (by have := hrow 1; omega) (by have := hrow 2; omega)
      (by simp only [SEL]; omega) (by simp only [SEL]; omega)
      (by rw [r5.get (by decide), r4.get (by decide), g22])
      (by rw [r5.get (by decide), r4.get (by decide), g23])
      (by rw [r5.get (by decide), r4.get (by decide), g24])
      (by rw [r5.get (by decide), r4.get (by decide), h6]; rfl)
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x21])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x25])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x20])
  refine ⟨2 + 22 + k3 + 1 + 1 + 44, t6, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6,
    by omega, ?_⟩
  rw [if_pos hok]
  have fr0 := (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6)
  have fr : Frame t t6 SelW := fr0.mono (by sel_frame)
  refine ⟨p6, h20', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h21', selCost_succ]; unfold rowCost; congr 1; omega
  · rw [h25']; congr 1
  · intro c' hc'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · exact hI.ok c' h
    · exact hok
  · intro c' hc' j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · rw [fr0.get (by simp only [SEL]; omega) (by simp only [SEL, or_false, false_or]; omega)]
      exact hI.rows c' h j hj
    · interval_cases j
      · simpa [selBucket, Nat.add_comm] using m0
      · simpa [selBucket, Nat.add_comm] using m8
      · simpa [selBucket, Nat.add_comm] using m16
  · exact regs_mono (regs4.trans (r5.trans r6)) (by decide)
  · exact (hI.frame.trans fr).mono (by intro A _ hA; rcases hA with hA | hA <;> exact hA)
theorem sel_loop (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) :
    ∀ n c t, c + n = 7 → SelInv b s0 N c t →
      ∃ k u, Steps image t k k u ∧ k ≤ 90 * n ∧
        ((u.pc = pcOf (b + 101) ∧ (List.range 7).all (fun c => rowOk (selRow N c)) = false ∧
          RegsExcept s0 u selRegs ∧ Frame s0 u SelW) ∨ SelInv b s0 N 7 u) := by
  intro n
  induction n with
  | zero => intro c t hc hI; exact ⟨0, t, Steps.refl t, le_refl _, Or.inr (by simpa using hc ▸ hI)⟩
  | succ n ih =>
    intro c t hc hI
    obtain ⟨k1, t1, s1, k1le, h1⟩ := sel_body hK hN (by omega) hI
    by_cases hok : rowOk (selRow N c) = true
    · rw [if_pos hok] at h1
      obtain ⟨k2, t2, s2, k2le, h2⟩ := ih (c + 1) t1 (by omega) h1
      exact ⟨k1 + k2, t2, s1.trans s2, by rw [Nat.mul_succ]; omega, h2⟩
    · rw [if_neg hok] at h1
      refine ⟨k1, t1, s1, by rw [Nat.mul_succ]; omega, Or.inl ⟨h1.1, ?_, h1.2⟩⟩
      rw [List.all_eq_false]
      exact ⟨c, List.mem_range.2 (by omega), hok⟩
theorem selectOk_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 640 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.admissible (T3.selections N) then 1 else 0) ∧
      (T3.admissible (T3.selections N) = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨t0, s0', p0, h21, h20, h25, r0, f0⟩ := so3_spec hK s hpc
  have hI : SelInv b s N 0 t0 :=
    ⟨p0, h20, by simpa [selCost_zero] using h21, by simpa using h25, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), regs_mono r0 (by decide), f0.mono (by intro _ _ h; exact h.elim)⟩
  obtain ⟨k1, t1, s1, k1le, h⟩ := sel_loop hK hN 7 0 t0 rfl hI
  have hx1 : ∀ u, RegsExcept s u selRegs → u.getReg .x1 = pcOf ret := fun u hu => by
    rw [hu.get (by decide), h1]
  rcases h with ⟨p1, hall, r1, f1⟩ | hI7
  · obtain ⟨t2, s2, p2, h13, r2, f2⟩ := so101_spec hK t1 p1 ret (hx1 t1 r1)
    have hadm : T3.admissible (T3.selections N) = false := by
      rw [admissible_selections, hall, Bool.false_and]
    refine ⟨4 + k1 + 2, t2, (s0'.trans s1).trans s2, by omega, p2, by rw [h13, hadm]; rfl,
      fun h => by rw [hadm] at h; exact absurd h (by decide), regs_mono (r1.trans r2) (by decide),
      f1.trans f2 |>.mono (by intro A _ hA; rcases hA with hA | hA; exact hA; exact hA.elim)⟩
  · have hS := selCost_le N 7
    obtain ⟨t2, s2, p2, r2, f2⟩ := so7_spec hK t1 hI7.pc 7 (le_refl _) hI7.x20
    rw [if_neg (by omega)] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ := so97_spec hK t2 p2 (21 + selCost N 7) (by omega)
      (by rw [r2.get (by decide), hI7.x21])
    have hall : (List.range 7).all (fun c => rowOk (selRow N c)) = true :=
      List.all_eq_true.2 (fun c hc => hI7.ok c (List.mem_range.1 hc))
    have rr : RegsExcept s t3 selRegs := regs_mono ((hI7.regs.trans r2).trans r3) (by decide)
    have ff : Frame t1 t3 (fun _ => False) := (f2.trans f3).mono (by intro A _ hA; simpa using hA)
    by_cases hc : 116 ≤ 21 + selCost N 7
    · rw [if_pos hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so101_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = false := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun h => by rw [hadm] at h; exact absurd h (by decide),
        regs_mono (rr.trans r4) (by decide), ?_⟩
      exact ((hI7.frame.trans ff).trans f4).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)
    · rw [if_neg hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so99_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = true := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      have fr : Frame t1 t4 (fun _ => False) := (ff.trans f4).mono (by intro A _ hA; simpa using hA)
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun _ c hc j hj => ?_, regs_mono (rr.trans r4) (by decide),
        (hI7.frame.trans fr).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)⟩
      rw [fr.get (by simp only [SEL]; omega) (by simp)]
      exact hI7.rows c hc j hj
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
theorem gatedSelect_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 646 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.digestAdmissible N then 1 else 0) ∧
      (T3.digestAdmissible N = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨u, hs, hp, hr, hf⟩ := gate_head_spec hK hG s hpc N hN
  have hN' : NAt u N := by intro j hj; rw [hf.get (by simp only [NBUF]; omega) (by simp)]; exact hN j hj
  have hu1 : u.getReg .x1 = pcOf ret := by rw [hr.get (by decide), h1]
  by_cases hg : N.toNat / 2 ^ 206 % 8 = 0
  · rw [if_pos hg] at hp
    obtain ⟨v, hs', hp', hr', hf'⟩ := gate_jump_spec hK hG u hp
    have hN'' : NAt v N := by intro j hj; rw [hf'.get (by simp only [NBUF]; omega) (by simp)]; exact hN' j hj
    have hv1 : v.getReg .x1 = pcOf ret := by rw [hr'.get (by decide), hu1]
    obtain ⟨k, t, st, hk, pt, ht13, htrows, rt, ft⟩ := selectOk_spec hK v hp' ret hv1 N hN''
    have hgB : T3.digestGate N = true := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = true; exact decide_eq_true hg
    have he : T3.digestAdmissible N = T3.admissible (T3.selections N) := by simp only [T3.digestAdmissible, hgB, Bool.and_true]
    refine ⟨5 + 1 + k, t, (hs.trans hs').trans st, by omega, pt, by simpa [he] using ht13,
      by simpa [he] using htrows, ?_, ?_⟩
    · exact regs_mono ((hr.trans hr').trans rt) (by decide)
    · exact ((hf.trans hf').trans ft).mono (by intro A _ h; simpa using h)
  · rw [if_neg hg] at hp
    obtain ⟨t, st, pt, ht13, rt, ft⟩ := so101_spec hK u hp ret hu1
    have hgB : T3.digestGate N = false := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = false; exact decide_eq_false hg
    have he : T3.digestAdmissible N = false := by simp only [T3.digestAdmissible, hgB, Bool.and_false]
    refine ⟨7, t, hs.trans st, by decide, pt, by simpa [he] using ht13,
      by simp [he], ?_, ?_⟩
    · exact regs_mono (hr.trans rt) (by decide)
    · exact (hf.trans ft).mono (by intro A _ h; simpa using h)
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
section blocks
variable {image : Image} {d b : Nat}
end blocks
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
section pieces
variable {im : Image}
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
end PairCopy
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
section code
variable {im : Image}                        
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
