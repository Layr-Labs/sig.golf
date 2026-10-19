import SigGolfCandidate.T3M_Verify_Judg
import SigGolfCandidate.T3M_Mem
import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Layout

set_option autoImplicit false
namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
structure Layout where
  image : Image
  chainWord : Fin 666 → Nat
  childWord : Fin 128 → Nat
  returnWord : Fin 9 → Nat
  /-- Base shift of the FTS frame in 8-byte units: verify runs the shared banks at `coordinateBase` (`0`); expand
  runs them 1224 bytes lower (`153`) and moves the block up afterwards. Only `min delta8 153` is used. -/
  delta8 : Nat
def GoodQFor (im : Image) (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat)
    (X : OracleComp HashSpec Obs) (P : Hash → Prop := HashOk) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F im s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F im s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F im s)).exit = .success → P hash →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ A)
structure Budget where
  fuel : Nat
  allCycles : Nat
  acceptCycles : Nat
def layerEntryWord : Nat := 32951
def layerWitnessOffset : Nat := 7664
def forestRootAddress : Nat := 0x100
/-- Nested FTS (r1-1, witness stack): region `n` (tree `n`, `n ≤ 8`) at `10992 - 848 n`; region 9 is the virtual tree below tree 8
(its leaf-pad and Z slots receive tree 8's top pair). -/
def regionAddr (n : Nat) : Nat := 10992 - 848 * n
def coordinateBase (k : Fin 9) : Nat := 4208 + 848 * (8 - k.val)
/-- Byte shift of the FTS frame of a layout (`0` for verify, `1224` for expand). -/
def Layout.shift (L : Layout) : Nat := 8 * min L.delta8 153
namespace Chain
/-- Base register `x8` of coordinate `k` in layout `L`. -/
abbrev base (L : Layout) (k : Fin 9) : Nat := coordinateBase k - L.shift
end Chain
theorem Layout.shift_le (L : Layout) : L.shift ≤ 1224 ∧ L.shift % 8 = 0 := by
  unfold Layout.shift; omega
theorem Chain.base_bounds (L : Layout) (k : Fin 9) :
    2984 ≤ Chain.base L k ∧ Chain.base L k ≤ 10992 ∧ Chain.base L k % 8 = 0 ∧
      Chain.base L k + L.shift = coordinateBase k := by
  have := k.isLt; unfold Chain.base coordinateBase Layout.shift; omega
def headerTable (k : Fin 9) : Nat := 0xfee600 + 512 * k.val
def forestInputAddress : Nat := 0xffbdf0
def pairAddress (k : Fin 9) : Nat := forestInputAddress + 32 + 32 * k.val
abbrev WBytes := ClaudeWCT.W9.T3M.WBytes
abbrev wdig (w : WBytes) (off : Nat) : SigGolfCandidate.T3.Digest := ClaudeWCT.W9.T3M.wdig w off
def OrigW (w : WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A - 0x1020)) 64
/-- `OrigW` for a frame shifted down by `d` bytes (witness byte `o` at `0x1020 - d + o`). -/
def OrigWD (d : Nat) (w : WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A + d - 0x1020)) 64
theorem wdig_lo (w : WBytes) (off : Nat) : (wdig w off).extractLsb' 0 64 = w.extractLsb' (8 * off) 64 := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem wdig_hi (w : WBytes) (off : Nat) :
    (wdig w off).extractLsb' 64 64 = w.extractLsb' (8 * (off + 8)) 64 := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (off + 8) = 8 * off + 64 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize w.toNat / 2 ^ (8 * off) = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem DigAt_origW {w : WBytes} {s : MachineState} {A : Nat} (h0 : OrigW w s A) (h1 : OrigW w s (A + 8))
    (hA : 0x1020 ≤ A) : DigAt s A (wdig w (A - 0x1020)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 - 0x1020 = A - 0x1020 + 8 by omega]
theorem DigAt_origWD {d : Nat} {w : WBytes} {s : MachineState} {A : Nat} (h0 : OrigWD d w s A)
    (h1 : OrigWD d w s (A + 8)) (hA : 0x1020 ≤ A + d) : DigAt s A (wdig w (A + d - 0x1020)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 + d - 0x1020 = A + d - 0x1020 + 8 by omega]
end W9Machine
