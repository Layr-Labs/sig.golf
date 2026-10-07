import SigGolfCandidate.T3M.Verify.Judg
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Layout

set_option autoImplicit false
namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
structure Layout where
  image : Image
  chainWord : Fin 728 → Nat
  childWord : Fin 128 → Nat
  returnWord : Fin 9 → Nat
def GoodQFor (im : Image) (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat)
    (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F im s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F im s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F im s)).exit = .success → HashOk hash →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ A)
structure Budget where
  fuel : Nat
  allCycles : Nat
  acceptCycles : Nat
def layerEntryWord : Nat := 33360
def layerWitnessOffset : Nat := 8104
def forestRootAddress : Nat := 0x100
def coordinateBase (k : Fin 9) : Nat := 2080 + 896 * k.val
def headerTable (k : Fin 9) : Nat := 0xfee600 + 512 * k.val
def forestInputAddress : Nat := 0xffbdf0
def pairAddress (k : Fin 9) : Nat := forestInputAddress + 32 + 32 * k.val
abbrev WBytes := ClaudeWCT.W9.T3M.WBytes
abbrev wdig (w : WBytes) (off : Nat) : SigGolfCandidate.T3.Digest := ClaudeWCT.W9.T3M.wdig w off
def OrigW (w : WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A - 0x800)) 64
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
    (hA : 0x800 ≤ A) : DigAt s A (wdig w (A - 0x800)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 - 0x800 = A - 0x800 + 8 by omega]
end W9Machine
