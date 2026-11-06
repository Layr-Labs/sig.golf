import SigGolfCandidate.Merge091
import SigGolfCandidate.FtsExpandSearch
set_option linter.all false

/-! # FTS carrier grind: expand-owned copies of the first-coordinate (A) child routines, piece checks

Copy `j` sits at `copyBase j` (`COPY_FIRST + 32 j`) and holds the bank routine's words up to its level-3
(heap 8..15) fold, whose `ecall` is replaced by `jal zero, trampOf j`. The trampoline returns into the bank right
after the bank's level-3 `ecall`, so the bank's level-4 and hand code (already proved) finish the routine.

This module checks the prefix pieces (leaf, levels 0..3) of all 128 copies by kernel evaluation, as Merge091
does for the bank. -/

namespace W9Drv.SharedAProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bank slot of child `j` (A: the table slot). -/
def cSlot (j : Nat) : Nat := j
def copyBase (j : Nat) : Nat := SigGolfCandidate.FtsGrind.COPY_FIRST + 32 * cSlot j
def trampOf (j : Nat) : Nat := SigGolfCandidate.FtsGrind.TRAMP + 5 * (0 * 128 + cSlot j)
/-- The level-3 fold site in the copy and in the bank. -/
def siteC (j : Nat) : Nat := copyBase j + ecIdx j 4
def siteB (j : Nat) : Nat := childBase j + ecIdx j 4
def copyPre (j : Nat) : List (BitVec 32) :=
  (childWords j).take (ecIdx j 4) ++
    [SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (siteC j) (trampOf j))]
def copyLook (j n : Nat) : Option (BitVec 32) :=
  if copyBase j ≤ n then (copyPre j)[n - copyBase j]? else none
/-- Symbolic run in the copy from word `i`, stopping before the site `jal`. -/
def copyRun (j i : Nat) : Option PRes :=
  pathAux cfg0 (copyLook j) [pcOf (siteC j)] 64 (pcOf (copyBase j + i)) [] (σK []) []
def cp0Res (j : Nat) : PRes := { p0Res j with pc := pcOf (copyBase j + 2) }
def clvlRes (j l : Nat) : PRes :=
  { lvlRes j l with pc := pcOf (copyBase j + ecIdx j (l + 1)), ecall := decide (l < 3) }
def copyPiecesOK (j : Nat) : Bool :=
  optBeq (copyRun j 1) (cp0Res j) &&
    (List.range 4).all (fun l => optBeq (copyRun j (ecIdx j l + 1)) (clvlRes j l)) &&
    decide (ecIdx j 4 ≤ (childWords j).length) && !(hiSel j 4) &&
    decide (padO j 3 + 16 ≤ 784) && decide (ecIdx j 4 + 1 < 32 ∧ padO j 4 ≠ padO j 3 ∧ sibO 4 j ≠ padO j 3)
def copyPiecesRange (lo n : Nat) : Bool := (List.range' lo n).all copyPiecesOK

theorem copyPieces_0 : copyPiecesRange 0 16 = true := by decide +kernel
theorem copyPieces_1 : copyPiecesRange 16 16 = true := by decide +kernel
theorem copyPieces_2 : copyPiecesRange 32 16 = true := by decide +kernel
theorem copyPieces_3 : copyPiecesRange 48 16 = true := by decide +kernel
theorem copyPieces_4 : copyPiecesRange 64 16 = true := by decide +kernel
theorem copyPieces_5 : copyPiecesRange 80 16 = true := by decide +kernel
theorem copyPieces_6 : copyPiecesRange 96 16 = true := by decide +kernel
theorem copyPieces_7 : copyPiecesRange 112 16 = true := by decide +kernel

theorem copyPiecesOK_at (j : Nat) (hj : j < 128) : copyPiecesOK j = true := by
  have hall : ∀ lo n, copyPiecesRange lo n = true → lo ≤ j → j < lo + n → copyPiecesOK j = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : j < 16; · exact hall 0 16 copyPieces_0 (by omega) (by omega)
  by_cases h1 : j < 32; · exact hall 16 16 copyPieces_1 (by omega) (by omega)
  by_cases h2 : j < 48; · exact hall 32 16 copyPieces_2 (by omega) (by omega)
  by_cases h3 : j < 64; · exact hall 48 16 copyPieces_3 (by omega) (by omega)
  by_cases h4 : j < 80; · exact hall 64 16 copyPieces_4 (by omega) (by omega)
  by_cases h5 : j < 96; · exact hall 80 16 copyPieces_5 (by omega) (by omega)
  by_cases h6 : j < 112; · exact hall 96 16 copyPieces_6 (by omega) (by omega)
  exact hall 112 16 copyPieces_7 (by omega) (by omega)

theorem copyRun_p0 (j : Nat) (hj : j < 128) : copyRun j 1 = some (cp0Res j) := by
  have h := copyPiecesOK_at j hj
  simp only [copyPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq h.1.1.1.1.1
theorem copyRun_lvl (j : Nat) (hj : j < 128) (l : Nat) (hl : l < 4) :
    copyRun j (ecIdx j l + 1) = some (clvlRes j l) := by
  have h := copyPiecesOK_at j hj
  simp only [copyPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq (List.all_eq_true.mp h.1.1.1.1.2 l (List.mem_range.mpr hl))
theorem ecIdx4_le (j : Nat) (hj : j < 128) : ecIdx j 4 ≤ (childWords j).length := by
  have h := copyPiecesOK_at j hj
  simp only [copyPiecesOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2
theorem hiSel_four (j : Nat) (hj : j < 128) : hiSel j 4 = false := by
  have h := copyPiecesOK_at j hj
  simp only [copyPiecesOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.1.2
theorem pad3_prefix (j : Nat) (hj : j < 128) : padO j 3 + 16 ≤ 784 := by
  have h := copyPiecesOK_at j hj
  simp only [copyPiecesOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2
theorem site_lt (j : Nat) (hj : j < 128) : ecIdx j 4 + 1 < 32 ∧ padO j 4 ≠ padO j 3 ∧ sibO 4 j ≠ padO j 3 := by
  have h := copyPiecesOK_at j hj
  simp only [copyPiecesOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

end W9Drv.SharedAProof
