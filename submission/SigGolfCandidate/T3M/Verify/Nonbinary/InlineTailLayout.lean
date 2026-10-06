import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailWords

/- Source-only next common54 child. The real three-chain macro has no entry
   JAL. It retains all nine-minus-digits chain queries and all twelve fused
   leaf-prefix words. Neither this schedule nor its native adapter is a
   complete Verify proof. Original T3M/PR635 body attribution is preserved. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def digit (rank ordinal : Nat) : Nat := rank / 4^ordinal % 4
def pieceLen (d : Nat) : Nat :=
  if d=3 then 4 else 4+2*(3-d)-(if d=2 then 1 else 0)
def chainPC (rank ordinal : Nat) : Nat :=
  armPC rank + ((List.range ordinal).map fun j => pieceLen (digit rank j)).sum
def queryPC (rank ordinal step : Nat) : Nat :=
  chainPC rank ordinal + 4 + 2*(step-digit rank ordinal) +
    (if digit rank ordinal < step ∧ step=2 then 1 else 0)
def rungPC (rank ordinal step : Nat) : Nat :=
  queryPC rank ordinal step - (if step=2 then 2 else 1)
def macroOrdinary (rank : Nat) : Nat := (words rank).length-hashes rank

theorem digit_lt (rank ordinal : Nat) : digit rank ordinal<4 := by
  exact Nat.mod_lt _ (by decide)

theorem piece_len_cases : (List.range 4).map pieceLen=[10,8,5,4] := by
  decide +kernel

theorem macro_length_check : ((List.range 64).all fun rank =>
    decide ((words rank).length=pieceLen (digit rank 0)+pieceLen (digit rank 1)+
      pieceLen (digit rank 2)+12))=true := by decide +kernel

theorem leaf_pc_check : ((List.range 64).all fun rank =>
    decide (leafPC rank=chainPC rank 3))=true := by decide +kernel

theorem body_fits_check : ((List.range 64).all fun rank =>
    decide (armPC rank+(words rank).length≤176744+256*rank+256))=true := by
  decide +kernel

-- Every query is the literal ECALL word, including the very last chain step.
theorem query_words_check : ((List.range 64).all fun rank =>
    ((List.range 3).all fun ordinal =>
      ((List.range' (digit rank ordinal) (3-digit rank ordinal)).all fun step =>
        decide ((words rank)[queryPC rank ordinal step-armPC rank]?=some 115))))=true := by
  decide +kernel

#print axioms macro_length_check
#print axioms leaf_pc_check
#print axioms body_fits_check
#print axioms query_words_check
end SigGolfCandidate.T3M.Nonbinary.InlineTail
