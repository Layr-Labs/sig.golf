import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailLayout
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout

/- Real finite ordinary windows of the new64 complete three-chain macros.
   Expected heads, copies and rungs are the attributed original T3M effects;
   the windows are actual literal new macro words at their new addresses.
   No chain output, oracle answer, or whole Verify result is supplied. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def run (rank pc fuel : Nat) : Option Result :=
  symRun {} ((words rank).drop (pc-armPC rank)) (pcOf pc) fuel

def headResult (rank ordinal : Nat) : Result :=
  let d := digit rank ordinal
  let i := 51+ordinal
  let p := chainPC rank ordinal
  if d=3 then copyFH .x8 (off i) (slot i) p
  else if d=2 then headRHT .x8 (off i) d (slot i) p i
  else headRH .x8 (off i) d none p i

def headCheck (rank ordinal : Nat) : Bool :=
  rOK (run rank (chainPC rank ordinal) (if digit rank ordinal=3 then 4 else 5))
    (headResult rank ordinal)

def rungCheck (rank ordinal step : Nat) : Bool :=
  let p := rungPC rank ordinal step
  rOK (run rank p 3) (rungR step (if step=2 then some (slot (51+ordinal)) else none) p)

def macroCheck (rank : Nat) : Bool :=
  (List.range 3).all fun ordinal =>
    headCheck rank ordinal && ((List.range' (digit rank ordinal+1)
      (2-digit rank ordinal)).all fun step => rungCheck rank ordinal step)

-- The fused leaf prefix is retained literally; this final JALR remains.
def leafWords : List (BitVec 32) := [3758981523,540031011,541080611,
  1442854947,1442855971,4027417107,536872211,939525523,
  66844435,1594296083,8853267,458855]

theorem macro_checks : ((List.range 64).all macroCheck)=true := by
  decide +kernel

theorem leaf_words_check : ((List.range 64).all fun rank =>
    decide ((words rank).drop (chainPC rank 3-armPC rank)=leafWords))=true := by
  decide +kernel

theorem head_run (rank ordinal : Nat) (hr : rank<64) (ho : ordinal<3) :
    run rank (chainPC rank ordinal) (if digit rank ordinal=3 then 4 else 5)=
      some (headResult rank ordinal) := by
  have h := List.all_eq_true.mp macro_checks rank (List.mem_range.mpr hr)
  have h' := List.all_eq_true.mp h ordinal (List.mem_range.mpr ho)
  simp only [Bool.and_eq_true] at h'
  exact rOK_eq h'.1

theorem rung_run (rank ordinal step : Nat) (hr : rank<64) (ho : ordinal<3)
    (hd : digit rank ordinal<step) (hs : step≤2) :
    run rank (rungPC rank ordinal step) 3=
      some (rungR step (if step=2 then some (slot (51+ordinal)) else none)
        (rungPC rank ordinal step)) := by
  have h := List.all_eq_true.mp macro_checks rank (List.mem_range.mpr hr)
  have h' := List.all_eq_true.mp h ordinal (List.mem_range.mpr ho)
  have hm : step∈List.range' (digit rank ordinal+1) (2-digit rank ordinal) := by
    rw [List.mem_range'_1]
    omega
  simp only [Bool.and_eq_true] at h'
  exact rOK_eq (List.all_eq_true.mp h'.2 step hm)

#print axioms macro_checks
#print axioms leaf_words_check
#print axioms head_run
#print axioms rung_run
end SigGolfCandidate.T3M.Nonbinary.InlineTail
