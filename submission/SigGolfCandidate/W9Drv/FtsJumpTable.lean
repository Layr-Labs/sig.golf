import SigGolfCandidate.W9Drv.SourceBridge
import SigGolfCandidate.W9Drv.Gate
import SigGolfCandidate.T3M.Verify.AfterDefs
import SigGolfCandidate.T3M.Verify.Common

section


namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def jtStart : Nat := 218624
def jtReject : Nat := 32792
def chainEntries : List Nat := Frozen.chainEntries
def jtTarget (field : Nat) : Nat :=
  if field < 16200 then Frozen.layout.chainWord (N600.embed ⟨field % 600, Nat.mod_lt _ (by decide)⟩)
  else jtReject
def jtCheck (start : Nat) (words : List (BitVec 32)) : Bool :=
  words.zipIdx.all fun wi =>
    rOK (symRun {} [wi.1] (pcOf (jtStart + start + wi.2)) 1)
      ⟨SymState.init, .c (pcOf (jtTarget (start + wi.2))), .jump, 1, 1⟩
end W9Drv
namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def jtChunk (c : Fin 64) : List (BitVec 32) :=
  (W9Machine.Frozen.codeFrom (jtStart + 256 * c.val)).take 256
theorem jtChunk_length (c : Fin 64) : (jtChunk c).length = 256 := by
  fin_cases c <;> decide +kernel
theorem jtChunk_checked (c : Fin 64) : jtCheck (256 * c.val) (jtChunk c) = true := by
  fin_cases c <;> decide +kernel
theorem jtChunk_linked (c : Fin 64) : CodeAt Frozen.image (pcOf (jtStart + 256 * c.val)) (jtChunk c) := by
  apply slice_at
  fin_cases c <;> decide +kernel
end W9Drv
end

