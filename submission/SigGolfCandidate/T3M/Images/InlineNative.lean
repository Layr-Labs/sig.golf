import SigGolfCandidate.T3M.Images.InlineBlueprint
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailWords

namespace SigGolfCandidate.T3M.Images.InlineNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
set_option autoImplicit false
set_option maxRecDepth 200000
def patchRow (rank : Nat) (row : List (BitVec 32)) : List (BitVec 32) :=
  row.take 40 ++ Nonbinary.InlineTail.words rank ++ List.replicate (64-(Nonbinary.InlineTail.words rank).length) 19 ++ row.drop 104

def mapRows (start : Nat) : List (List (BitVec 32)) → List (List (BitVec 32))
  | [] => []
  | row::rows =>
      (if 691 ≤ start ∧ start<755 then patchRow (start-691) row else row)::
        mapRows (start+1) rows
def chunks : List (List (BitVec 32)) := mapRows 0 InlineBlueprint.originalChunks
def code : List (BitVec 32) := chunks.flatten
def image : Image := ⟨code,InlineBlueprint.verifyData⟩

end SigGolfCandidate.T3M.Images.InlineNative
