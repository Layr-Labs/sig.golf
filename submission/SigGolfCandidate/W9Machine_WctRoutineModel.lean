import SigGolfCandidate.W9Machine_WctImage
import SigGolfCandidate.W9Machine_WctChainPieces
import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_VerifyP

section


namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
def chainEntries : List Nat := Frozen.chainEntries
end W9Machine
end

section



namespace W9Machine
open SigGolfCandidate.T3M
/-- Witness stack: FTS chain `t`'s block offset from `s0` (F 592, G 504, F 528, G 400, F 424, F 320). -/
def ftsOff (t : Nat) : Nat := ClaudeWCT.W9.T3M.wctChainOff t
/-- Where an interior step (and an in-place terminal step) leaves its output: F `off + 48` (the value slot),
G `off - 16` (the high half lands on the value at `off`). -/
def ftsOut (t : Nat) : Nat := if ClaudeWCT.WCT9.ftsIsG t then ftsOff t - 16 else ftsOff t + 48
/-- `.copy off dst` copies `off + 48`, `off + 56` (the 16 bytes at `ftsOut t`) to the leaf slot. -/
def expectedChainKinds (digits : List Nat) (t : Nat) : List ChainPieceKind :=
  let d := digits.getD t 0
  if d = 0 then [] else
    let off := ftsOff t
    let out := ftsOut t
    let slot := if t = 0 then 640 else 672 + 16 * t
    let own := 0 < t ∧ t < 5 ∧ digits.getD (t + 1) 0 = 0
    let dst := if own then out else slot
    [.head off (if d = 1 then dst else out) t (4 - d)] ++
      ((List.range' (5 - d) (d - 1)).map fun step ↦
        .rung step (if step = 3 ∧ dst ≠ out then some dst else none)) ++
      (if own then [.copy (out - 48) slot] else [])
def expectedKinds (digits : List Nat) : List ChainPieceKind :=
  (List.range 6).flatMap (expectedChainKinds digits) ++ [.leaf]
def ChainPiece.isHash (p : ChainPiece) : Bool :=
  match p.kind with
  | .head .. | .rung .. => true
  | _ => false
def ChainPiece.totalCycles (p : ChainPiece) : Nat :=
  p.result.cycles + if p.isHash then 8 else 0
def ChainPiece.nextPc (p : ChainPiece) : Nat :=
  match p.kind with
  | .jump target => target
  | _ => p.pc + p.words.length
structure ChainRoutine where
  rank : Nat
  digits : List Nat
  pieces : List ChainPiece
def ChainRoutine.cycles (r : ChainRoutine) : Nat := (r.pieces.map ChainPiece.totalCycles).sum
def ChainRoutine.fuel (r : ChainRoutine) : Nat := (r.pieces.map fun p ↦ p.words.length).sum
def ChainRoutine.checked (r : ChainRoutine) : Bool :=
  decide (r.rank < 666) &&
  (r.digits == (ClaudeWCT.WCT9.compositions 5 6 7).getD r.rank []) &&
  (r.pieces.head?.map ChainPiece.pc == some (chainEntries.getD r.rank 0)) &&
  (r.pieces.filterMap (fun p ↦ match p.kind with | .jump _ => none | k => some k)
    == expectedKinds r.digits) &&
  ((r.pieces.zip r.pieces.tail).all fun pq ↦ pq.2.pc == pq.1.nextPc) &&
  ((r.pieces.filter ChainPiece.isHash).length == 7) &&
  decide (r.cycles ≤ 89) && decide (r.fuel ≤ 40)
end W9Machine
end
