import SigGolfCandidate.ClaudeWCT.W9.New.Machine.VLib
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def blkO (l : Nat) : Nat := 64 * (6 - l)
def curO (l j : Nat) : Nat := blkO l + 48 * bitAt j l
def sibO (l j : Nat) : Nat := blkO l + 48 * (1 - bitAt j l)
def padO (l : Nat) : Nat := blkO l + 32
def leafO : Nat := 816
def heapOf (l j : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
def nodeLo (k index : Nat) : Nat := 1537 + 65536 * k + 2 ^ 27 * index
def heapReg (h : Nat) : Reg :=
  match h with
  | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | _ => .x30
def leafBytes (leaf : Nat → Digest) : List UInt8 := (List.range 8).flatMap fun i => bytesLE 16 (leaf i)
def childLevel (k index j : Nat) (sibs : Nat → Digest) (value : Digest) (l : Nat) : M Digest :=
  let pair := if bitAt j l = 0 then (value, sibs l) else (sibs l, value)
  WCT9.wctNodeHash k index (heapOf l j) pair.1 pair.2
def pairOf (j : Nat) (top sib : Digest) : Digest × Digest := if bitAt j 6 = 0 then (top, sib) else (sib, top)
def childProgC (k index j : Nat) (leaf sibs : Nat → Digest) : M (Digest × Digest) := do
  let v ← shortHash (leafBytes leaf)
  let top ← (List.range 6).foldlM (childLevel k index j sibs) v
  pure (pairOf j top (sibs 6))
def stageW (j l : Nat) : List Nat :=
  [curO l j, curO l j + 8, curO l j + 16, curO l j + 24, blkO l + 16, blkO l + 24]
def stagesW (j n : Nat) : List Nat := (List.range n).flatMap (stageW j)
def childWrites (j : Nat) : List Nat := stagesW j 6
/-- The 8 leaf digests (T8): `end0 | header | pad (honest 0) | end1..end5`. -/
def leafFields (k index j : Nat) (ends : List Digest) (i : Nat) : Digest :=
  if i = 0 then ends.getD 0 0 else if i = 1 then ClaudeWCT.WCT9.ftsLeafHeader index k j
  else if i = 2 then 0 else ends.getD (i - 2) 0
def sixLevels (k index j : Nat) (path : Nat → Digest) (root : Digest) : M Digest :=
  (List.range 6).foldlM (fun value l =>
    let other := path l
    let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.WCT9.wctNodeHash k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2) root
def finPath (path : Fin 7 → Digest) (l : Nat) : Digest := if h : l < 7 then path ⟨l, h⟩ else 0
end ClaudeWCT.W9.Machine.Merkle
