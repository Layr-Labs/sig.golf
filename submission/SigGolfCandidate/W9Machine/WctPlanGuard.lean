import SigGolfCandidate.W9Machine.WctChainTrace

namespace W9Machine
def pieceGuard (tr : ChainTrace) : ChainPieceKind → Bool
  | .head off dst chain digit => decide
      (320 ≤ off ∧ off + 64 ≤ 832 ∧ off % 8 = 0 ∧
       336 ≤ dst ∧ dst + 32 ≤ 832 ∧ dst % 8 = 0 ∧ chain < 6 ∧ digit < 4)
  | .rung digit dst =>
      decide (0 < tr.queries.length ∧ 320 ≤ tr.input ∧ tr.input + 64 ≤ 832 ∧
        tr.input % 8 = 0 ∧ 336 ≤ dst.getD tr.output ∧ dst.getD tr.output + 32 ≤ 832 ∧
        dst.getD tr.output % 8 = 0 ∧ digit < 4) &&
      match tr.read (tr.input + 16) with
      | .header chain old => decide (chain = tr.chain ∧ chain < 6 ∧ old < 4)
      | _ => false
  | .copy off dst => decide
      (off + 64 ≤ 832 ∧ off % 8 = 0 ∧ 336 ≤ dst ∧ dst + 16 ≤ 832 ∧ dst % 8 = 0)
  | .jump _ | .leaf => true
def planGuard : List ChainPiece → ChainTrace → Bool
  | [], _ => false
  | p :: ps, tr =>
      pieceGuard tr p.kind &&
      decide (p.words.length = p.result.steps + if p.isHash then 1 else 0) &&
      match p.kind with
      | .leaf => ps.isEmpty
      | _ => (ps.head?.map ChainPiece.pc == some p.nextPc) &&
          planGuard ps (tr.step p.kind)
end W9Machine
