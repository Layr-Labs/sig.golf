import SigGolfCandidate.W9Machine.WctChainTrace

namespace W9Machine
def pieceGuard (tr : ChainTrace) : ChainPieceKind → Bool
  | .head off dst chain digit => decide
      (320 ≤ off ∧ off + 64 ≤ 896 ∧ off % 8 = 0 ∧
       320 ≤ dst ∧ dst + 32 ≤ 896 ∧ dst % 8 = 0 ∧ chain < 7 ∧ digit < 3)
  | .rung digit dst =>
      decide (0 < tr.queries.length ∧ 320 ≤ tr.input ∧ tr.input + 64 ≤ 896 ∧
        tr.input % 8 = 0 ∧ 320 ≤ dst.getD tr.output ∧ dst.getD tr.output + 32 ≤ 896 ∧
        dst.getD tr.output % 8 = 0 ∧ digit < 3) &&
      match tr.read (tr.input + 16) with
      | .header chain old => decide (chain = tr.chain ∧ chain < 7 ∧ old < 3)
      | _ => false
  | .copy off dst => decide
      (off + 64 ≤ 896 ∧ off % 8 = 0 ∧ 320 ≤ dst ∧ dst + 16 ≤ 896 ∧ dst % 8 = 0)
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
