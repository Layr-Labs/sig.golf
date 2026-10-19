import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEvents
import SigGolfCandidate.T3_Secc_WotsExtractChain

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
def PosSource : Extract.Pos → Prop
  | .chain lay tree leaf i step => tree < 2 ^ Extract.treeBits lay ∧ leaf < 2 ^ height lay ∧ i < chainCount lay ∧
      step + 1 < 2 ^ width lay i
  | .leaf lay tree leaf => tree < 2 ^ Extract.treeBits lay ∧ leaf < 2 ^ height lay
  | .node lay tree level node => tree < 2 ^ Extract.treeBits lay ∧ level < height lay ∧
      node < 2 ^ (height lay - level - 1) ∧ (lay = 0 ∨ level + 1 < height lay)
  | .forest index => index < 2 ^ 31
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6 ∧ step < 4
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
def StructuralHitSrc (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ PosSource position ∧ StructuralClass answers input position ∧
    Extract.HashHitAt answers position (Extract.honestInput answers position) input
end ClaudeWCT.W9.T3.Security.WotsExtract
