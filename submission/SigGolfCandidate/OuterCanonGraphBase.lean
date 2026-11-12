import SigGolfCandidate.OuterCanonicalNodeQueries
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterCanonGraph
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security
open ChainGraph (Point)
abbrev LeafPos := ClaudeWCT.W9.T3.Security.CanonGraph.LeafPos
abbrev SrcLeaf := ClaudeWCT.W9.T3.Security.CanonGraph.SrcLeaf
abbrev TreeNodeRaw := ClaudeWCT.W9.T3.Security.CanonGraph.TreeNodeRaw
abbrev TreeNode := ClaudeWCT.W9.T3.Security.CanonGraph.TreeNode
abbrev WctAddr := ClaudeWCT.W9.T3.Security.CanonGraph.WctAddr
abbrev WctPoint := ClaudeWCT.W9.T3.Security.CanonGraph.WctPoint
abbrev WctLeafPos := ClaudeWCT.W9.T3.Security.CanonGraph.WctLeafPos
abbrev WctCoef := ClaudeWCT.W9.T3.Security.CanonGraph.WctCoef
abbrev CoefficientAddress := ClaudeWCT.W9.T3.Security.CanonGraph.CoefficientAddress
abbrev SecretIndex := ClaudeWCT.W9.T3.Security.CanonGraph.SecretIndex
abbrev Secrets := ClaudeWCT.W9.T3.Security.CanonGraph.Secrets
structure WctNodeRaw where
  index : Fin (2^31)
  coord : Fin 9
  level : Fin 6
  idx : Fin 64
  nonce : Fin 4096
  deriving DecidableEq, Fintype
def WctNodeRaw.Valid (n : WctNodeRaw) : Prop := n.idx.val < 2 ^ (7 - n.level.val - 1)
instance instDecidablePredWctNodeRawValid : DecidablePred WctNodeRaw.Valid := fun n => by unfold WctNodeRaw.Valid; infer_instance
abbrev WctNodePos := {n : WctNodeRaw // n.Valid}
inductive Node where
  | chain (point : Point)
  | leaf (pos : SrcLeaf)
  | node (pos : TreeNode)
  | wctChain (point : WctPoint)
  | wctLeaf (pos : WctLeafPos)
  | wctNode (pos : WctNodePos)
  | forest (index : Fin (2^31))
  deriving DecidableEq, Fintype
attribute [local irreducible] ChainGraph.instFintypeAddress
def Node.depth : Node → Nat
  | .chain p => p.2.val
  | .leaf _ => 7
  | .node n => 8 + n.1.level.val * 2 ^ 18 + n.1.nonce.val
  | .wctChain p => p.2.val
  | .wctLeaf L => 4096 * (4 + 7 * L.coord.val)
  | .wctNode n => 4096 * (5 + 7 * n.1.coord.val + n.1.level.val) + n.1.nonce.val
  | .forest _ => 4096 * 70

abbrev Labels := Node → HashOutput
#print axioms instFintypeNode
end OuterCanonGraph
