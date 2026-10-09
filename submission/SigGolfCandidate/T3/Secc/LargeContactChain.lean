import SigGolfCandidate.T3.Secc.LargeContactMonitor
import SigGolfCandidate.T3.Secc.WotsExtractVerify

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeContactChain : DecidableEq T3.Cache := Classical.decEq _
def wotsAddr (a : ChainGraph.Address) : Wots.ChainAddr := ⟨⟨a.layer, a.tree.val, a.leaf.val⟩, a.chain.val⟩
def Disclosed (A : Answers) (published : T3.Cache) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ request, c ∈ signDisclosed A published request
end SigGolfCandidate.T3.Security.LargeCoupling
