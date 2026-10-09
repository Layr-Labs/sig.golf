import SigGolfCandidate.T3.BPORS

section
namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree
abbrev S (answers : Answers) (index coord leaf : Nat) : Digest := Extract.ftsSecret answers index coord leaf
theorem hdrBlock_nodeInputP (tag lay tree heap : Nat) (l p r : Digest) :
    Extract.hdrBlock (nodeInputP tag lay tree heap l p r) = bytesLE 16 (nodeTweak tag lay tree heap) := by
  unfold nodeInputP; exact Extract.hdrBlock_block4 _ _ _ _
theorem hdrBlock_ftsLeafInputP (index coord leaf : Nat) (a s b : Digest) :
    Extract.hdrBlock (ftsLeafInputP index coord leaf a s b) = bytesLE 16 (header 9 coord index 0 leaf) := by
  unfold ftsLeafInputP; exact Extract.hdrBlock_block4 _ _ _ _
end SigGolfCandidate.T3.Security.BSuf
end
section
namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree
end SigGolfCandidate.T3.Security.BSuf
end
