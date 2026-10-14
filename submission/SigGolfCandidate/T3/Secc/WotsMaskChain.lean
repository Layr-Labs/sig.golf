import SigGolfCandidate.T3.Secc.WotsMaskBase

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Mask
theorem eval_chain_one (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 1 v) =
      projHalf (chainHigh lay i s) (T (.inl (.inr (chainInput lay tree leaf i s v)))) := by
  rw [← pad64_chainInput]
  rfl
variable (answers : Answers) (a : ChainAddr)
end Mask
namespace Mask
variable (answers : Answers) (a : ChainAddr)
end Mask
end SigGolfCandidate.T3.Security.Wots
