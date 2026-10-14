import SigGolfCandidate.T3.Secc.WotsMaskChain

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
variable (a : ChainAddr)
theorem lay_eq_of_header {lay : Layer} {t t' tree pos leaf tree' pos' leaf' : Nat}
    (h : header t lay.val tree pos leaf = header t' a.key.lay.val tree' pos' leaf') : lay = a.key.lay := by
  have hl := (header_fields h).2.1
  apply Fin.ext
  rw [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
    Nat.mod_eq_of_lt (lt_trans a.key.lay.isLt (by decide))] at hl
  exact hl
theorem untouched_chainInput_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i s : Nat) (v : Digest) :
    Untouched a (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  intro step value _ heq
  rw [pad64_chainInput] at heq
  exact hl (chainHeader_fields (chainInput_fields heq).1).1
theorem respects_chain_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i start count : Nat) (v : Digest) :
    Respects (Untouched a) (chain lay tree leaf i start count v) := by
  unfold chain
  exact Respects.foldlM _ _ (fun step _ value => Respects.shortHash _ (untouched_chainInput_of_lay a hl _ _ _ _ _))
    _
variable {T T' : Answers} (hT : ∀ q, Untouched a q → T q = T' q)
include hT
end Mask
end SigGolfCandidate.T3.Security.Wots
