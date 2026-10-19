import SigGolfCandidate.T3_Secc_CanonGraphHonest
import SigGolfCandidate.SphincsSecurity_Proof_Base_FirstSuccessFamily
import SigGolfCandidate.SphincsSecurity_Proof_Base_UniformTableOverwrite

namespace SigGolfCandidate.T3.Security.CanonEncoding
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev EncLeaf := {L : LeafPos // L.Source}
def EncLeaf.toWots (L : EncLeaf) : Wots.LeafAddr := ⟨L.1.lay, L.1.tree.val, L.1.leaf.val⟩
theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ treeBits lay := by
  fin_cases lay <;> simp [route, treeBits, height] <;> omega
theorem childIndex_lt (L : EncLeaf) : L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val < 2 ^ 31 := by
  obtain ⟨⟨lay, tree, leaf⟩, ht, hl⟩ := L
  change tree.val < 2 ^ treeBits lay at ht
  change leaf.val < 2 ^ height lay at hl
  change tree.val * 2 ^ height lay + leaf.val < 2 ^ 31
  fin_cases lay <;> simp [treeBits, height] at ht hl ⊢ <;> omega
def childIndex (L : EncLeaf) : Fin (2^31) :=
  ⟨L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val, childIndex_lt L⟩
def msgLabel (labels : Labels) (L : EncLeaf) : Digest :=
  if h : L.1.lay.val < 3 then
    treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩) 0
  else (labels (.forest (childIndex L))).extractLsb' 0 128
def decodeAt (L : EncLeaf) (answer : HashOutput) : Option Digest :=
  if (searchDecode L.1.lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none
abbrev Selection := Option (Fin (2^22) × Digest)
abbrev Selections := EncLeaf → Selection
noncomputable def rowsLaw (selections : Selections) : PMF (EncLeaf → Fin (2^22) → HashOutput) :=
  FinitePmfProduct.law (fun L => FirstSuccessTable.afterSelect (decodeAt L) (2^22) (selections L))
end SigGolfCandidate.T3.Security.CanonEncoding
