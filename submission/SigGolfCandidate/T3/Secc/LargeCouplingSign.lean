import SigGolfCandidate.T3.Secc.LargeCouplingCell
import SigGolfCandidate.T3.Secc.WotsExtractVerify

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafValue honestPieces forestOpenPrefix
  forestProofPrefix forestRoots forestOpened forestInner forestOuter)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_largeCouplingSign : DecidableEq T3.Cache := Classical.decEq _
section Honest
variable {T : Answers} {labels : Labels}
theorem honestValue_eq (h : Agrees T labels) : honestValue T = coordVal (secretsOf T) labels := by
  funext c
  cases c with
  | inl M =>
      change (T (.inl (.inr (Extract.honestInput T M.toPos)))).extractLsb' 0 128 = _
      rw [honest_answer h M]
      rfl
  | inr x => rfl
theorem filterMap_map_getD {α β γ : Type} (l : List α) (f : α → Option β) (v : β → γ) (d : γ)
    (h : ∀ a ∈ l, (f a).isSome) : (l.filterMap f).map v = l.map fun a => ((f a).map v).getD d := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have ha := h a List.mem_cons_self
      cases hf : f a with
      | none => rw [hf] at ha; cases ha
      | some b =>
          rw [List.filterMap_cons, hf]
          simp only [List.map_cons]
          rw [ih fun x hx => h x (List.mem_cons_of_mem _ hx), hf]
          rfl
end Honest
end SigGolfCandidate.T3.Security.LargeResidual
