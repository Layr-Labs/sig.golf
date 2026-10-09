import SigGolfCandidate.T3.Secc.LargeCouplingLaw

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Chain
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
noncomputable def initComp : ProbComp AuxData :=
  ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
      ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => pure ⟨high, rows, priv⟩
noncomputable def initLaw : PMF AuxData := liftM initComp
theorem completeRows_none_apply (U : Finset HashInput) (table : Cell U → LargeResidual.HashOutput) :
    SphincsSecurity.Concrete.ResidualTableCompletion.completeRows (Cell := Cell U) (fun _ => none) table =
      Pr[= table | ($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] := by
  unfold SphincsSecurity.Concrete.ResidualTableCompletion.completeRows
  rw [SphincsSecurity.Concrete.UniformTableCompletion.complete_apply, if_pos (fun _ => by
      simp [SphincsSecurity.Concrete.ResidualTableCompletion.allowed]),
    probOutput_uniformSample, Fintype.card_fun]
  simp only [SphincsSecurity.Concrete.ResidualTableCompletion.allowed, Finset.prod_const, Finset.card_univ]
theorem completeRows_none (U : Finset HashInput) :
    SphincsSecurity.Concrete.ResidualTableCompletion.completeRows (Cell := Cell U) (fun _ => none) =
      𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] := by
  apply SPMF.ext
  intro table
  rw [completeRows_none_apply]
  rfl
section Lazy
variable {U : Finset HashInput}
theorem probEvent_bind_congr_eq {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] = Pr[E' | g x]) : Pr[E | m >>= f] = Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact tsum_congr fun x => by rw [h x]
end Lazy
end Chain
end SigGolfCandidate.T3.Security.LargeCoupling
