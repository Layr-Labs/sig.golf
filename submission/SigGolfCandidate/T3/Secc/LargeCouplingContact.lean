import SigGolfCandidate.T3.Secc.LargeCouplingChain

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Contact
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem probEvent_bind_le_of {α β γ : Type} (mx : ProbComp α) (my : SPMF α) (f : α → ProbComp β) (g : α → SPMF γ)
    (E : β → Prop) (F : γ → Prop) (hw : ∀ x, Pr[= x | mx] = Pr[= x | my]) (h : ∀ x, Pr[E | f x] ≤ Pr[F | g x]) :
    Pr[E | mx >>= f] ≤ Pr[F | my >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by rw [hw x]; gcongr; exact h x
theorem uniform_weight {α : Type} [Fintype α] [Nonempty α] (s1 s2 : SampleableType α) (x : α) :
    Pr[= x | (@uniformSample α s1 : ProbComp α)] = Pr[= x | 𝒮[(@uniformSample α s2 : ProbComp α)]] := by
  rw [show Pr[= x | 𝒮[(@uniformSample α s2 : ProbComp α)]] = Pr[= x | (@uniformSample α s2 : ProbComp α)] from rfl,
    probOutput_uniformSample, probOutput_uniformSample]
theorem evalSPMF_uniform_inst {α : Type} [Fintype α] [Nonempty α] (s1 s2 : SampleableType α) :
    𝒮[(@uniformSample α s1 : ProbComp α)] = 𝒮[(@uniformSample α s2 : ProbComp α)] := by
  apply evalSPMF_ext
  intro x
  rw [probOutput_uniformSample, probOutput_uniformSample]
theorem weight_self {α : Type} (mx : ProbComp α) (x : α) : Pr[= x | mx] = Pr[= x | 𝒮[mx]] := rfl
end Contact
end SigGolfCandidate.T3.Security.LargeCoupling
