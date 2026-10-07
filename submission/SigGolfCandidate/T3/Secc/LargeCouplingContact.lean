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
def RealContact (adversary : AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  ContactR adversary q x.1 x.2
noncomputable def fixedNext (adversary : AdversaryP) (T : Answers) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  (fun r => (r, T)) <$> Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)
def worldEquiv : Secrets × ((Message → Digest) × LowLabels) ≃ (WCoord → LargeResidual.Digest) where
  toFun p := Sum.elim (Sum.elim p.2.2 p.1) p.2.1
  invFun lab := (fun s => lab (.inl (.inr s)), fun m => lab (.inr m), fun N => lab (.inl (.inl N)))
  left_inv p := rfl
  right_inv lab := by
    funext c
    rcases c with (N | s) | m <;> rfl
theorem world_split {R : Type} (K : Secrets → (Message → Digest) → LowLabels → ProbComp R) :
    𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => K sec nv low] =
      𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _) >>= fun lab =>
        K (fun s => lab (.inl (.inr s))) (fun m => lab (.inr m)) (fun N => lab (.inl (.inl N)))] := by
  let _ : SampleableType ((Message → Digest) × LowLabels) := SampleableType.ofFintype _
  let _ : SampleableType (Secrets × ((Message → Digest) × LowLabels)) := SampleableType.ofFintype _
  rw [uniform_equiv_bind worldEquiv, uniform_prod_bind]
  refine evalSPMF_bind_congr' _ fun sec => ?_
  rw [uniform_prod_bind]
  rfl
theorem weight_self {α : Type} (mx : ProbComp α) (x : α) : Pr[= x | mx] = Pr[= x | 𝒮[mx]] := rfl
end Contact
end SigGolfCandidate.T3.Security.LargeCoupling
