import SigGolfCandidate.T3.Secc.LargeCouplingBankState

section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Frame
variable (U : Finset HashInput)
def QFrame (X : HashInput) (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (∀ row : Cell U, row.1 ≠ X → s'.rows row = s.rows row) ∧ s'.counters.calls = s.counters.calls + 1 ∧
    s'.counters.mass = s.counters.mass ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
def OutcomeLe {α : Type} (X : HashInput) (s : LargeResidual.State WCoord (Cell U))
    (g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal) : Prop :=
  (∀ v s', QFrame U X s s' → g (some v, s') ≤ B) ∧ ∀ s', s'.counters.mass = s.counters.mass → g (none, s') ≤ B
theorem OutcomeLe.map {α β : Type} {X : HashInput} {s : LargeResidual.State WCoord (Cell U)}
    {g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (f : α → β)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s (fun r => g (r.1.map f, r.2)) B :=
  ⟨fun v s' hs => h.1 (f v) s' hs, fun s' hs => h.2 s' hs⟩
end Frame
section Invariant
variable {U : Finset HashInput}
theorem BankInv.after {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hX : ¬(X ∈ U ∧ IsDigestRow X)) (hf : QFrame U X ws ws') : BankInv U ws' (st.after X) := by
  have hne : ∀ X' (hX' : X' ∈ U), IsDigestRow X' → X' ≠ X := fun X' hX' hd he => hX ⟨he ▸ hX', he ▸ hd⟩
  refine ⟨by rw [hf.2.1, h.calls]; rfl, by rw [hf.2.2.1, hf.2.1]; exact (h.mass).trans (Nat.le_succ _),
    (h.births).trans (Nat.le_succ _), fun m hm => by rw [hf.2.2.2 m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    have hs' : X' ∈ st.seen := by
      rcases List.mem_cons.mp hs with he | hm
      · exact absurd he (hne X' hX' hd)
      · exact hm
    exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)
end Invariant
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Step
variable {U : Finset HashInput}
theorem birth_pay (m q : Nat) (hm : m < q) (p : ENNReal) :
    p + (CaseC.theta + 1 / 64) / 2 ^ 128 + ((q - (m + 1) : Nat) : ENNReal) / 2 ^ 128 ≤
      p + ((q - m : Nat) : ENNReal) / 2 ^ 128 := by
  rw [add_assoc]
  apply add_le_add le_rfl
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  have hq : q - m = (q - (m + 1)) + 1 := by omega
  rw [hq, Nat.cast_add, Nat.cast_one, add_comm ((q - (m + 1) : Nat) : ENNReal)]
  exact add_le_add CaseC.theta_add_sixteenth_le_one le_rfl
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
end Step
end SigGolfCandidate.T3.Security.LargeCoupling
end
