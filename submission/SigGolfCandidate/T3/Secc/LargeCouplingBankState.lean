import SigGolfCandidate.T3.Secc.LargeCouplingBankLazy
import SigGolfCandidate.T3.Secc.SeccSufRoute

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure BankInv (U : Finset HashInput) (ws : LargeResidual.State WCoord (Cell U)) (st : RouterState) : Prop where
  calls : ws.counters.calls = st.calls
  mass : ws.counters.mass ≤ ws.counters.calls
  births : st.births.length ≤ st.calls
  nonce : ∀ m, st.memo.lookup m = none → ws.candidates (.inr m) = Finset.univ
  fresh : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∉ st.seen → X ∉ st.trials → ws.rows ⟨X, hX⟩ = none
  seenRows : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∈ st.seen → X ∉ st.trials →
    ∃ y, st.cache X = some y ∧ ws.rows ⟨X, hX⟩ = some y
  bornSeen : ∀ p ∈ st.births, p.1 ∈ st.seen
  trials : ∀ X ∈ st.trials, ∃ rho m c, X = pad64 (digestInput rho m c) ∧ (st.memo.lookup m).isSome
theorem digestTrial_inj {rho rho' : Digest} {m m' : Message} {c c' : Fin (2 ^ 32)}
    (h : Sampling.digestTrial rho m c.val = Sampling.digestTrial rho' m' c'.val) : m = m' ∧ rho = rho' ∧ c = c' := by
  have h' : pad64 (digestInput rho m (BitVec.ofNat 32 c.val)) = pad64 (digestInput rho' m' (BitVec.ofNat 32 c'.val)) := h
  obtain ⟨h1, h2, h3⟩ := BPB.digestInput_injective h'
  refine ⟨h3, h1, Fin.ext ?_⟩
  have := congrArg BitVec.toNat h2
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt c'.isLt] using this
theorem tsum_trial_indicator_le (X : HashInput) (a : ENNReal) :
    (∑' m : Message, ∑' p : Digest × Fin (2 ^ 32),
      if Sampling.digestTrial p.1 m p.2.val = X then a else 0) ≤ a := by
  by_cases hex : ∃ (m : Message) (p : Digest × Fin (2 ^ 32)), Sampling.digestTrial p.1 m p.2.val = X
  · obtain ⟨m0, p0, h0⟩ := hex
    have hinner : ∀ m, (∑' p : Digest × Fin (2 ^ 32), if Sampling.digestTrial p.1 m p.2.val = X then a else 0) =
        if m = m0 then a else 0 := by
      intro m
      by_cases hm : m = m0
      · subst hm
        rw [if_pos rfl, tsum_eq_single p0]
        · rw [if_pos h0]
        · intro p hp
          rw [if_neg]
          intro hp'
          obtain ⟨-, h1, h2⟩ := digestTrial_inj (hp'.trans h0.symm)
          exact hp (Prod.ext h1 h2)
      · rw [if_neg hm]
        apply ENNReal.tsum_eq_zero.mpr
        intro p
        rw [if_neg]
        intro hp'
        exact hm (digestTrial_inj (hp'.trans h0.symm)).1
    simp_rw [hinner]
    rw [tsum_ite_eq]
  · push Not at hex
    simp only [hex, if_false, tsum_zero]
    exact zero_le
theorem expectedValue_uniform_reply (f : LargeResidual.HashOutput → ENNReal) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput) f =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun y => f y) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro y
  have h1 : Pr[= y | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := probOutput_uniformSample _ y
  have h2 : Pr[= y | (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := by
    rw [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  rw [h1, h2]
end SigGolfCandidate.T3.Security.LargeCoupling
