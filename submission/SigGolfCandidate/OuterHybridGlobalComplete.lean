import SigGolfCandidate.OuterHybridCross
import SigGolfCandidate.OuterHybridFailureNumerics
import SigGolfCandidate.OuterGlobalFresh
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridGlobalComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open ClaudeWCT.W9.T3.TopMoment (Ev Ev_bind Ev_pure Ev_const_le)
open OuterHybridForestComplete OuterForestBudget

def checkStep (acc : Bool) (index : Nat) : M Bool := do
  let ok←forestCheck index
  pure (acc && ok)
def check : M Bool := ftsIndices.foldlM checkStep true

theorem E_checkFold (secret : BitVec 256) :
    ∀ (L : List Nat) (acc : Bool) (cache : RCache), L.Nodup →
      (∀ index ∈ L, index < 2 ^ 31 ∧ FreshF index (AllAbove 0) cache) →
      Ev secret (L.foldlM checkStep acc) cache (fun r => if r.1 then 0 else 1) ≤
        (if acc then 0 else 1) + L.length * forestFailure := by
  intro L
  induction L with
  | nil =>
      intro acc cache _ _
      simp only [List.foldlM_nil, Ev_pure, List.length_nil, Nat.cast_zero, zero_mul, add_zero]
      exact le_rfl
  | cons index L ih =>
      intro acc cache hnd hL
      obtain ⟨hidx, hf⟩ := hL index (List.mem_cons_self ..)
      rw [List.foldlM_cons]
      unfold checkStep
      simp only [bind_assoc, pure_bind]
      rw [Ev_bind]
      have hrest : ∀ r ∈ support (roRun secret (forestCheck index) cache),
          Ev secret (L.foldlM checkStep (acc && r.1)) r.2 (fun r => if r.1 then 0 else 1) ≤
          ((if acc then 0 else 1) + L.length * forestFailure) + (if r.1 then 0 else 1) := by
        intro r hr
        refine (ih _ r.2 (List.nodup_cons.mp hnd).2 fun j hj => ?_).trans ?_
        · obtain ⟨hj31, hfj⟩ := hL j (List.mem_cons_of_mem _ hj)
          have hne : index ≠ j := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hj)
          exact ⟨hj31, freshF_preserved secret (OuterHybridCross.xF_forestCheck hidx hj31 hne) cache hfj r hr⟩
        · rcases r with ⟨b, c⟩
          cases acc <;> cases b <;> simp [add_comm]
      refine (expectedValue_mono_of_support hrest).trans ?_
      have hadd := expectedValue_add (roRun secret (forestCheck index) cache)
        (fun _ => (if acc then 0 else 1) + L.length * forestFailure)
        (fun r => if r.1 then (0 : ℝ≥0∞) else 1)
      refine (le_of_eq hadd).trans ?_
      have h1 := Ev_const_le secret (forestCheck index) cache ((if acc then 0 else 1) + L.length * forestFailure)
      have h2 := OuterHybridForestComplete.E_forestCheck secret index hidx cache hf
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring


theorem Ev_check_false (secret : BitVec 256) (cache : RCache) (hc : OuterGlobalFresh.AllFFresh cache) :
    Ev secret check cache (fun r=>if r.1 then 0 else 1)≤ENNReal.ofReal (1/(2:ℝ)^146) := by
  unfold check
  refine (E_checkFold secret _ true cache ftsIndices_nodup (fun index hi=>?_)).trans ?_
  · have hidx:=mem_ftsIndices.mp hi
    exact ⟨hidx,OuterGlobalFresh.freshF_of_all hidx hc⟩
  · rw [ftsIndices_length]
    simpa using OuterHybridFailureNumerics.global_sum_le

#print axioms Ev_check_false
end OuterHybridGlobalComplete
