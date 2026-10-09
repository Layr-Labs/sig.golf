import SigGolfCandidate.T3.Secc.LargeCouplingTrace

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem queryEvent_answer_eq {state : LazyPrivate.State} {input : T3.Spec.Domain} {a b : T3.Spec.Range input}
    (h : (⟨state, input, a⟩ : FirstHit.QueryEvent) = ⟨state, input, b⟩) : a = b := by
  simp only [FirstHit.QueryEvent.mk.injEq, heq_eq_eq, true_and] at h
  exact h
theorem record_prefix_unique {α : Type} (program : M α) (state : LazyPrivate.State)
    (r1 r2 : FirstHit.Recorded α) (h1 : r1 ∈ support (FirstHit.record program state))
    (h2 : r2 ∈ support (FirstHit.record program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : r1.events ++ rest1 = r2.events ++ rest2) : r1 = r2 := by
  induction program using OracleComp.inductionOn generalizing state r1 r2 rest1 rest2 with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at h1 h2
      obtain ⟨m1, hm1, h1⟩ := h1
      obtain ⟨m2, hm2, h2⟩ := h2
      rw [support_map] at h1 h2
      obtain ⟨l1, hl1, rfl⟩ := h1
      obtain ⟨l2, hl2, rfl⟩ := h2
      simp only [List.cons_append, List.cons.injEq] at heq
      have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
      have hs1 := FirstHit.query_advance state input m1 hm1
      have hs2 := FirstHit.query_advance state input m2 hm2
      have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
      subst hm
      have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
      rw [hl]
end SigGolfCandidate.T3.Security.LargeCoupling
