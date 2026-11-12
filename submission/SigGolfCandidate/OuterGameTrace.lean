import SigGolfCandidate.OuterGameWith
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
namespace OuterGameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Forgery : Type}
namespace Counted
open SigGolfCandidate.T3.Security.CountedPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (OuterGameWith.idealGame checker adversary) (0,∅,∅)
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | OuterGameWith.idealLazyExperiment checker adversary] := by
  simp only [experiment,run,OuterGameWith.idealLazyExperiment,probEvent_map,Function.comp_def,Nat.zero_add]
theorem real_to_counted_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact OuterGameWith.real_to_ideal_lazy checker adversary q hq
end Counted
namespace Monitored
open SigGolfCandidate.T3.Security.MonitoredPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (OuterGameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    Prod.map id State.source <$> experiment checker adversary=Counted.experiment checker adversary :=
  run_erasure (OuterGameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | Counted.experiment checker adversary] := by
  rw [← experiment_erasure checker adversary,probEvent_map]
  rfl
theorem real_to_monitored_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact Counted.real_to_counted_ideal checker adversary q hq
end Monitored
namespace Recorded
open SigGolfCandidate.T3.Security.QueryRecorded
abbrev TraceResult := Bool × (SigGolfCandidate.T3.Security.MonitoredPrivate.History × State)
/-- The paired source is recorded directly. Its bank exposes accepted outputs,
so no auxiliary proposal trace is needed by this game. -/
noncomputable def tracedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (_budget : Nat) (_hbudget : _budget≤2^127) : PMF TraceResult :=
  (fun r=> (r.1,[],r.2)) <$> (liftM (run (OuterGameWith.idealGame checker adversary) initial) : PMF _)

theorem traced_source_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Prod.map id Prod.snd <$> tracedExperiment checker adversary q hq =
      (liftM (run (OuterGameWith.idealGame checker adversary) initial) : PMF _) := by
  unfold tracedExperiment
  simp only [Functor.map_map,Prod.map,id_eq]
  exact id_map _

theorem traced_base_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    (fun r : TraceResult=>(r.1,r.2.2.base)) <$> tracedExperiment checker adversary q hq =
      (liftM (Monitored.experiment checker adversary) : PMF _) := by
  unfold tracedExperiment
  simp only [Functor.map_map]
  exact lift_run_erasure (OuterGameWith.idealGame checker adversary) initial

theorem traced_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.1=true ∧ r.2.2.base.source.1≤q|tracedExperiment checker adversary q hq]=
    Pr[fun r=>r.1=true ∧ r.2.source.1≤q|Monitored.experiment checker adversary] := by
  have h:=congrArg (fun law : PMF (Bool×SigGolfCandidate.T3.Security.MonitoredPrivate.State)=>
    Pr[fun r=>r.1=true ∧ r.2.source.1≤q|law]) (traced_base_erasure checker adversary q hq)
  simpa only [probEvent_map,Function.comp_def,MonitoredPrivate.event_lift] using h

theorem traced_exception_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.2.2.base.source.1≤q ∧ r.2.2.base.exceptional=true|
      tracedExperiment checker adversary q hq] ≤ q/(2:ENNReal)^146 := by
  have he:=congrArg (fun law : PMF (Bool×SigGolfCandidate.T3.Security.MonitoredPrivate.State)=>
    Pr[fun r=>r.2.source.1≤q ∧ r.2.exceptional=true|law]) (traced_base_erasure checker adversary q hq)
  simp only [probEvent_map,Function.comp_def,MonitoredPrivate.event_lift] at he
  rw [he]
  exact MonitoredPrivate.gate6_run_empty_linear_charge (OuterGameWith.idealGame checker adversary) q 146 hq (by decide)

theorem split_clean (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.1=true ∧ r.2.2.base.source.1≤q|tracedExperiment checker adversary q hq]≤
      Pr[CleanWin q|tracedExperiment checker adversary q hq]+
      Pr[fun r=>r.2.2.base.source.1≤q ∧ r.2.2.base.exceptional=true|
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr:r∈(tracedExperiment checker adversary q hq).support
  · have hh:r.2.1=[] := by
      unfold tracedExperiment at hr
      rw [PMF.monad_map_eq_map,PMF.support_map] at hr
      obtain ⟨v,hv,he⟩:=hr
      exact congrArg (fun x:TraceResult=>x.2.1) he.symm
    by_cases hw:r.1=true ∧ r.2.2.base.source.1≤q
    · cases hb:r.2.2.base.exceptional <;> simp [CleanWin,hw,hw.1,hw.2,hb,hh]
    · simp only [hw,if_false,zero_le]
  · have hz:(tracedExperiment checker adversary q hq) r=0 := by
      simpa only [PMF.mem_support_iff,not_not] using hr
    simp only [PMF.probOutput_eq_apply,hz,ite_self,add_zero,le_refl]

theorem real_to_clean_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.1=true ∧ r.2≤q|realExperiment checker adversary]≤
      Pr[CleanWin q|tracedExperiment checker adversary q hq]+
      q/(2:ENNReal)^146+((2:ENNReal)^152)⁻¹+q/((2^256:Nat):ENNReal) := by
  have h:=Monitored.real_to_monitored_ideal checker adversary q (lt_of_le_of_lt hq (by decide))
  rw [←traced_event checker adversary q hq] at h
  exact h.trans (add_le_add (add_le_add
    ((split_clean checker adversary q hq).trans
      (add_le_add le_rfl (traced_exception_bound checker adversary q hq))) le_rfl) le_rfl)

theorem traced_record_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    recordedTrace <$> tracedExperiment checker adversary budget hbudget=
      (liftM (FirstHit.record (OuterGameWith.idealGame checker adversary) (∅,∅)) : PMF _) := by
  have hr : recorded <$> run (OuterGameWith.idealGame checker adversary) initial=
      FirstHit.record (OuterGameWith.idealGame checker adversary) (∅,∅) := by
    rw [run_recorded]
    have hp : prepend ([] : List FirstHit.QueryEvent)=(id : FirstHit.Recorded Bool → FirstHit.Recorded Bool) := by
      funext result
      rfl
    change prepend [] <$> FirstHit.record (OuterGameWith.idealGame checker adversary) (∅,∅)=_
    rw [hp,id_map]
  calc
    _ = recorded <$> (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget) := by
      rw [Functor.map_map]
      rfl
    _ = recorded <$> (liftM (run (OuterGameWith.idealGame checker adversary) initial) : PMF _) := by
      rw [traced_source_erasure]
    _ = (liftM (recorded <$> run (OuterGameWith.idealGame checker adversary) initial) : PMF _) := (liftM_map _ _).symm
    _ = _ := by rw [hr]
theorem traced_cost_coherent (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment checker adversary budget hbudget).support) : CostCoherent result.2.2 := by
  have hp : (result.1,result.2.2) ∈
      (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map,PMF.support_map]
    exact ⟨result,hr,rfl⟩
  rw [traced_source_erasure] at hp
  rw [MonitoredPrivate.pmf_support] at hp
  exact run_cost_coherent (OuterGameWith.idealGame checker adversary) initial initial_cost
    (result.1,result.2.2) hp
theorem known_public_hit_bound (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
      tracedExperiment checker adversary q hq] ≤ q/(2 : ENNReal)^128 := by
  have h := FirstHit.recorded_known_public_hit_bound reference (OuterGameWith.idealGame checker adversary) (∅,∅) q
  have he := congrArg (fun law => Pr[fun result : FirstHit.Recorded Bool =>
      (result.events.map (fun event => FullGame.queryCharge event.input)).sum≤q ∧
      FirstHit.KnownPublicHit reference result | law]) (traced_record_erasure checker adversary q hq)
  rw [probEvent_map,Function.comp_def,MonitoredPrivate.event_lift] at he
  apply le_trans _ (he.le.trans h)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (tracedExperiment checker adversary q hq).support
  · have hc := traced_cost_coherent checker adversary q hq result hr
    simp only [Function.comp_def,recordedTrace,recorded]
    rw [show result.2.2.base.source.1=
      (result.2.2.events.map (fun event => FullGame.queryCharge event.input)).sum from hc]
  · have hz : (tracedExperiment checker adversary q hq) result=0 := by
      by_contra hn
      exact hr (by simpa only [PMF.mem_support_iff] using hn)
    simp only [PMF.probOutput_eq_apply,hz,ite_self,le_refl]

end Recorded

end OuterGameWith
