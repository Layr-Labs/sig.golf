import SigGolfCandidate.OuterVerifyBudget
import SigGolfCandidate.OuterAdmissible
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifyRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.T3M.Final.Paired (DigestCapOk)
open W9Fin.V7.Canonical.Runtime
open OuterImageValidity

theorem initial_eq (m : Message) (pk : PublicKey) (w : Bytes 21756) :
    initialState sub .verify (m,pk,w)=initialState SigGolfCandidate.T3M.submission .verify (m,pk,w) := by
  unfold initialState
  rw [if_pos OuterAdmissible.verify,if_pos SigGolfCandidate.T3M.submission_verify_valid]
  dsimp only [sub,OuterRuntime.runtimeSub,OuterImageValidity.images,SigGolfCandidate.T3M.submission,inputBuffers,List.foldl_cons,List.foldl_nil]

theorem fixed74 : OuterVerifyBudget.CreditFloors74 (fun _=>20) := by
  constructor
  · intro lay;norm_num
  · decide

def Inputs : Prop:=∀ (floors : SigGolfCandidate.T3.Layer→Nat),OuterVerifyBudget.CreditFloors74 floors →
  ∀(m : Message)(pk : PublicKey)(w : Bytes 21756)(s : MachineState),
  initialState SigGolfCandidate.T3M.submission .verify (m,pk,w)=some s →
  GoodQP (fun hash=>HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w) hash ∧ DigestCapOk hash m w)
    s 10083 15784 True 6873 (ccM (ClaudeWCT.W9.T3M.Paired.verifyP m pk w) Kb)

theorem inputs : Inputs := by
  intro floors hcredit message pk witness state hstate
  exact OuterVerifyBudget.installed_good floors hcredit message pk witness state hstate

theorem refines : ∀ (m : Message) (pk : PublicKey) (w : Bytes 21756),
  (fun r=>(r.value,r.hashCalls)) <$> sub.run .verify (m,pk,w)=
    (fun p=>(if p.1 then some () else none,p.2)) <$> countCalls (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP m pk w)) := by
  intro m pk w
  obtain ⟨s,hs⟩ := W9Fin.V7.init_exists m pk w
  have hs' := (initial_eq m pk w).trans hs
  have hg := (inputs _ fixed74 m pk w s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT; norm_num)).1
  rw [ccM_Kb] at hg
  rw [run_eq _ .verify _ s hs',Functor.map_map]
  change _ = (fun p => (if p.1 then some () else none,p.2)) <$>
    countCalls (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP m pk w))
  rw [←hg,Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT Verify.image s) ?_
  funext e
  simp only [toRunResult,obs]
  by_cases h : e.exit=.success
  · simp only [h,decide_true,if_true];rfl
  · simp only [h,decide_false,if_false,Bool.false_eq_true];rfl

theorem terminates : ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 21756),
  (sub.runWith hash .verify (m,pk,w)).finished=true ∧ (sub.runWith hash .verify (m,pk,w)).cycles<CYCLE_LIMIT := by
  intro hash m pk w
  obtain ⟨s,hs⟩ := W9Fin.V7.init_exists m pk w
  have hs' := (initial_eq m pk w).trans hs
  have hg := (inputs _ fixed74 m pk w s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT; norm_num)).2 hash
  rw [runWith_eq _ hash .verify _ s hs']
  simp only [toRunResult,sub,OuterRuntime.runtimeSub,OuterImageValidity.images]
  refine ⟨?_,lt_of_le_of_lt hg.2.1 (by unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1

theorem accept_cycles : ∀ (floors : SigGolfCandidate.T3.Layer→Nat), OuterVerifyBudget.CreditFloors74 floors →
  ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 21756),
  HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w) hash → DigestCapOk hash m w →
  (sub.runWith hash .verify (m,pk,w)).value.isSome=true → (sub.runWith hash .verify (m,pk,w)).cycles≤6873 := by
  intro floors hcredit hash m pk w hok hcap h
  obtain ⟨s,hs⟩ := W9Fin.V7.init_exists m pk w
  have hs' := (initial_eq m pk w).trans hs
  have hg := (inputs floors hcredit m pk w s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT; norm_num)).2 hash
  rw [runWith_eq _ hash .verify _ s hs'] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT (sub.image .verify) s)).exit=.success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  have hsuc' : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Verify.image s)).exit=.success:=by
    simpa only [sub,OuterRuntime.runtimeSub,OuterImageValidity.images] using hsucc
  simpa only [sub,OuterRuntime.runtimeSub,OuterImageValidity.images] using (hg.2.2 hsuc' ⟨hok,hcap⟩).2


#print axioms initial_eq
#print axioms inputs
#print axioms refines
#print axioms terminates
#print axioms accept_cycles
end OuterVerifyRun
