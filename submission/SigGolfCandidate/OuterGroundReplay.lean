import SigGolfCandidate.OuterRecover
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterGroundReplay
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open OuterGroundCore

theorem search_answer (answers : Answers) (coord index heap : Nat) (left right : Digest) : ∀fuel n,
    let r:=evalWithAnswerFn answers (search coord index heap left right fuel n)
    n≤r.1 ∧ r.1≤n+fuel ∧ evalWithAnswerFn answers (hashN coord index heap r.1 left right)=r.2 := by
  intro fuel
  induction fuel with
  | zero=>
    intro n
    simp only [search,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    exact ⟨le_rfl,by omega,trivial⟩
  | succ fuel ih=>
    intro n
    simp only [search,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    split_ifs with hz
    · simp only [evalWithAnswerFn_pure]
      exact ⟨le_rfl,by omega,trivial⟩
    · have h:=ih (n+1)
      exact ⟨by omega,by omega,h.2.2⟩

theorem node_answer (answers : Answers) (coord index heap : Nat) (left right : Digest) :
    let r:=evalWithAnswerFn answers (nodeAt coord index heap left right)
    r.1<cap coord ∧ evalWithAnswerFn answers (hashN coord index heap r.1 left right)=r.2 := by
  dsimp only [nodeAt]
  have h:=search_answer answers coord index heap left right (cap coord-1) 0
  have hc : 0<cap coord:=by unfold cap;positivity
  exact ⟨by omega,h.2.2⟩
#print axioms search_answer
#print axioms node_answer
end OuterGroundReplay
