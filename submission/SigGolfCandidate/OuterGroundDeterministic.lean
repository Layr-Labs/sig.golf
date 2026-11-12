import SigGolfCandidate.OuterGroundCore
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterGroundDeterministic
open OuterGroundCore SigGolfCandidate.T3 OracleComp
open SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Sampling

def scan (coord : Nat) (f : Nat → Digest) : Nat → Nat → Nat × Digest
  | 0,n => (n,f n)
  | fuel+1,n => if zeroOk coord (f n) then (n,f n) else scan coord f fuel (n+1)

theorem scan_range (coord : Nat) (f : Nat → Digest) (fuel n : Nat) :
    n≤(scan coord f fuel n).1 ∧ (scan coord f fuel n).1≤n+fuel := by
  induction fuel generalizing n with
  | zero => simp [scan]
  | succ fuel ih =>
    simp only [scan]
    split
    · simp
    · have h:=ih (n+1);omega

theorem scan_value (coord : Nat) (f : Nat → Digest) (fuel n : Nat) :
    (scan coord f fuel n).2=f (scan coord f fuel n).1 := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan]
    split
    · rfl
    · exact ih (n+1)

theorem scan_earlier (coord : Nat) (f : Nat → Digest) (fuel n k : Nat)
    (hlo : n≤k) (hhi : k<(scan coord f fuel n).1) : zeroOk coord (f k)=false := by
  induction fuel generalizing n with
  | zero => simp only [scan] at hhi;omega
  | succ fuel ih =>
    simp only [scan] at hhi
    split at hhi
    · omega
    · rename_i hn
      by_cases he : k=n
      · subst k;exact Bool.eq_false_iff.mpr hn
      · exact ih (n+1) (by omega) hhi

theorem scan_success (coord : Nat) (f : Nat → Digest) (fuel n : Nat)
    (h : ∃ k,n≤k ∧ k≤n+fuel ∧ zeroOk coord (f k)=true) :
    zeroOk coord (scan coord f fuel n).2=true := by
  induction fuel generalizing n with
  | zero =>
    obtain ⟨k,hlo,hhi,hk⟩:=h
    have he:k=n:=by omega
    simpa [scan,he] using hk
  | succ fuel ih =>
    simp only [scan]
    split
    · assumption
    · rename_i hn
      apply ih (n+1)
      obtain ⟨k,hlo,hhi,hk⟩:=h
      refine ⟨k,?_,by omega,hk⟩
      by_cases he:k=n
      · subst k;exact False.elim (hn hk)
      · omega

def response (answers : SigGolfCandidate.T3.Correctness.Answers) (coord index heap : Nat) (left right : Digest) (n : Nat) : Digest :=
  value coord heap (answers (.inl (.inr (trial coord index heap n left right))))

theorem eval_search (answers : SigGolfCandidate.T3.Correctness.Answers) (coord index heap : Nat) (left right : Digest) (fuel n : Nat) :
    evalWithAnswerFn answers (search coord index heap left right fuel n)=
      scan coord (response answers coord index heap left right) fuel n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    rw [search,evalWithAnswerFn_bind]
    change evalWithAnswerFn answers (if zeroOk coord (response answers coord index heap left right n) then
      pure (n,response answers coord index heap left right n) else
      search coord index heap left right fuel (n+1))=_
    split <;> simp_all [scan,response,evalWithAnswerFn_pure]

theorem eval_node_nonce_lt (answers : SigGolfCandidate.T3.Correctness.Answers) (coord index heap : Nat) (left right : Digest) :
    (evalWithAnswerFn answers (nodeAt coord index heap left right)).1<cap coord := by
  rw [nodeAt,eval_search]
  have h:=scan_range coord (response answers coord index heap left right) (cap coord-1) 0
  have hc : 0<cap coord := by unfold cap;positivity
  omega

#print axioms eval_search
#print axioms eval_node_nonce_lt
#print axioms scan_range
#print axioms scan_value
#print axioms scan_earlier
#print axioms scan_success
end OuterGroundDeterministic
