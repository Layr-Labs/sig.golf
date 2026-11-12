import SigGolfCandidate.OuterGroundDeterministic
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterGroundDeterministic
open SigGolfCandidate.T3 OuterGroundCore

theorem scan_selected (coord : Nat) (f : Nat → Digest) (fuel start target : Nat)
    (hlo : start ≤ target) (hhi : target ≤ start+fuel)
    (hearly : ∀ j, start ≤ j → j<target → zeroOk coord (f j)=false)
    (hlast : zeroOk coord (f target)=true ∨ target=start+fuel) :
    scan coord f fuel start=(target,f target)  :=  by
  induction fuel generalizing start with
  | zero=>
    have he : target=start := by omega
    subst target
    rfl
  | succ fuel ih=>
    unfold scan
    by_cases h : zeroOk coord (f start)=true
    · rw [if_pos h]
      have he : target=start := by
        by_contra hn
        have hh := hearly start le_rfl (by omega)
        rw [h] at hh
        cases hh
      subst target
      rfl
    · rw [if_neg h]
      have hlt : start<target := by
        by_contra hn
        have he : target=start := by omega
        subst target
        rcases hlast with ht|ht
        · exact h ht
        · omega
      exact ih (start+1) (by omega) (by omega) (fun j hj ht=>hearly j (by omega) ht)
        (by rcases hlast with ht|ht;exact Or.inl ht;exact Or.inr (by omega))
#print axioms scan_selected
end OuterGroundDeterministic
