import SigGolfCandidate.OuterSigning
import SigGolfCandidate.Merge092
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPolicyCondition
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research
def policyCondition (index : Nat) (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool) : Prop :=
  let r1:=(OuterSigning.requiredCredit index)-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-SharedForest.LocalRoute.ownSave index 1
  let r2:=r1-CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])-SharedForest.LocalRoute.ownSave index 2
  let r3:=r2-CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])-SharedForest.LocalRoute.ownSave index 3
  r1<58 ∧ r2<42 ∧ r3<24 ∧
    hints.toNat/576=ClaudeWCT.WCT9.Policy75Safe23.threshold 1 r1 ∧
    hints.toNat/24%24=ClaudeWCT.WCT9.Policy75Safe23.threshold 2 r2 ∧ hints.toNat%24=ClaudeWCT.WCT9.Policy75Safe23.lowerThreeFloor r3

theorem policyCondition_iff (index : Nat) (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hh : hints.toNat<12288) (hlen : digits.length=4)
    (hc0 : ClaudeWCT.WCT9.Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)≤CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (hc1 : OuterSigning.hintFloor index hints 1≤CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (hc2 : OuterSigning.hintFloor index hints 2≤CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])) :
    policyCondition index hints digits lows ↔ OuterSigning.policyHintsValid index hints digits lows=true := by
  rw [ClaudeWCT.WCT9.Policy75Safe23.threshold_top] at hc0
  have h1 : OuterSigning.hintFloor index hints 1=hints.toNat/576%24 := by
    simp only [OuterSigning.hintFloor,show (1:Layer)≠0 by decide,ite_false]; rfl
  have h2 : OuterSigning.hintFloor index hints 2=hints.toNat/24%24 := by
    simp only [OuterSigning.hintFloor,show (2:Layer)≠0 by decide,ite_false]; rfl
  have h3 : OuterSigning.hintFloor index hints 3=hints.toNat%24 := by
    simp only [OuterSigning.hintFloor,show (3:Layer)≠0 by decide,ite_false]
    show hints.toNat/1%24=_
    rw [Nat.div_one]
  rw [h1] at hc1
  rw [h2] at hc2
  simp only [OuterSigning.policyHintsValid,decide_eq_true_eq,SharedForest.routeResidual,CanonicalPolicy.nextResidual,Fin.val_zero,Fin.val_one,show (2:SigGolfCandidate.T3.Layer).val=2 by rfl,
    ClaudeWCT.WCT9.Policy75Safe23.threshold_top,hlen,true_and,and_true,h1,h2,h3]
  norm_num only at *
  unfold policyCondition
  constructor
  · rintro ⟨hR1,hR2,hR3,he1,he2,he3⟩
    have hlt := ClaudeWCT.WCT9.Policy75Safe23.lower_one_floor_lt ⟨_,hR1⟩
    simp only [Fin.val_mk] at hlt
    refine ⟨by omega,by omega,he2,?_⟩
    rw [ClaudeWCT.WCT9.Policy75Safe23.lower_three_progress _ hR3]
    exact he3
  · rintro ⟨hH,he1,he2,he3⟩
    have hr1 : (OuterSigning.requiredCredit index)-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-SharedForest.LocalRoute.ownSave index 1<58 := by omega
    have ht1 := (ClaudeWCT.WCT9.Policy75Safe23.lower_one_progress ⟨_,hr1⟩).2
    simp only [Fin.val_mk] at ht1
    have hr2 : (OuterSigning.requiredCredit index)-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-SharedForest.LocalRoute.ownSave index 1-
        CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])-SharedForest.LocalRoute.ownSave index 2<42 := by
      rw [←he1] at ht1
      omega
    have ht2 := (ClaudeWCT.WCT9.Policy75Safe23.lower_two_progress ⟨_,hr2⟩).2
    simp only [Fin.val_mk] at ht2
    have hr3 : (OuterSigning.requiredCredit index)-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-SharedForest.LocalRoute.ownSave index 1-
        CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])-SharedForest.LocalRoute.ownSave index 2-
        CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])-SharedForest.LocalRoute.ownSave index 3<24 := by
      rw [←he2] at ht2
      omega
    refine ⟨hr1,hr2,hr3,by omega,he2,?_⟩
    rw [ClaudeWCT.WCT9.Policy75Safe23.lower_three_progress _ hr3] at he3
    exact he3

#print axioms policyCondition_iff
end OuterPolicyCondition
