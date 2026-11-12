import SigGolfCandidate.OuterVerifyBudget
import SigGolfCandidate.OuterPreparedFacts
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterCredit74
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest

theorem sum {index : Nat} (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hh : OuterSigning.policyHintsValid index hints digits lows=true)
    (hc : ∀lay : Layer,OuterSigning.hintFloor index hints lay≤CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])) :
    74≤((List.finRange 4).map fun lay=>CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])+
      if lay=0 then CanonicalPolicy.topPathSave (route index 0).1 else LocalRoute.ownSave index lay.val).sum := by
  simp only [OuterSigning.policyHintsValid,decide_eq_true_eq] at hh
  let c (lay : Layer):=CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])
  let r0:=OuterSigning.requiredCredit index
  let r1:=r0-c 0-LocalRoute.ownSave index 1
  let r2:=r1-c 1-LocalRoute.ownSave index 2
  let r3:=r2-c 2-LocalRoute.ownSave index 3
  have h0 : Policy75Safe23.threshold 0 r0≤c 0:=hc 0
  have h1:=hc 1
  have h2:=hc 2
  have h3:=hc 3
  rw [hh.2.2.1] at h1
  rw [hh.2.2.2.1] at h2
  rw [hh.2.2.2.2] at h3
  change Policy75Safe23.threshold 1 r1≤c 1 at h1
  change Policy75Safe23.threshold 2 r2≤c 2 at h2
  change Policy75Safe23.threshold 3 r3≤c 3 at h3
  have hp:=OuterSigning.requiredCredit_bounds index
  have hm:=Nat.le_max_right 18 (r0-57)
  rw [Policy75Safe23.threshold_top] at h0
  have hr1 : r1<58:=by dsimp only [r1];omega
  have hf1:=(Policy75Safe23.lower_one_progress ⟨r1,hr1⟩).2
  simp only [Fin.val_mk] at hf1
  have hr2 : r2<42:=by dsimp only [r2];omega
  have hf2:=(Policy75Safe23.lower_two_progress ⟨r2,hr2⟩).2
  simp only [Fin.val_mk] at hf2
  have hr3 : r3≤23:=by dsimp only [r3];omega
  rw [Policy75Safe23.lower_three_progress r3 (by omega)] at h3
  have hf3:=Policy75Safe23.lowerThreeFloor_ge r3
  have hs : 74≤r0+CanonicalPolicy.topPathSave (route index 0).1 := by
    dsimp only [r0,OuterSigning.requiredCredit,OuterSigning.rootPool]
    omega
  change 74≤(c 0+CanonicalPolicy.topPathSave (route index 0).1)+
    ((c 1+LocalRoute.ownSave index 1)+((c 2+LocalRoute.ownSave index 2)+((c 3+LocalRoute.ownSave index 3)+0)))
  dsimp only [r3,r2,r1] at *
  omega

theorem clip (credits : Layer→Nat) (h : 74≤((List.finRange 4).map credits).sum) :
    OuterVerifyBudget.CreditFloors74 (fun lay=>min 74 (credits lay)) := by
  constructor
  · intro lay;exact (Nat.min_le_left _ _).trans (by decide)
  · change 74≤credits 0+(credits 1+(credits 2+(credits 3+0))) at h
    change 74≤ min 74 (credits 0)+(min 74 (credits 1)+(min 74 (credits 2)+(min 74 (credits 3)+0)))
    omega
theorem recovered (answers : SigGolfCandidate.T3.Correctness.Answers)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (index : Nat) (other : Digest)
    (msg : LayerMsg) (result : RecoveredLayers)
    (he : evalWithAnswerFn answers (recoverHintedLayers sig index other 4 msg)=some result)
    (hh : OuterSigning.policyHintsValid index sig.policyHints result.digits result.lows=true) :
    OuterVerifyBudget.CreditFloors74 (fun lay=>min 74
      (CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val [])+
        if lay=0 then CanonicalPolicy.topPathSave (route index 0).1 else LocalRoute.ownSave index lay.val)) := by
  apply clip
  apply sum _ _ _ hh
  intro lay
  have hc:=(recoverHintedLayers_credit answers sig index other 4 le_rfl msg result he).2.2 lay lay.isLt
  have heq : OuterSigning.hintFloor index sig.policyHints lay=hintFloor index sig.policyHints lay := by
    unfold OuterSigning.hintFloor hintFloor
    split
    · rw [OuterSigning.root_floor,OuterPreparedFacts.old_root_floor]
    · rfl
  rw [heq]
  exact hc
#print axioms recovered
#print axioms sum
#print axioms clip
end OuterCredit74
