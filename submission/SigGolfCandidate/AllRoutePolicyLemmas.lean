import SigGolfCandidate.Merge033
set_option debug.skipKernelTC false
namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.AllRoute
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem nextResidualAt_rewrite (index r : Nat) (lay : Layer) (low : Bool) (digits : List Nat) :
    nextResidualAt index r lay low digits =
      CanonicalPolicy.nextResidual (r-usedSave lay.val (route index lay).1) lay low digits := by
  simp only [nextResidualAt, routeCredit, CanonicalPolicy.nextResidual, Nat.sub_sub]
  rw [Nat.add_comm]

theorem nextResidualAt_le (index r : Nat) (lay : Layer) (low : Bool) (digits : List Nat) :
    nextResidualAt index r lay low digits ≤ CanonicalPolicy.nextResidual r lay low digits := by
  unfold nextResidualAt routeCredit CanonicalPolicy.nextResidual
  omega

theorem usedSave_one_le (leaf : Nat) : usedSave 1 leaf ≤ 2 := by
  have h := l1_bounds ⟨leaf%128, Nat.mod_lt _ (by decide)⟩
  simpa [usedSave, lowerSave, Nat.mod_mod] using h

theorem usedSave_two_le (leaf : Nat) : usedSave 2 leaf ≤ 1 := by
  unfold usedSave lowerSave
  split_ifs <;> omega

def saveClass (index : Nat) : Fin 6 :=
  ⟨2*usedSave 1 (route index 1).1 + usedSave 2 (route index 2).1, by
    have h1 := usedSave_one_le (route index 1).1
    have h2 := usedSave_two_le (route index 2).1
    omega⟩

def poolClass (index : Nat) : Fin 3 :=
  ⟨requiredCredit index-72, by have h := requiredCredit_bounds index; omega⟩

theorem saveClass_one (index : Nat) : (saveClass index).val/2 = usedSave 1 (route index 1).1 := by
  have h2 := usedSave_two_le (route index 2).1
  unfold saveClass
  dsimp only
  omega

theorem saveClass_two (index : Nat) : (saveClass index).val%2 = usedSave 2 (route index 2).1 := by
  have h2 := usedSave_two_le (route index 2).1
  unfold saveClass
  dsimp only
  omega

theorem poolClass_eq (index : Nat) : 72 + (poolClass index).val = requiredCredit index := by
  have h := requiredCredit_bounds index
  unfold poolClass
  dsimp only
  omega
#print axioms nextResidualAt_rewrite
#print axioms usedSave_one_le
#print axioms usedSave_two_le
#print axioms saveClass_one
#print axioms saveClass_two
#print axioms poolClass_eq
end SigGolfCandidate.Research.SharedForest
