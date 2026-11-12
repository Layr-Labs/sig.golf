import SigGolfCandidate.Merge009
set_option debug.skipKernelTC false
namespace SigGolfCandidate.AllRoute
 def l1Table : List Nat := [0, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 0]
 def lowerSave (lay leaf : Nat) : Nat :=
   if lay = 1 then l1Table.getD (leaf % 128) 0
   else if lay = 2 ∨ lay = 3 then if leaf % 4 = 1 ∨ leaf % 4 = 2 then 1 else 0 else 0
 theorem l1_bounds : ∀ i : Fin 128, lowerSave 1 i.val ≤ 2 := by decide +kernel
 theorem l1_dist : (List.range 128).countP (fun i => lowerSave 1 i == 0) = 2 ∧
   (List.range 128).countP (fun i => lowerSave 1 i == 1) = 66 ∧
   (List.range 128).countP (fun i => lowerSave 1 i == 2) = 60 := by decide +kernel
 def l1Masks : List Nat := [0, 1, 2, 2, 4, 5, 5, 4, 8, 9, 9, 8, 8, 9, 9, 8, 16, 17, 17, 16, 4, 5, 5, 4, 4, 5, 5, 4, 16, 17, 17, 16, 32, 33, 33, 32, 4, 5, 5, 4, 8, 9, 9, 8, 8, 9, 9, 8, 8, 9, 9, 8, 4, 5, 5, 4, 4, 5, 5, 4, 2, 33, 33, 32, 32, 33, 33, 32, 4, 5, 5, 4, 8, 9, 9, 8, 8, 9, 9, 8, 16, 17, 17, 16, 4, 5, 5, 4, 4, 5, 5, 4, 16, 17, 17, 16, 16, 17, 17, 16, 4, 5, 5, 4, 8, 9, 9, 8, 8, 9, 9, 8, 8, 9, 9, 8, 4, 5, 5, 4, 4, 5, 5, 4, 2, 2, 1, 0]
 def lowerPairSave (lay leaf k : Nat) : Nat :=
   if lay = 1 then (l1Masks.getD (leaf % 128) 0 / 2^k) % 2
   else if (lay = 2 ∨ lay = 3) ∧ k = 0 then (if leaf % 4 = 1 ∨ leaf % 4 = 2 then 1 else 0) else 0
 theorem lowerPairSave_zero (lay k : Nat) : lowerPairSave lay 0 k = 0 := by
   simp [lowerPairSave, l1Masks]
 theorem lowerPairSave_sum : ∀ lay : Fin 4, ∀ leaf : Fin 128,
    (List.range (if lay.val = 1 then 6 else 5)).foldl (fun a k => a + lowerPairSave lay.val leaf.val k) 0 = lowerSave lay.val leaf.val := by decide +kernel
def usedSave (lay leaf : Nat) : Nat := if lay = 1 ∨ lay = 2 then lowerSave lay leaf else 0
@[simp] theorem usedSave_top (leaf : Nat) : usedSave 0 leaf = 0 := by simp [usedSave]
@[simp] theorem usedSave_three (leaf : Nat) : usedSave 3 leaf = 0 := by simp [usedSave]
theorem usedSave_le_two (lay leaf : Nat) : usedSave lay leaf ≤ 2 := by
  unfold usedSave
  split_ifs with h
  · rcases h with h | h
    · subst lay
      have hb := l1_bounds ⟨leaf%128, Nat.mod_lt _ (by decide)⟩
      simpa [lowerSave, Nat.mod_mod] using hb
    · subst lay
      unfold lowerSave
      split_ifs <;> omega
  · omega
end SigGolfCandidate.AllRoute
