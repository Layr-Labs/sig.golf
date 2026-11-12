import SigGolfCandidate.OuterCanonWct
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace OuterCanonBase
open SigGolfCandidate.T3
theorem ftsNodeAt_some (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hlevel : level < 6)
    (hc : c < 2 ^ (7 - level - 1)) :
    ∃ n : WctNodePos, ftsNodeAt index coord level c = some n ∧ n.1.index = index ∧ n.1.coord = coord ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold ftsNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
#print axioms ftsNodeAt_some
end OuterCanonBase
