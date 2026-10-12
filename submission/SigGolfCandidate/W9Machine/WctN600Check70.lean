import SigGolfCandidate.W9Machine.WctN600Evidence

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine560 : ChainRoutine := ⟨663, [4, 2, 0, 1, 0, 0], [⟨231424, [0x28040513, 0x2b040613, 0xa7ff8c93, 0x1953823, 0x73], .head 640 688 0 0⟩, ⟨231429, [0x7508a3, 0x73], .rung 1 none⟩, ⟨231431, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231433, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231435, [0x24040513, 0x27040613, 0xc83f8c93, 0x1953823, 0x73], .head 576 624 1 2⟩, ⟨231440, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231442, [0x27043183, 0x27843703, 0x2e343023, 0x2ee43423], .copy 576 736⟩, ⟨231446, [0x1c040513, 0x1f040613, 0xd8bf8c93, 0x1953823, 0x73], .head 448 496 3 3⟩, ⟨231451, [0x1f043183, 0x1f843703, 0x30343023, 0x30e43423], .copy 448 768⟩, ⟨231455, [0x2df43023, 0x2c043423, 0x2b040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine561 : ChainRoutine := ⟨664, [4, 2, 1, 0, 0, 0], [⟨231488, [0x28040513, 0x2b040613, 0xa7ff8c93, 0x1953823, 0x73], .head 640 688 0 0⟩, ⟨231493, [0x7508a3, 0x73], .rung 1 none⟩, ⟨231495, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231497, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231499, [0x24040513, 0x27040613, 0xc83f8c93, 0x1953823, 0x73], .head 576 624 1 2⟩, ⟨231504, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨231507, [0x20040513, 0x23040613, 0xd87f8c93, 0x1953823, 0x73], .head 512 560 2 3⟩, ⟨231512, [0x23043183, 0x23843703, 0x2e343823, 0x2ee43c23], .copy 512 752⟩, ⟨231516, [0x2df43023, 0x2c043423, 0x2b040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine562 : ChainRoutine := ⟨665, [4, 3, 0, 0, 0, 0], [⟨231552, [0x28040513, 0x2b040613, 0xa7ff8c93, 0x1953823, 0x73], .head 640 688 0 0⟩, ⟨231557, [0x7508a3, 0x73], .rung 1 none⟩, ⟨231559, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231561, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231563, [0x24040513, 0x27040613, 0xb83f8c93, 0x1953823, 0x73], .head 576 624 1 1⟩, ⟨231568, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231570, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231572, [0x27043183, 0x27843703, 0x2e343023, 0x2ee43423], .copy 576 736⟩, ⟨231576, [0x2df43023, 0x2c043423, 0x2b040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch70 : List (ChainRoutine × Nat) := [(routine560, 85), (routine561, 82), (routine562, 78)]
theorem batch70_checked : (batch70.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready560 : Chain.RoutineReady (embed ⟨560, by decide⟩) routine560 ∧ planCycles routine560.pieces ≤ rankCost ⟨560, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch70_checked (routine560, 85) (by unfold batch70; exact List.mem_cons_self)
theorem ready561 : Chain.RoutineReady (embed ⟨561, by decide⟩) routine561 ∧ planCycles routine561.pieces ≤ rankCost ⟨561, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch70_checked (routine561, 82) (by unfold batch70; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready562 : Chain.RoutineReady (embed ⟨562, by decide⟩) routine562 ∧ planCycles routine562.pieces ≤ rankCost ⟨562, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch70_checked (routine562, 78) (by unfold batch70; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
end W9Machine.N600.Checks
