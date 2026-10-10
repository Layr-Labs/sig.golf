import SigGolfCandidate.W9Machine.WctN600Evidence

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine560 : ChainRoutine := ⟨663, [4, 2, 0, 1, 0, 0], [⟨144732, [0x28040513, 0x2b040613, 0xa7ff8c93, 0x1953823, 0x73], .head 640 688 0 0⟩, ⟨144737, [0x7508a3, 0x73], .rung 1 none⟩, ⟨144739, [0xd508a3, 0x73], .rung 2 none⟩, ⟨144741, [0x13508a3, 0x73], .rung 3 none⟩, ⟨144743, [0x24040513, 0x27040613, 0xc83f8c93, 0x1953823, 0x73], .head 576 624 1 2⟩, ⟨144748, [0x13508a3, 0x73], .rung 3 none⟩, ⟨144750, [0x27043183, 0x27843703, 0x2e343023, 0x2ee43423], .copy 576 736⟩, ⟨144754, [0x1c040513, 0x1f040613, 0xd8bf8c93, 0x1953823, 0x73], .head 448 496 3 3⟩, ⟨144759, [0x1f043183, 0x1f843703, 0x30343023, 0x30e43423], .copy 448 768⟩, ⟨144763, [0x2df43023, 0x2c043423, 0x2b040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine561 : ChainRoutine := ⟨664, [4, 2, 1, 0, 0, 0], [⟨244180, [0x28040513, 0x2b040613, 0xa7ff8c93, 0x1953823, 0x73], .head 640 688 0 0⟩, ⟨244185, [0x7508a3, 0x73], .rung 1 none⟩, ⟨244187, [0xd508a3, 0x73], .rung 2 none⟩, ⟨244189, [0x13508a3, 0x73], .rung 3 none⟩, ⟨244191, [0x24040513, 0x27040613, 0xc83f8c93, 0x1953823, 0x73], .head 576 624 1 2⟩, ⟨244196, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨244199, [0x20040513, 0x23040613, 0xd87f8c93, 0x1953823, 0x73], .head 512 560 2 3⟩, ⟨244204, [0x23043183, 0x23843703, 0x2e343823, 0x2ee43c23], .copy 512 752⟩, ⟨244208, [0x2df43023, 0x2c043423, 0x2b040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine562 : ChainRoutine := ⟨665, [4, 3, 0, 0, 0, 0], [⟨239199, [0x28040513, 0x2b040613, 0xa7ff8c93, 0x1953823, 0x73], .head 640 688 0 0⟩, ⟨239204, [0x7508a3, 0x73], .rung 1 none⟩, ⟨239206, [0xd508a3, 0x73], .rung 2 none⟩, ⟨239208, [0x13508a3, 0x73], .rung 3 none⟩, ⟨239210, [0x24040513, 0x27040613, 0xb83f8c93, 0x1953823, 0x73], .head 576 624 1 1⟩, ⟨239215, [0xd508a3, 0x73], .rung 2 none⟩, ⟨239217, [0x13508a3, 0x73], .rung 3 none⟩, ⟨239219, [0x27043183, 0x27843703, 0x2e343023, 0x2ee43423], .copy 576 736⟩, ⟨239223, [0x2df43023, 0x2c043423, 0x2b040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
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
