import SigGolfCandidate.W9Machine_WctN600Evidence

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine560 : ChainRoutine := ⟨663, [4, 2, 0, 1, 0, 0], [⟨231424, [0x25040513, 0x28040613, 0xa7ff8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231429, [0x7508a3, 0x73], .rung 1 none⟩, ⟨231431, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231433, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231435, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨231440, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231442, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨231446, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨231451, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨231455, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine561 : ChainRoutine := ⟨664, [4, 2, 1, 0, 0, 0], [⟨231488, [0x25040513, 0x28040613, 0xa7ff8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231493, [0x7508a3, 0x73], .rung 1 none⟩, ⟨231495, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231497, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231499, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨231504, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨231507, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨231512, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨231516, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine562 : ChainRoutine := ⟨665, [4, 3, 0, 0, 0, 0], [⟨231552, [0x25040513, 0x28040613, 0xa7ff8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231557, [0x7508a3, 0x73], .rung 1 none⟩, ⟨231559, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231561, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231563, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨231568, [0xd508a3, 0x73], .rung 2 none⟩, ⟨231570, [0x13508a3, 0x73], .rung 3 none⟩, ⟨231572, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨231576, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
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
