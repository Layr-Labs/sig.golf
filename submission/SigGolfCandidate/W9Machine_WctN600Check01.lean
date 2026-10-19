import SigGolfCandidate.W9Machine_WctN600Evidence
set_option Elab.async false

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine8 : ChainRoutine := ⟨8, [0, 0, 0, 2, 4, 1], [⟨196096, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨196101, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196104, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨196109, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196111, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196113, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196116, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨196121, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine9 : ChainRoutine := ⟨9, [0, 0, 0, 3, 0, 4], [⟨196160, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196165, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196167, [0x13508a3, 0x73], .rung 3 none⟩, ⟨196169, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨196173, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨196178, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196180, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196182, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196185, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine10 : ChainRoutine := ⟨10, [0, 0, 0, 3, 1, 3], [⟨196224, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196229, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196231, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196234, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨196239, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨196244, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196246, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196249, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine11 : ChainRoutine := ⟨11, [0, 0, 0, 3, 2, 2], [⟨196288, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196293, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196295, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196298, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨196303, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196306, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨196311, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196314, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine12 : ChainRoutine := ⟨12, [0, 0, 0, 3, 3, 1], [⟨196352, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196357, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196359, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196362, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨196367, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196369, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196372, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨196377, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine13 : ChainRoutine := ⟨13, [0, 0, 0, 3, 4, 0], [⟨196416, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196421, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196423, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196426, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨196431, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196433, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196435, [0x13508a3, 0x73], .rung 3 none⟩, ⟨196437, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨196441, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine14 : ChainRoutine := ⟨14, [0, 0, 0, 4, 0, 3], [⟨196480, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨196485, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196487, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196489, [0x13508a3, 0x73], .rung 3 none⟩, ⟨196491, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨196495, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨196500, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196502, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196505, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine15 : ChainRoutine := ⟨15, [0, 0, 0, 4, 1, 2], [⟨196544, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨196549, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196551, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196553, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196556, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨196561, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨196566, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196569, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch1 : List (ChainRoutine × Nat) := [(routine8, 79), (routine9, 79), (routine10, 79), (routine11, 80), (routine12, 79), (routine13, 79), (routine14, 79), (routine15, 79)]
theorem batch1_checked : (batch1.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready8 : Chain.RoutineReady (embed ⟨8, by decide⟩) routine8 ∧ planCycles routine8.pieces ≤ rankCost ⟨8, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine8, 79) (by unfold batch1; exact List.mem_cons_self)
theorem ready9 : Chain.RoutineReady (embed ⟨9, by decide⟩) routine9 ∧ planCycles routine9.pieces ≤ rankCost ⟨9, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine9, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready10 : Chain.RoutineReady (embed ⟨10, by decide⟩) routine10 ∧ planCycles routine10.pieces ≤ rankCost ⟨10, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine10, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready11 : Chain.RoutineReady (embed ⟨11, by decide⟩) routine11 ∧ planCycles routine11.pieces ≤ rankCost ⟨11, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine11, 80) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready12 : Chain.RoutineReady (embed ⟨12, by decide⟩) routine12 ∧ planCycles routine12.pieces ≤ rankCost ⟨12, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine12, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready13 : Chain.RoutineReady (embed ⟨13, by decide⟩) routine13 ∧ planCycles routine13.pieces ≤ rankCost ⟨13, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine13, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready14 : Chain.RoutineReady (embed ⟨14, by decide⟩) routine14 ∧ planCycles routine14.pieces ≤ rankCost ⟨14, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine14, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready15 : Chain.RoutineReady (embed ⟨15, by decide⟩) routine15 ∧ planCycles routine15.pieces ≤ rankCost ⟨15, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine15, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
