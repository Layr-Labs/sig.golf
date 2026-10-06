import SigGolfCandidate.W9Machine.WctN600Evidence

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine8 : ChainRoutine := ⟨8, [0, 0, 0, 0, 3, 2, 1], [⟨33734, [0x1c040513, 0x1f040613, 0x90f8c93, 0x1953823, 0x73], .head 448 496 4 0⟩, ⟨33739, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33741, [0xd508a3, 0x34040613, 0x73], .rung 2 (some 832)⟩, ⟨33744, [0x18040513, 0x1b040613, 0x194f8c93, 0x1953823, 0x73], .head 384 432 5 1⟩, ⟨33749, [0xd508a3, 0x35040613, 0x73], .rung 2 (some 848)⟩, ⟨33752, [0x14040513, 0x36040613, 0x298f8c93, 0x1953823, 0x73], .head 320 864 6 2⟩, ⟨33757, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine9 : ChainRoutine := ⟨9, [0, 0, 0, 0, 3, 3, 0], [⟨33762, [0x1c040513, 0x1f040613, 0x90f8c93, 0x1953823, 0x73], .head 448 496 4 0⟩, ⟨33767, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33769, [0xd508a3, 0x34040613, 0x73], .rung 2 (some 832)⟩, ⟨33772, [0x18040513, 0x1b040613, 0x94f8c93, 0x1953823, 0x73], .head 384 432 5 0⟩, ⟨33777, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33779, [0xd508a3, 0x73], .rung 2 none⟩, ⟨33781, [0x1b043183, 0x1b843703, 0x34343823, 0x34e43c23], .copy 384 848⟩, ⟨33785, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine10 : ChainRoutine := ⟨10, [0, 0, 0, 1, 0, 2, 3], [⟨33790, [0x20040513, 0x23040613, 0x28cf8c93, 0x1953823, 0x73], .head 512 560 3 2⟩, ⟨33795, [0x23043183, 0x23843703, 0x32343823, 0x32e43c23], .copy 512 816⟩, ⟨33799, [0x18040513, 0x1b040613, 0x194f8c93, 0x1953823, 0x73], .head 384 432 5 1⟩, ⟨33804, [0xd508a3, 0x35040613, 0x73], .rung 2 (some 848)⟩, ⟨33807, [0x14040513, 0x17040613, 0x98f8c93, 0x1953823, 0x73], .head 320 368 6 0⟩, ⟨33812, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33814, [0xd508a3, 0x36040613, 0x73], .rung 2 (some 864)⟩, ⟨33817, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine11 : ChainRoutine := ⟨11, [0, 0, 0, 1, 0, 3, 2], [⟨33822, [0x20040513, 0x23040613, 0x28cf8c93, 0x1953823, 0x73], .head 512 560 3 2⟩, ⟨33827, [0x23043183, 0x23843703, 0x32343823, 0x32e43c23], .copy 512 816⟩, ⟨33831, [0x18040513, 0x1b040613, 0x94f8c93, 0x1953823, 0x73], .head 384 432 5 0⟩, ⟨33836, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33838, [0xd508a3, 0x35040613, 0x73], .rung 2 (some 848)⟩, ⟨33841, [0x14040513, 0x17040613, 0x198f8c93, 0x1953823, 0x73], .head 320 368 6 1⟩, ⟨33846, [0xd508a3, 0x36040613, 0x73], .rung 2 (some 864)⟩, ⟨33849, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine12 : ChainRoutine := ⟨12, [0, 0, 0, 1, 1, 1, 3], [⟨33854, [0x20040513, 0x33040613, 0x28cf8c93, 0x1953823, 0x73], .head 512 816 3 2⟩, ⟨33859, [0x1c040513, 0x34040613, 0x290f8c93, 0x1953823, 0x73], .head 448 832 4 2⟩, ⟨33864, [0x18040513, 0x35040613, 0x294f8c93, 0x1953823, 0x73], .head 384 848 5 2⟩, ⟨33869, [0x14040513, 0x17040613, 0x98f8c93, 0x1953823, 0x73], .head 320 368 6 0⟩, ⟨33874, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33876, [0xd508a3, 0x36040613, 0x73], .rung 2 (some 864)⟩, ⟨33879, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine13 : ChainRoutine := ⟨13, [0, 0, 0, 1, 1, 2, 2], [⟨33884, [0x20040513, 0x33040613, 0x28cf8c93, 0x1953823, 0x73], .head 512 816 3 2⟩, ⟨33889, [0x1c040513, 0x34040613, 0x290f8c93, 0x1953823, 0x73], .head 448 832 4 2⟩, ⟨33894, [0x18040513, 0x1b040613, 0x194f8c93, 0x1953823, 0x73], .head 384 432 5 1⟩, ⟨33899, [0xd508a3, 0x35040613, 0x73], .rung 2 (some 848)⟩, ⟨33902, [0x14040513, 0x17040613, 0x198f8c93, 0x1953823, 0x73], .head 320 368 6 1⟩, ⟨33907, [0xd508a3, 0x36040613, 0x73], .rung 2 (some 864)⟩, ⟨33910, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine14 : ChainRoutine := ⟨14, [0, 0, 0, 1, 1, 3, 1], [⟨33915, [0x20040513, 0x33040613, 0x28cf8c93, 0x1953823, 0x73], .head 512 816 3 2⟩, ⟨33920, [0x1c040513, 0x34040613, 0x290f8c93, 0x1953823, 0x73], .head 448 832 4 2⟩, ⟨33925, [0x18040513, 0x1b040613, 0x94f8c93, 0x1953823, 0x73], .head 384 432 5 0⟩, ⟨33930, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33932, [0xd508a3, 0x35040613, 0x73], .rung 2 (some 848)⟩, ⟨33935, [0x14040513, 0x36040613, 0x298f8c93, 0x1953823, 0x73], .head 320 864 6 2⟩, ⟨33940, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine15 : ChainRoutine := ⟨15, [0, 0, 0, 1, 2, 0, 3], [⟨33945, [0x20040513, 0x33040613, 0x28cf8c93, 0x1953823, 0x73], .head 512 816 3 2⟩, ⟨33950, [0x1c040513, 0x1f040613, 0x190f8c93, 0x1953823, 0x73], .head 448 496 4 1⟩, ⟨33955, [0xd508a3, 0x73], .rung 2 none⟩, ⟨33957, [0x1f043183, 0x1f843703, 0x34343023, 0x34e43423], .copy 448 832⟩, ⟨33961, [0x14040513, 0x17040613, 0x98f8c93, 0x1953823, 0x73], .head 320 368 6 0⟩, ⟨33966, [0x7508a3, 0x73], .rung 1 none⟩, ⟨33968, [0xd508a3, 0x36040613, 0x73], .rung 2 (some 864)⟩, ⟨33971, [0x31c43023, 0x31643423, 0x2f040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def batch1 : List (ChainRoutine × Nat) := [(routine8, 70), (routine9, 70), (routine10, 74), (routine11, 74), (routine12, 72), (routine13, 73), (routine14, 72), (routine15, 73)]
theorem batch1_checked : (batch1.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready8 : Chain.RoutineReady (embed ⟨8, by decide⟩) routine8 ∧ planCycles routine8.pieces ≤ rankCost ⟨8, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine8, 70) (by unfold batch1; exact List.mem_cons_self)
theorem ready9 : Chain.RoutineReady (embed ⟨9, by decide⟩) routine9 ∧ planCycles routine9.pieces ≤ rankCost ⟨9, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine9, 70) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready10 : Chain.RoutineReady (embed ⟨10, by decide⟩) routine10 ∧ planCycles routine10.pieces ≤ rankCost ⟨10, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine10, 74) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready11 : Chain.RoutineReady (embed ⟨11, by decide⟩) routine11 ∧ planCycles routine11.pieces ≤ rankCost ⟨11, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine11, 74) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready12 : Chain.RoutineReady (embed ⟨12, by decide⟩) routine12 ∧ planCycles routine12.pieces ≤ rankCost ⟨12, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine12, 72) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready13 : Chain.RoutineReady (embed ⟨13, by decide⟩) routine13 ∧ planCycles routine13.pieces ≤ rankCost ⟨13, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine13, 73) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready14 : Chain.RoutineReady (embed ⟨14, by decide⟩) routine14 ∧ planCycles routine14.pieces ≤ rankCost ⟨14, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine14, 72) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready15 : Chain.RoutineReady (embed ⟨15, by decide⟩) routine15 ∧ planCycles routine15.pieces ≤ rankCost ⟨15, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine15, 73) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
