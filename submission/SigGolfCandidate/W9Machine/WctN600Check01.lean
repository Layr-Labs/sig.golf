import SigGolfCandidate.W9Machine.WctN600Evidence

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine8 : ChainRoutine := ⟨8, [0, 0, 0, 0, 3, 2, 1], [⟨966, [0x24040513, 0x27040613, 0x90f8c93, 0x1953823, 0x73], .head 576 624 4 0⟩, ⟨971, [0x7508a3, 0x73], .rung 1 none⟩, ⟨973, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨976, [0x20040513, 0x23040613, 0x194f8c93, 0x1953823, 0x73], .head 512 560 5 1⟩, ⟨981, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨984, [0x1c040513, 0x3e040613, 0x298f8c93, 0x1953823, 0x73], .head 448 992 6 2⟩, ⟨989, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine9 : ChainRoutine := ⟨9, [0, 0, 0, 0, 3, 3, 0], [⟨994, [0x24040513, 0x27040613, 0x90f8c93, 0x1953823, 0x73], .head 576 624 4 0⟩, ⟨999, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1001, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨1004, [0x20040513, 0x23040613, 0x94f8c93, 0x1953823, 0x73], .head 512 560 5 0⟩, ⟨1009, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1011, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1013, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩, ⟨1017, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine10 : ChainRoutine := ⟨10, [0, 0, 0, 1, 0, 2, 3], [⟨1022, [0x28040513, 0x2b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 688 3 2⟩, ⟨1027, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1031, [0x20040513, 0x23040613, 0x194f8c93, 0x1953823, 0x73], .head 512 560 5 1⟩, ⟨1036, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨1039, [0x1c040513, 0x1f040613, 0x98f8c93, 0x1953823, 0x73], .head 448 496 6 0⟩, ⟨1044, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1046, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1049, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine11 : ChainRoutine := ⟨11, [0, 0, 0, 1, 0, 3, 2], [⟨1054, [0x28040513, 0x2b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 688 3 2⟩, ⟨1059, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1063, [0x20040513, 0x23040613, 0x94f8c93, 0x1953823, 0x73], .head 512 560 5 0⟩, ⟨1068, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1070, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨1073, [0x1c040513, 0x1f040613, 0x198f8c93, 0x1953823, 0x73], .head 448 496 6 1⟩, ⟨1078, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1081, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine12 : ChainRoutine := ⟨12, [0, 0, 0, 1, 1, 1, 3], [⟨1086, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1091, [0x24040513, 0x3c040613, 0x290f8c93, 0x1953823, 0x73], .head 576 960 4 2⟩, ⟨1096, [0x20040513, 0x3d040613, 0x294f8c93, 0x1953823, 0x73], .head 512 976 5 2⟩, ⟨1101, [0x1c040513, 0x1f040613, 0x98f8c93, 0x1953823, 0x73], .head 448 496 6 0⟩, ⟨1106, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1108, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1111, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine13 : ChainRoutine := ⟨13, [0, 0, 0, 1, 1, 2, 2], [⟨1116, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1121, [0x24040513, 0x3c040613, 0x290f8c93, 0x1953823, 0x73], .head 576 960 4 2⟩, ⟨1126, [0x20040513, 0x23040613, 0x194f8c93, 0x1953823, 0x73], .head 512 560 5 1⟩, ⟨1131, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨1134, [0x1c040513, 0x1f040613, 0x198f8c93, 0x1953823, 0x73], .head 448 496 6 1⟩, ⟨1139, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1142, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine14 : ChainRoutine := ⟨14, [0, 0, 0, 1, 1, 3, 1], [⟨1147, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1152, [0x24040513, 0x3c040613, 0x290f8c93, 0x1953823, 0x73], .head 576 960 4 2⟩, ⟨1157, [0x20040513, 0x23040613, 0x94f8c93, 0x1953823, 0x73], .head 512 560 5 0⟩, ⟨1162, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1164, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨1167, [0x1c040513, 0x3e040613, 0x298f8c93, 0x1953823, 0x73], .head 448 992 6 2⟩, ⟨1172, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine15 : ChainRoutine := ⟨15, [0, 0, 0, 1, 2, 0, 3], [⟨1177, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1182, [0x24040513, 0x27040613, 0x190f8c93, 0x1953823, 0x73], .head 576 624 4 1⟩, ⟨1187, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1189, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩, ⟨1193, [0x1c040513, 0x1f040613, 0x98f8c93, 0x1953823, 0x73], .head 448 496 6 0⟩, ⟨1198, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1200, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1203, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
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
