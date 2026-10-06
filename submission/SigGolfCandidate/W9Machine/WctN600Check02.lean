import SigGolfCandidate.W9Machine.WctN600Evidence

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine16 : ChainRoutine := ⟨16, [0, 0, 0, 1, 2, 1, 2], [⟨1208, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1213, [0x24040513, 0x27040613, 0x190f8c93, 0x1953823, 0x73], .head 576 624 4 1⟩, ⟨1218, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨1221, [0x20040513, 0x3d040613, 0x294f8c93, 0x1953823, 0x73], .head 512 976 5 2⟩, ⟨1226, [0x1c040513, 0x1f040613, 0x198f8c93, 0x1953823, 0x73], .head 448 496 6 1⟩, ⟨1231, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1234, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine17 : ChainRoutine := ⟨17, [0, 0, 0, 1, 2, 2, 1], [⟨1239, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1244, [0x24040513, 0x27040613, 0x190f8c93, 0x1953823, 0x73], .head 576 624 4 1⟩, ⟨1249, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨1252, [0x20040513, 0x23040613, 0x194f8c93, 0x1953823, 0x73], .head 512 560 5 1⟩, ⟨1257, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨1260, [0x1c040513, 0x3e040613, 0x298f8c93, 0x1953823, 0x73], .head 448 992 6 2⟩, ⟨1265, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine18 : ChainRoutine := ⟨18, [0, 0, 0, 1, 2, 3, 0], [⟨1270, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1275, [0x24040513, 0x27040613, 0x190f8c93, 0x1953823, 0x73], .head 576 624 4 1⟩, ⟨1280, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨1283, [0x20040513, 0x23040613, 0x94f8c93, 0x1953823, 0x73], .head 512 560 5 0⟩, ⟨1288, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1290, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1292, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩, ⟨1296, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine19 : ChainRoutine := ⟨19, [0, 0, 0, 1, 3, 0, 2], [⟨1301, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1306, [0x24040513, 0x27040613, 0x90f8c93, 0x1953823, 0x73], .head 576 624 4 0⟩, ⟨1311, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1313, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1315, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩, ⟨1319, [0x1c040513, 0x1f040613, 0x198f8c93, 0x1953823, 0x73], .head 448 496 6 1⟩, ⟨1324, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1327, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine20 : ChainRoutine := ⟨20, [0, 0, 0, 1, 3, 1, 1], [⟨1332, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1337, [0x24040513, 0x27040613, 0x90f8c93, 0x1953823, 0x73], .head 576 624 4 0⟩, ⟨1342, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1344, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨1347, [0x20040513, 0x3d040613, 0x294f8c93, 0x1953823, 0x73], .head 512 976 5 2⟩, ⟨1352, [0x1c040513, 0x3e040613, 0x298f8c93, 0x1953823, 0x73], .head 448 992 6 2⟩, ⟨1357, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine21 : ChainRoutine := ⟨21, [0, 0, 0, 1, 3, 2, 0], [⟨1362, [0x28040513, 0x3b040613, 0x28cf8c93, 0x1953823, 0x73], .head 640 944 3 2⟩, ⟨1367, [0x24040513, 0x27040613, 0x90f8c93, 0x1953823, 0x73], .head 576 624 4 0⟩, ⟨1372, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1374, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨1377, [0x20040513, 0x23040613, 0x194f8c93, 0x1953823, 0x73], .head 512 560 5 1⟩, ⟨1382, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1384, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩, ⟨1388, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine22 : ChainRoutine := ⟨22, [0, 0, 0, 2, 0, 1, 3], [⟨1393, [0x28040513, 0x2b040613, 0x18cf8c93, 0x1953823, 0x73], .head 640 688 3 1⟩, ⟨1398, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1400, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1404, [0x20040513, 0x3d040613, 0x294f8c93, 0x1953823, 0x73], .head 512 976 5 2⟩, ⟨1409, [0x1c040513, 0x1f040613, 0x98f8c93, 0x1953823, 0x73], .head 448 496 6 0⟩, ⟨1414, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1416, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1419, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine23 : ChainRoutine := ⟨23, [0, 0, 0, 2, 0, 2, 2], [⟨1424, [0x28040513, 0x2b040613, 0x18cf8c93, 0x1953823, 0x73], .head 640 688 3 1⟩, ⟨1429, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1431, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1435, [0x20040513, 0x23040613, 0x194f8c93, 0x1953823, 0x73], .head 512 560 5 1⟩, ⟨1440, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨1443, [0x1c040513, 0x1f040613, 0x198f8c93, 0x1953823, 0x73], .head 448 496 6 1⟩, ⟨1448, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1451, [0x39c43023, 0x39643423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def batch2 : List (ChainRoutine × Nat) := [(routine16, 73), (routine17, 73), (routine18, 73), (routine19, 73), (routine20, 72), (routine21, 73), (routine22, 73), (routine23, 74)]
theorem batch2_checked : (batch2.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready16 : Chain.RoutineReady (embed ⟨16, by decide⟩) routine16 ∧ planCycles routine16.pieces ≤ rankCost ⟨16, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine16, 73) (by unfold batch2; exact List.mem_cons_self)
theorem ready17 : Chain.RoutineReady (embed ⟨17, by decide⟩) routine17 ∧ planCycles routine17.pieces ≤ rankCost ⟨17, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine17, 73) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready18 : Chain.RoutineReady (embed ⟨18, by decide⟩) routine18 ∧ planCycles routine18.pieces ≤ rankCost ⟨18, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine18, 73) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready19 : Chain.RoutineReady (embed ⟨19, by decide⟩) routine19 ∧ planCycles routine19.pieces ≤ rankCost ⟨19, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine19, 73) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready20 : Chain.RoutineReady (embed ⟨20, by decide⟩) routine20 ∧ planCycles routine20.pieces ≤ rankCost ⟨20, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine20, 72) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready21 : Chain.RoutineReady (embed ⟨21, by decide⟩) routine21 ∧ planCycles routine21.pieces ≤ rankCost ⟨21, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine21, 73) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready22 : Chain.RoutineReady (embed ⟨22, by decide⟩) routine22 ∧ planCycles routine22.pieces ≤ rankCost ⟨22, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine22, 73) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready23 : Chain.RoutineReady (embed ⟨23, by decide⟩) routine23 ∧ planCycles routine23.pieces ≤ rankCost ⟨23, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine23, 74) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
