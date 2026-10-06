import SigGolfCandidate.W9Machine.WctN600Evidence

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine32 : ChainRoutine := ⟨32, [0, 0, 0, 2, 3, 0, 1], [⟨1707, [0x28040513, 0x2b040613, 0x18cf8c93, 0x1953823, 0x73], .head 640 688 3 1⟩, ⟨1712, [0xd508a3, 0x3b040613, 0x73], .rung 2 (some 944)⟩, ⟨1715, [0x24040513, 0x27040613, 0x90f8c93, 0x1953823, 0x73], .head 576 624 4 0⟩, ⟨1720, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1722, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1724, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩, ⟨1728, [0x1c040513, 0x3e040613, 0x298f8c93, 0x1953823, 0x73], .head 448 992 6 2⟩, ⟨1733, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine33 : ChainRoutine := ⟨33, [0, 0, 0, 2, 3, 1, 0], [⟨1738, [0x28040513, 0x2b040613, 0x18cf8c93, 0x1953823, 0x73], .head 640 688 3 1⟩, ⟨1743, [0xd508a3, 0x3b040613, 0x73], .rung 2 (some 944)⟩, ⟨1746, [0x24040513, 0x27040613, 0x90f8c93, 0x1953823, 0x73], .head 576 624 4 0⟩, ⟨1751, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1753, [0xd508a3, 0x3c040613, 0x73], .rung 2 (some 960)⟩, ⟨1756, [0x20040513, 0x23040613, 0x294f8c93, 0x1953823, 0x73], .head 512 560 5 2⟩, ⟨1761, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩, ⟨1765, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine34 : ChainRoutine := ⟨34, [0, 0, 0, 3, 0, 0, 3], [⟨1770, [0x28040513, 0x2b040613, 0x8cf8c93, 0x1953823, 0x73], .head 640 688 3 0⟩, ⟨1775, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1777, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1779, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1783, [0x1c040513, 0x1f040613, 0x98f8c93, 0x1953823, 0x73], .head 448 496 6 0⟩, ⟨1788, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1790, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1793, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine35 : ChainRoutine := ⟨35, [0, 0, 0, 3, 0, 1, 2], [⟨1798, [0x28040513, 0x2b040613, 0x8cf8c93, 0x1953823, 0x73], .head 640 688 3 0⟩, ⟨1803, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1805, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1807, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1811, [0x20040513, 0x3d040613, 0x294f8c93, 0x1953823, 0x73], .head 512 976 5 2⟩, ⟨1816, [0x1c040513, 0x1f040613, 0x198f8c93, 0x1953823, 0x73], .head 448 496 6 1⟩, ⟨1821, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1824, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine36 : ChainRoutine := ⟨36, [0, 0, 0, 3, 0, 2, 1], [⟨1829, [0x28040513, 0x2b040613, 0x8cf8c93, 0x1953823, 0x73], .head 640 688 3 0⟩, ⟨1834, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1836, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1838, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1842, [0x20040513, 0x23040613, 0x194f8c93, 0x1953823, 0x73], .head 512 560 5 1⟩, ⟨1847, [0xd508a3, 0x3d040613, 0x73], .rung 2 (some 976)⟩, ⟨1850, [0x1c040513, 0x3e040613, 0x298f8c93, 0x1953823, 0x73], .head 448 992 6 2⟩, ⟨1855, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine37 : ChainRoutine := ⟨37, [0, 0, 0, 3, 0, 3, 0], [⟨1860, [0x28040513, 0x2b040613, 0x8cf8c93, 0x1953823, 0x73], .head 640 688 3 0⟩, ⟨1865, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1867, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1869, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩, ⟨1873, [0x20040513, 0x23040613, 0x94f8c93, 0x1953823, 0x73], .head 512 560 5 0⟩, ⟨1878, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1880, [0xd508a3, 0x73], .rung 2 none⟩, ⟨1882, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩, ⟨1886, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine38 : ChainRoutine := ⟨38, [0, 0, 0, 3, 1, 0, 2], [⟨1891, [0x28040513, 0x2b040613, 0x8cf8c93, 0x1953823, 0x73], .head 640 688 3 0⟩, ⟨1896, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1898, [0xd508a3, 0x3b040613, 0x73], .rung 2 (some 944)⟩, ⟨1901, [0x24040513, 0x27040613, 0x290f8c93, 0x1953823, 0x73], .head 576 624 4 2⟩, ⟨1906, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩, ⟨1910, [0x1c040513, 0x1f040613, 0x198f8c93, 0x1953823, 0x73], .head 448 496 6 1⟩, ⟨1915, [0xd508a3, 0x3e040613, 0x73], .rung 2 (some 992)⟩, ⟨1918, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def routine39 : ChainRoutine := ⟨39, [0, 0, 0, 3, 1, 1, 1], [⟨1923, [0x28040513, 0x2b040613, 0x8cf8c93, 0x1953823, 0x73], .head 640 688 3 0⟩, ⟨1928, [0x7508a3, 0x73], .rung 1 none⟩, ⟨1930, [0xd508a3, 0x3b040613, 0x73], .rung 2 (some 944)⟩, ⟨1933, [0x24040513, 0x3c040613, 0x290f8c93, 0x1953823, 0x73], .head 576 960 4 2⟩, ⟨1938, [0x20040513, 0x3d040613, 0x294f8c93, 0x1953823, 0x73], .head 512 976 5 2⟩, ⟨1943, [0x1c040513, 0x3e040613, 0x298f8c93, 0x1953823, 0x73], .head 448 992 6 2⟩, ⟨1948, [0x39c43023, 0x38443423, 0x37040513, 0x8000593, 0xb8067], .leaf⟩]⟩
def batch4 : List (ChainRoutine × Nat) := [(routine32, 73), (routine33, 74), (routine34, 70), (routine35, 73), (routine36, 73), (routine37, 73), (routine38, 74), (routine39, 72)]
theorem batch4_checked : (batch4.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready32 : Chain.RoutineReady (embed ⟨32, by decide⟩) routine32 ∧ planCycles routine32.pieces ≤ rankCost ⟨32, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine32, 73) (by unfold batch4; exact List.mem_cons_self)
theorem ready33 : Chain.RoutineReady (embed ⟨33, by decide⟩) routine33 ∧ planCycles routine33.pieces ≤ rankCost ⟨33, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine33, 74) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready34 : Chain.RoutineReady (embed ⟨34, by decide⟩) routine34 ∧ planCycles routine34.pieces ≤ rankCost ⟨34, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine34, 70) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready35 : Chain.RoutineReady (embed ⟨35, by decide⟩) routine35 ∧ planCycles routine35.pieces ≤ rankCost ⟨35, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine35, 73) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready36 : Chain.RoutineReady (embed ⟨36, by decide⟩) routine36 ∧ planCycles routine36.pieces ≤ rankCost ⟨36, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine36, 73) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready37 : Chain.RoutineReady (embed ⟨37, by decide⟩) routine37 ∧ planCycles routine37.pieces ≤ rankCost ⟨37, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine37, 73) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready38 : Chain.RoutineReady (embed ⟨38, by decide⟩) routine38 ∧ planCycles routine38.pieces ≤ rankCost ⟨38, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine38, 74) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready39 : Chain.RoutineReady (embed ⟨39, by decide⟩) routine39 ∧ planCycles routine39.pieces ≤ rankCost ⟨39, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine39, 72) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
