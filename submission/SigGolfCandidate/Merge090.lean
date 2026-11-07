import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge084
import SigGolfCandidate.Merge085
import SigGolfCandidate.Merge086
import SigGolfCandidate.Merge087
import SigGolfCandidate.Merge088
import SigGolfCandidate.Merge089
set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from W9Machine_WctN600Check65 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine520 : ChainRoutine := ⟨622, [0x3, 0x2, 0x1, 0x0, 0x0, 0x1], [⟨228864, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨228869, [0xd50823, 0x73], .rung 2 none⟩, ⟨228871, [0x1350823, 0x73], .rung 3 none⟩, ⟨228873, [0x1f840513, 0x1e840613, 0xb02f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨228878, [0x1350823, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨228881, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨228886, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨228890, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨228895, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine521 : ChainRoutine := ⟨624, [0x3, 0x2, 0x1, 0x1, 0x0, 0x0], [⟨228928, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨228933, [0xd50823, 0x73], .rung 2 none⟩, ⟨228935, [0x1350823, 0x73], .rung 3 none⟩, ⟨228937, [0x1f840513, 0x1e840613, 0xb02f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨228942, [0x1350823, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨228945, [0x21040513, 0x2c040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨228950, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨228955, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨228959, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine522 : ChainRoutine := ⟨625, [0x3, 0x2, 0x2, 0x0, 0x0, 0x0], [⟨228992, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨228997, [0xd50823, 0x73], .rung 2 none⟩, ⟨228999, [0x1350823, 0x73], .rung 3 none⟩, ⟨229001, [0x1f840513, 0x1e840613, 0xb02f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨229006, [0x1350823, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨229009, [0x21040513, 0x24040613, 0xc02f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨229014, [0x1350823, 0x73], .rung 3 none⟩, ⟨229016, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨229020, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine523 : ChainRoutine := ⟨626, [0x3, 0x3, 0x0, 0x0, 0x0, 0x1], [⟨229056, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨229061, [0xd50823, 0x73], .rung 2 none⟩, ⟨229063, [0x1350823, 0x73], .rung 3 none⟩, ⟨229065, [0x1f840513, 0x1e840613, 0xb01f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨229070, [0xd50823, 0x73], .rung 2 none⟩, ⟨229072, [0x1350823, 0x73], .rung 3 none⟩, ⟨229074, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨229078, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨229083, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine524 : ChainRoutine := ⟨627, [0x3, 0x3, 0x0, 0x0, 0x1, 0x0], [⟨229120, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨229125, [0xd50823, 0x73], .rung 2 none⟩, ⟨229127, [0x1350823, 0x73], .rung 3 none⟩, ⟨229129, [0x1f840513, 0x1e840613, 0xb01f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨229134, [0xd50823, 0x73], .rung 2 none⟩, ⟨229136, [0x1350823, 0x73], .rung 3 none⟩, ⟨229138, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨229142, [0x1a840513, 0x1d840613, 0xe03f8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨229147, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨229151, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine525 : ChainRoutine := ⟨628, [0x3, 0x3, 0x0, 0x1, 0x0, 0x0], [⟨229184, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨229189, [0xd50823, 0x73], .rung 2 none⟩, ⟨229191, [0x1350823, 0x73], .rung 3 none⟩, ⟨229193, [0x1f840513, 0x1e840613, 0xb01f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨229198, [0xd50823, 0x73], .rung 2 none⟩, ⟨229200, [0x1350823, 0x73], .rung 3 none⟩, ⟨229202, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨229206, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨229211, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨229215, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine526 : ChainRoutine := ⟨629, [0x3, 0x3, 0x1, 0x0, 0x0, 0x0], [⟨229248, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨229253, [0xd50823, 0x73], .rung 2 none⟩, ⟨229255, [0x1350823, 0x73], .rung 3 none⟩, ⟨229257, [0x1f840513, 0x1e840613, 0xb01f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨229262, [0xd50823, 0x73], .rung 2 none⟩, ⟨229264, [0x1350823, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨229267, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨229272, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨229276, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine527 : ChainRoutine := ⟨630, [0x3, 0x4, 0x0, 0x0, 0x0, 0x0], [⟨229312, [0x25040513, 0x28040613, 0xa01f8c93, 0x1953823, 0x73], .head 592 640 0 1⟩, ⟨229317, [0xd50823, 0x73], .rung 2 none⟩, ⟨229319, [0x1350823, 0x73], .rung 3 none⟩, ⟨229321, [0x1f840513, 0x1e840613, 0xb00f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨229326, [0x750823, 0x73], .rung 1 none⟩, ⟨229328, [0xd50823, 0x73], .rung 2 none⟩, ⟨229330, [0x1350823, 0x73], .rung 3 none⟩, ⟨229332, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨229336, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch65 : List (ChainRoutine × Nat) := [(routine520, 85), (routine521, 85), (routine522, 82), (routine523, 81), (routine524, 85), (routine525, 85), (routine526, 82), (routine527, 78)]
theorem batch65_checked : (batch65.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready520 : Chain.RoutineReady (embed ⟨520, by decide⟩) routine520 ∧ planCycles routine520.pieces ≤ rankCost ⟨520, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine520, 85) (by unfold batch65; exact List.mem_cons_self)
theorem ready521 : Chain.RoutineReady (embed ⟨521, by decide⟩) routine521 ∧ planCycles routine521.pieces ≤ rankCost ⟨521, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine521, 85) (by unfold batch65; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready522 : Chain.RoutineReady (embed ⟨522, by decide⟩) routine522 ∧ planCycles routine522.pieces ≤ rankCost ⟨522, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine522, 82) (by unfold batch65; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready523 : Chain.RoutineReady (embed ⟨523, by decide⟩) routine523 ∧ planCycles routine523.pieces ≤ rankCost ⟨523, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine523, 81) (by unfold batch65; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready524 : Chain.RoutineReady (embed ⟨524, by decide⟩) routine524 ∧ planCycles routine524.pieces ≤ rankCost ⟨524, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine524, 85) (by unfold batch65; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready525 : Chain.RoutineReady (embed ⟨525, by decide⟩) routine525 ∧ planCycles routine525.pieces ≤ rankCost ⟨525, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine525, 85) (by unfold batch65; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready526 : Chain.RoutineReady (embed ⟨526, by decide⟩) routine526 ∧ planCycles routine526.pieces ≤ rankCost ⟨526, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine526, 82) (by unfold batch65; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready527 : Chain.RoutineReady (embed ⟨527, by decide⟩) routine527 ∧ planCycles routine527.pieces ≤ rankCost ⟨527, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch65_checked (routine527, 78) (by unfold batch65; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check66 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine528 : ChainRoutine := ⟨631, [0x4, 0x0, 0x0, 0x0, 0x0, 0x3], [⟨229376, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229381, [0x750823, 0x73], .rung 1 none⟩, ⟨229383, [0xd50823, 0x73], .rung 2 none⟩, ⟨229385, [0x1350823, 0x73], .rung 3 none⟩, ⟨229387, [0x14040513, 0x17040613, 0xf01f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨229392, [0xd50823, 0x73], .rung 2 none⟩, ⟨229394, [0x1350823, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨229397, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine529 : ChainRoutine := ⟨632, [0x4, 0x0, 0x0, 0x0, 0x1, 0x2], [⟨229440, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229445, [0x750823, 0x73], .rung 1 none⟩, ⟨229447, [0xd50823, 0x73], .rung 2 none⟩, ⟨229449, [0x1350823, 0x73], .rung 3 none⟩, ⟨229451, [0x1a840513, 0x2e040613, 0xe03f8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨229456, [0x14040513, 0x17040613, 0xf02f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨229461, [0x1350823, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨229464, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine530 : ChainRoutine := ⟨633, [0x4, 0x0, 0x0, 0x0, 0x2, 0x1], [⟨229504, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229509, [0x750823, 0x73], .rung 1 none⟩, ⟨229511, [0xd50823, 0x73], .rung 2 none⟩, ⟨229513, [0x1350823, 0x73], .rung 3 none⟩, ⟨229515, [0x1a840513, 0x1d840613, 0xe02f8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨229520, [0x1350823, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨229523, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨229528, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine531 : ChainRoutine := ⟨634, [0x4, 0x0, 0x0, 0x0, 0x3, 0x0], [⟨229568, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229573, [0x750823, 0x73], .rung 1 none⟩, ⟨229575, [0xd50823, 0x73], .rung 2 none⟩, ⟨229577, [0x1350823, 0x73], .rung 3 none⟩, ⟨229579, [0x1a840513, 0x1d840613, 0xe01f8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨229584, [0xd50823, 0x73], .rung 2 none⟩, ⟨229586, [0x1350823, 0x73], .rung 3 none⟩, ⟨229588, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨229592, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine532 : ChainRoutine := ⟨635, [0x4, 0x0, 0x0, 0x1, 0x0, 0x2], [⟨229632, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229637, [0x750823, 0x73], .rung 1 none⟩, ⟨229639, [0xd50823, 0x73], .rung 2 none⟩, ⟨229641, [0x1350823, 0x73], .rung 3 none⟩, ⟨229643, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨229648, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨229652, [0x14040513, 0x17040613, 0xf02f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨229657, [0x1350823, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨229660, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine533 : ChainRoutine := ⟨636, [0x4, 0x0, 0x0, 0x1, 0x1, 0x1], [⟨229696, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229701, [0x750823, 0x73], .rung 1 none⟩, ⟨229703, [0xd50823, 0x73], .rung 2 none⟩, ⟨229705, [0x1350823, 0x73], .rung 3 none⟩, ⟨229707, [0x19040513, 0x2d040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨229712, [0x1a840513, 0x2e040613, 0xe03f8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨229717, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨229722, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine534 : ChainRoutine := ⟨637, [0x4, 0x0, 0x0, 0x1, 0x2, 0x0], [⟨229760, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229765, [0x750823, 0x73], .rung 1 none⟩, ⟨229767, [0xd50823, 0x73], .rung 2 none⟩, ⟨229769, [0x1350823, 0x73], .rung 3 none⟩, ⟨229771, [0x19040513, 0x2d040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨229776, [0x1a840513, 0x1d840613, 0xe02f8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨229781, [0x1350823, 0x73], .rung 3 none⟩, ⟨229783, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨229787, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine535 : ChainRoutine := ⟨638, [0x4, 0x0, 0x0, 0x2, 0x0, 0x1], [⟨229824, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229829, [0x750823, 0x73], .rung 1 none⟩, ⟨229831, [0xd50823, 0x73], .rung 2 none⟩, ⟨229833, [0x1350823, 0x73], .rung 3 none⟩, ⟨229835, [0x19040513, 0x18040613, 0xd02f8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨229840, [0x1350823, 0x73], .rung 3 none⟩, ⟨229842, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨229846, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨229851, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch66 : List (ChainRoutine × Nat) := [(routine528, 75), (routine529, 78), (routine530, 78), (routine531, 78), (routine532, 82), (routine533, 80), (routine534, 81), (routine535, 81)]
theorem batch66_checked : (batch66.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready528 : Chain.RoutineReady (embed ⟨528, by decide⟩) routine528 ∧ planCycles routine528.pieces ≤ rankCost ⟨528, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine528, 75) (by unfold batch66; exact List.mem_cons_self)
theorem ready529 : Chain.RoutineReady (embed ⟨529, by decide⟩) routine529 ∧ planCycles routine529.pieces ≤ rankCost ⟨529, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine529, 78) (by unfold batch66; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready530 : Chain.RoutineReady (embed ⟨530, by decide⟩) routine530 ∧ planCycles routine530.pieces ≤ rankCost ⟨530, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine530, 78) (by unfold batch66; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready531 : Chain.RoutineReady (embed ⟨531, by decide⟩) routine531 ∧ planCycles routine531.pieces ≤ rankCost ⟨531, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine531, 78) (by unfold batch66; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready532 : Chain.RoutineReady (embed ⟨532, by decide⟩) routine532 ∧ planCycles routine532.pieces ≤ rankCost ⟨532, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine532, 82) (by unfold batch66; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready533 : Chain.RoutineReady (embed ⟨533, by decide⟩) routine533 ∧ planCycles routine533.pieces ≤ rankCost ⟨533, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine533, 80) (by unfold batch66; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready534 : Chain.RoutineReady (embed ⟨534, by decide⟩) routine534 ∧ planCycles routine534.pieces ≤ rankCost ⟨534, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine534, 81) (by unfold batch66; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready535 : Chain.RoutineReady (embed ⟨535, by decide⟩) routine535 ∧ planCycles routine535.pieces ≤ rankCost ⟨535, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch66_checked (routine535, 81) (by unfold batch66; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check67 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine536 : ChainRoutine := ⟨639, [0x4, 0x0, 0x0, 0x2, 0x1, 0x0], [⟨229888, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229893, [0x750823, 0x73], .rung 1 none⟩, ⟨229895, [0xd50823, 0x73], .rung 2 none⟩, ⟨229897, [0x1350823, 0x73], .rung 3 none⟩, ⟨229899, [0x19040513, 0x18040613, 0xd02f8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨229904, [0x1350823, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨229907, [0x1a840513, 0x1d840613, 0xe03f8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨229912, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨229916, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine537 : ChainRoutine := ⟨640, [0x4, 0x0, 0x0, 0x3, 0x0, 0x0], [⟨229952, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨229957, [0x750823, 0x73], .rung 1 none⟩, ⟨229959, [0xd50823, 0x73], .rung 2 none⟩, ⟨229961, [0x1350823, 0x73], .rung 3 none⟩, ⟨229963, [0x19040513, 0x18040613, 0xd01f8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨229968, [0xd50823, 0x73], .rung 2 none⟩, ⟨229970, [0x1350823, 0x73], .rung 3 none⟩, ⟨229972, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨229976, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine538 : ChainRoutine := ⟨641, [0x4, 0x0, 0x1, 0x0, 0x0, 0x2], [⟨230016, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230021, [0x750823, 0x73], .rung 1 none⟩, ⟨230023, [0xd50823, 0x73], .rung 2 none⟩, ⟨230025, [0x1350823, 0x73], .rung 3 none⟩, ⟨230027, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨230032, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨230036, [0x14040513, 0x17040613, 0xf02f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨230041, [0x1350823, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨230044, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine539 : ChainRoutine := ⟨642, [0x4, 0x0, 0x1, 0x0, 0x1, 0x1], [⟨230080, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230085, [0x750823, 0x73], .rung 1 none⟩, ⟨230087, [0xd50823, 0x73], .rung 2 none⟩, ⟨230089, [0x1350823, 0x73], .rung 3 none⟩, ⟨230091, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨230096, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨230100, [0x1a840513, 0x2e040613, 0xe03f8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨230105, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨230110, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine540 : ChainRoutine := ⟨643, [0x4, 0x0, 0x1, 0x0, 0x2, 0x0], [⟨230144, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230149, [0x750823, 0x73], .rung 1 none⟩, ⟨230151, [0xd50823, 0x73], .rung 2 none⟩, ⟨230153, [0x1350823, 0x73], .rung 3 none⟩, ⟨230155, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨230160, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨230164, [0x1a840513, 0x1d840613, 0xe02f8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨230169, [0x1350823, 0x73], .rung 3 none⟩, ⟨230171, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨230175, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine541 : ChainRoutine := ⟨644, [0x4, 0x0, 0x1, 0x1, 0x0, 0x1], [⟨230208, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230213, [0x750823, 0x73], .rung 1 none⟩, ⟨230215, [0xd50823, 0x73], .rung 2 none⟩, ⟨230217, [0x1350823, 0x73], .rung 3 none⟩, ⟨230219, [0x21040513, 0x2c040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨230224, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨230229, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨230233, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨230238, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine542 : ChainRoutine := ⟨645, [0x4, 0x0, 0x1, 0x1, 0x1, 0x0], [⟨230272, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230277, [0x750823, 0x73], .rung 1 none⟩, ⟨230279, [0xd50823, 0x73], .rung 2 none⟩, ⟨230281, [0x1350823, 0x73], .rung 3 none⟩, ⟨230283, [0x21040513, 0x2c040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨230288, [0x19040513, 0x2d040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨230293, [0x1a840513, 0x1d840613, 0xe03f8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨230298, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨230302, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine543 : ChainRoutine := ⟨646, [0x4, 0x0, 0x1, 0x2, 0x0, 0x0], [⟨230336, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230341, [0x750823, 0x73], .rung 1 none⟩, ⟨230343, [0xd50823, 0x73], .rung 2 none⟩, ⟨230345, [0x1350823, 0x73], .rung 3 none⟩, ⟨230347, [0x21040513, 0x2c040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨230352, [0x19040513, 0x18040613, 0xd02f8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨230357, [0x1350823, 0x73], .rung 3 none⟩, ⟨230359, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨230363, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch67 : List (ChainRoutine × Nat) := [(routine536, 82), (routine537, 78), (routine538, 82), (routine539, 84), (routine540, 85), (routine541, 84), (routine542, 84), (routine543, 81)]
theorem batch67_checked : (batch67.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready536 : Chain.RoutineReady (embed ⟨536, by decide⟩) routine536 ∧ planCycles routine536.pieces ≤ rankCost ⟨536, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine536, 82) (by unfold batch67; exact List.mem_cons_self)
theorem ready537 : Chain.RoutineReady (embed ⟨537, by decide⟩) routine537 ∧ planCycles routine537.pieces ≤ rankCost ⟨537, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine537, 78) (by unfold batch67; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready538 : Chain.RoutineReady (embed ⟨538, by decide⟩) routine538 ∧ planCycles routine538.pieces ≤ rankCost ⟨538, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine538, 82) (by unfold batch67; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready539 : Chain.RoutineReady (embed ⟨539, by decide⟩) routine539 ∧ planCycles routine539.pieces ≤ rankCost ⟨539, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine539, 84) (by unfold batch67; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready540 : Chain.RoutineReady (embed ⟨540, by decide⟩) routine540 ∧ planCycles routine540.pieces ≤ rankCost ⟨540, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine540, 85) (by unfold batch67; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready541 : Chain.RoutineReady (embed ⟨541, by decide⟩) routine541 ∧ planCycles routine541.pieces ≤ rankCost ⟨541, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine541, 84) (by unfold batch67; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready542 : Chain.RoutineReady (embed ⟨542, by decide⟩) routine542 ∧ planCycles routine542.pieces ≤ rankCost ⟨542, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine542, 84) (by unfold batch67; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready543 : Chain.RoutineReady (embed ⟨543, by decide⟩) routine543 ∧ planCycles routine543.pieces ≤ rankCost ⟨543, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch67_checked (routine543, 81) (by unfold batch67; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check68 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine544 : ChainRoutine := ⟨647, [0x4, 0x0, 0x2, 0x0, 0x0, 0x1], [⟨230400, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230405, [0x750823, 0x73], .rung 1 none⟩, ⟨230407, [0xd50823, 0x73], .rung 2 none⟩, ⟨230409, [0x1350823, 0x73], .rung 3 none⟩, ⟨230411, [0x21040513, 0x24040613, 0xc02f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨230416, [0x1350823, 0x73], .rung 3 none⟩, ⟨230418, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨230422, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨230427, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine545 : ChainRoutine := ⟨648, [0x4, 0x0, 0x2, 0x0, 0x1, 0x0], [⟨230464, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230469, [0x750823, 0x73], .rung 1 none⟩, ⟨230471, [0xd50823, 0x73], .rung 2 none⟩, ⟨230473, [0x1350823, 0x73], .rung 3 none⟩, ⟨230475, [0x21040513, 0x24040613, 0xc02f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨230480, [0x1350823, 0x73], .rung 3 none⟩, ⟨230482, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨230486, [0x1a840513, 0x1d840613, 0xe03f8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨230491, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨230495, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine546 : ChainRoutine := ⟨649, [0x4, 0x0, 0x2, 0x1, 0x0, 0x0], [⟨230528, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230533, [0x750823, 0x73], .rung 1 none⟩, ⟨230535, [0xd50823, 0x73], .rung 2 none⟩, ⟨230537, [0x1350823, 0x73], .rung 3 none⟩, ⟨230539, [0x21040513, 0x24040613, 0xc02f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨230544, [0x1350823, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨230547, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨230552, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨230556, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine547 : ChainRoutine := ⟨650, [0x4, 0x0, 0x3, 0x0, 0x0, 0x0], [⟨230592, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230597, [0x750823, 0x73], .rung 1 none⟩, ⟨230599, [0xd50823, 0x73], .rung 2 none⟩, ⟨230601, [0x1350823, 0x73], .rung 3 none⟩, ⟨230603, [0x21040513, 0x24040613, 0xc01f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨230608, [0xd50823, 0x73], .rung 2 none⟩, ⟨230610, [0x1350823, 0x73], .rung 3 none⟩, ⟨230612, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨230616, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine548 : ChainRoutine := ⟨651, [0x4, 0x1, 0x0, 0x0, 0x0, 0x2], [⟨230656, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230661, [0x750823, 0x73], .rung 1 none⟩, ⟨230663, [0xd50823, 0x73], .rung 2 none⟩, ⟨230665, [0x1350823, 0x73], .rung 3 none⟩, ⟨230667, [0x1f840513, 0x1e840613, 0xb03f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨230672, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨230676, [0x14040513, 0x17040613, 0xf02f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨230681, [0x1350823, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨230684, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine549 : ChainRoutine := ⟨652, [0x4, 0x1, 0x0, 0x0, 0x1, 0x1], [⟨230720, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230725, [0x750823, 0x73], .rung 1 none⟩, ⟨230727, [0xd50823, 0x73], .rung 2 none⟩, ⟨230729, [0x1350823, 0x73], .rung 3 none⟩, ⟨230731, [0x1f840513, 0x1e840613, 0xb03f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨230736, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨230740, [0x1a840513, 0x2e040613, 0xe03f8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨230745, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨230750, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine550 : ChainRoutine := ⟨653, [0x4, 0x1, 0x0, 0x0, 0x2, 0x0], [⟨230784, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230789, [0x750823, 0x73], .rung 1 none⟩, ⟨230791, [0xd50823, 0x73], .rung 2 none⟩, ⟨230793, [0x1350823, 0x73], .rung 3 none⟩, ⟨230795, [0x1f840513, 0x1e840613, 0xb03f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨230800, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨230804, [0x1a840513, 0x1d840613, 0xe02f8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨230809, [0x1350823, 0x73], .rung 3 none⟩, ⟨230811, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨230815, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine551 : ChainRoutine := ⟨654, [0x4, 0x1, 0x0, 0x1, 0x0, 0x1], [⟨230848, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230853, [0x750823, 0x73], .rung 1 none⟩, ⟨230855, [0xd50823, 0x73], .rung 2 none⟩, ⟨230857, [0x1350823, 0x73], .rung 3 none⟩, ⟨230859, [0x1f840513, 0x1e840613, 0xb03f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨230864, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨230868, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨230873, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨230877, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨230882, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch68 : List (ChainRoutine × Nat) := [(routine544, 81), (routine545, 85), (routine546, 82), (routine547, 78), (routine548, 82), (routine549, 84), (routine550, 85), (routine551, 88)]
theorem batch68_checked : (batch68.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready544 : Chain.RoutineReady (embed ⟨544, by decide⟩) routine544 ∧ planCycles routine544.pieces ≤ rankCost ⟨544, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine544, 81) (by unfold batch68; exact List.mem_cons_self)
theorem ready545 : Chain.RoutineReady (embed ⟨545, by decide⟩) routine545 ∧ planCycles routine545.pieces ≤ rankCost ⟨545, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine545, 85) (by unfold batch68; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready546 : Chain.RoutineReady (embed ⟨546, by decide⟩) routine546 ∧ planCycles routine546.pieces ≤ rankCost ⟨546, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine546, 82) (by unfold batch68; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready547 : Chain.RoutineReady (embed ⟨547, by decide⟩) routine547 ∧ planCycles routine547.pieces ≤ rankCost ⟨547, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine547, 78) (by unfold batch68; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready548 : Chain.RoutineReady (embed ⟨548, by decide⟩) routine548 ∧ planCycles routine548.pieces ≤ rankCost ⟨548, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine548, 82) (by unfold batch68; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready549 : Chain.RoutineReady (embed ⟨549, by decide⟩) routine549 ∧ planCycles routine549.pieces ≤ rankCost ⟨549, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine549, 84) (by unfold batch68; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready550 : Chain.RoutineReady (embed ⟨550, by decide⟩) routine550 ∧ planCycles routine550.pieces ≤ rankCost ⟨550, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine550, 85) (by unfold batch68; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready551 : Chain.RoutineReady (embed ⟨551, by decide⟩) routine551 ∧ planCycles routine551.pieces ≤ rankCost ⟨551, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch68_checked (routine551, 88) (by unfold batch68; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check69 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine552 : ChainRoutine := ⟨655, [0x4, 0x1, 0x0, 0x1, 0x1, 0x0], [⟨230912, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230917, [0x750823, 0x73], .rung 1 none⟩, ⟨230919, [0xd50823, 0x73], .rung 2 none⟩, ⟨230921, [0x1350823, 0x73], .rung 3 none⟩, ⟨230923, [0x1f840513, 0x1e840613, 0xb03f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨230928, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨230932, [0x19040513, 0x2d040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨230937, [0x1a840513, 0x1d840613, 0xe03f8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨230942, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨230946, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine553 : ChainRoutine := ⟨656, [0x4, 0x1, 0x0, 0x2, 0x0, 0x0], [⟨230976, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨230981, [0x750823, 0x73], .rung 1 none⟩, ⟨230983, [0xd50823, 0x73], .rung 2 none⟩, ⟨230985, [0x1350823, 0x73], .rung 3 none⟩, ⟨230987, [0x1f840513, 0x1e840613, 0xb03f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨230992, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨230996, [0x19040513, 0x18040613, 0xd02f8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨231001, [0x1350823, 0x73], .rung 3 none⟩, ⟨231003, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨231007, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine554 : ChainRoutine := ⟨657, [0x4, 0x1, 0x1, 0x0, 0x0, 0x1], [⟨231040, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231045, [0x750823, 0x73], .rung 1 none⟩, ⟨231047, [0xd50823, 0x73], .rung 2 none⟩, ⟨231049, [0x1350823, 0x73], .rung 3 none⟩, ⟨231051, [0x1f840513, 0x2b040613, 0xb03f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨231056, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨231061, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨231065, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨231070, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine555 : ChainRoutine := ⟨658, [0x4, 0x1, 0x1, 0x0, 0x1, 0x0], [⟨231104, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231109, [0x750823, 0x73], .rung 1 none⟩, ⟨231111, [0xd50823, 0x73], .rung 2 none⟩, ⟨231113, [0x1350823, 0x73], .rung 3 none⟩, ⟨231115, [0x1f840513, 0x2b040613, 0xb03f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨231120, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨231125, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨231129, [0x1a840513, 0x1d840613, 0xe03f8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨231134, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨231138, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine556 : ChainRoutine := ⟨659, [0x4, 0x1, 0x1, 0x1, 0x0, 0x0], [⟨231168, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231173, [0x750823, 0x73], .rung 1 none⟩, ⟨231175, [0xd50823, 0x73], .rung 2 none⟩, ⟨231177, [0x1350823, 0x73], .rung 3 none⟩, ⟨231179, [0x1f840513, 0x2b040613, 0xb03f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨231184, [0x21040513, 0x2c040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨231189, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨231194, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨231198, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine557 : ChainRoutine := ⟨660, [0x4, 0x1, 0x2, 0x0, 0x0, 0x0], [⟨231232, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231237, [0x750823, 0x73], .rung 1 none⟩, ⟨231239, [0xd50823, 0x73], .rung 2 none⟩, ⟨231241, [0x1350823, 0x73], .rung 3 none⟩, ⟨231243, [0x1f840513, 0x2b040613, 0xb03f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨231248, [0x21040513, 0x24040613, 0xc02f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨231253, [0x1350823, 0x73], .rung 3 none⟩, ⟨231255, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨231259, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine558 : ChainRoutine := ⟨661, [0x4, 0x2, 0x0, 0x0, 0x0, 0x1], [⟨231296, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231301, [0x750823, 0x73], .rung 1 none⟩, ⟨231303, [0xd50823, 0x73], .rung 2 none⟩, ⟨231305, [0x1350823, 0x73], .rung 3 none⟩, ⟨231307, [0x1f840513, 0x1e840613, 0xb02f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨231312, [0x1350823, 0x73], .rung 3 none⟩, ⟨231314, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨231318, [0x14040513, 0x2f040613, 0xf03f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨231323, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine559 : ChainRoutine := ⟨662, [0x4, 0x2, 0x0, 0x0, 0x1, 0x0], [⟨231360, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231365, [0x750823, 0x73], .rung 1 none⟩, ⟨231367, [0xd50823, 0x73], .rung 2 none⟩, ⟨231369, [0x1350823, 0x73], .rung 3 none⟩, ⟨231371, [0x1f840513, 0x1e840613, 0xb02f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨231376, [0x1350823, 0x73], .rung 3 none⟩, ⟨231378, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨231382, [0x1a840513, 0x1d840613, 0xe03f8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨231387, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨231391, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch69 : List (ChainRoutine × Nat) := [(routine552, 88), (routine553, 85), (routine554, 84), (routine555, 88), (routine556, 84), (routine557, 81), (routine558, 81), (routine559, 85)]
theorem batch69_checked : (batch69.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready552 : Chain.RoutineReady (embed ⟨552, by decide⟩) routine552 ∧ planCycles routine552.pieces ≤ rankCost ⟨552, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine552, 88) (by unfold batch69; exact List.mem_cons_self)
theorem ready553 : Chain.RoutineReady (embed ⟨553, by decide⟩) routine553 ∧ planCycles routine553.pieces ≤ rankCost ⟨553, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine553, 85) (by unfold batch69; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready554 : Chain.RoutineReady (embed ⟨554, by decide⟩) routine554 ∧ planCycles routine554.pieces ≤ rankCost ⟨554, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine554, 84) (by unfold batch69; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready555 : Chain.RoutineReady (embed ⟨555, by decide⟩) routine555 ∧ planCycles routine555.pieces ≤ rankCost ⟨555, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine555, 88) (by unfold batch69; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready556 : Chain.RoutineReady (embed ⟨556, by decide⟩) routine556 ∧ planCycles routine556.pieces ≤ rankCost ⟨556, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine556, 84) (by unfold batch69; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready557 : Chain.RoutineReady (embed ⟨557, by decide⟩) routine557 ∧ planCycles routine557.pieces ≤ rankCost ⟨557, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine557, 81) (by unfold batch69; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready558 : Chain.RoutineReady (embed ⟨558, by decide⟩) routine558 ∧ planCycles routine558.pieces ≤ rankCost ⟨558, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine558, 81) (by unfold batch69; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready559 : Chain.RoutineReady (embed ⟨559, by decide⟩) routine559 ∧ planCycles routine559.pieces ≤ rankCost ⟨559, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch69_checked (routine559, 85) (by unfold batch69; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check70 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine560 : ChainRoutine := ⟨663, [0x4, 0x2, 0x0, 0x1, 0x0, 0x0], [⟨231424, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231429, [0x750823, 0x73], .rung 1 none⟩, ⟨231431, [0xd50823, 0x73], .rung 2 none⟩, ⟨231433, [0x1350823, 0x73], .rung 3 none⟩, ⟨231435, [0x1f840513, 0x1e840613, 0xb02f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨231440, [0x1350823, 0x73], .rung 3 none⟩, ⟨231442, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨231446, [0x19040513, 0x18040613, 0xd03f8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨231451, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨231455, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine561 : ChainRoutine := ⟨664, [0x4, 0x2, 0x1, 0x0, 0x0, 0x0], [⟨231488, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231493, [0x750823, 0x73], .rung 1 none⟩, ⟨231495, [0xd50823, 0x73], .rung 2 none⟩, ⟨231497, [0x1350823, 0x73], .rung 3 none⟩, ⟨231499, [0x1f840513, 0x1e840613, 0xb02f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨231504, [0x1350823, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨231507, [0x21040513, 0x24040613, 0xc03f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨231512, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨231516, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine562 : ChainRoutine := ⟨665, [0x4, 0x3, 0x0, 0x0, 0x0, 0x0], [⟨231552, [0x25040513, 0x28040613, 0xa00f8c93, 0x1953823, 0x73], .head 592 640 0 0⟩, ⟨231557, [0x750823, 0x73], .rung 1 none⟩, ⟨231559, [0xd50823, 0x73], .rung 2 none⟩, ⟨231561, [0x1350823, 0x73], .rung 3 none⟩, ⟨231563, [0x1f840513, 0x1e840613, 0xb01f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨231568, [0xd50823, 0x73], .rung 2 none⟩, ⟨231570, [0x1350823, 0x73], .rung 3 none⟩, ⟨231572, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨231576, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
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
end
-- ==== merged from W9Machine_WctSourceEquiv ====
section

namespace W9Machine.V3SourceEquiv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M publicHash shortHash header)
open W9Machine W9Machine.Chain
theorem traceProgram_append (b : ChainWord → Word) (qs₁ qs₂ : List (List ChainWord))
    (as : List (BitVec 256)) :
    traceProgram b (qs₁ ++ qs₂) as = traceProgram b qs₁ as >>= fun as' => traceProgram b qs₂ as' := by
  induction qs₁ generalizing as with
  | nil => simp only [List.nil_append, traceProgram, pure_bind]
  | cons q qs ih => simp only [List.cons_append, traceProgram, ih, bind_assoc]
theorem sum_take_succ (l : List Nat) (t : Nat) :
    (l.take (t + 1)).sum = (l.take t).sum + l.getD t 0 := by
  induction l generalizing t with
  | nil => simp
  | cons x xs ih =>
    cases t with
    | zero => simp
    | succ t => simp only [List.take_succ_cons, List.sum_cons, ih, List.getD_cons_succ]; omega
theorem extract_lo (x : BitVec 256) :
    (x.extractLsb' 0 128).extractLsb' 0 64 = x.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
theorem extract_hi (x : BitVec 256) :
    (x.extractLsb' 0 128).extractLsb' 64 64 = x.extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem extract_hh_lo (x : BitVec 256) :
    (x.extractLsb' 128 128).extractLsb' 0 64 = x.extractLsb' 128 64 := by
  ext i hi
  have h : i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', Nat.zero_add, h, decide_true, Bool.true_and]
theorem extract_hh_hi (x : BitVec 256) :
    (x.extractLsb' 128 128).extractLsb' 64 64 = x.extractLsb' 192 64 := by
  ext i hi
  have h : 64 + i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and]
  rw [show 128 + (64 + i) = 192 + i by omega]
theorem projHash_def (high : Bool) (x : List UInt8) :
    SigGolfCandidate.T3.projHash high x =
      publicHash x >>= fun a => pure (SigGolfCandidate.T3.projHalf high a) := rfl
theorem orig_word {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (off : Nat)
    (ho : off < 848) (ha : off % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original off) =
      w.extractLsb' (8 * (V3.regionOffset k.val + off)) 64 := by
  exact hu.witness off ho ha
theorem ftsOff_bound (t : Nat) (ht : t < 6) : ftsOff t ≤ 592 ∧ ftsOff t % 8 = 0 := by
  unfold ftsOff ClaudeWCT.W9.T3M.wctChainOff
  split_ifs <;> omega
/-- A word of chain `t`'s 64-byte block, as the (possibly digested) witness word. -/
theorem orig_block {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (t c : Nat)
    (ht : t < 6) (hc : c < 64) (ha : c % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original (ftsOff t + c)) =
      w.extractLsb' (8 * (V3.chainOffset k.val t + c)) 64 := by
  have hb := ftsOff_bound t ht
  rw [orig_word hu as _ (by omega) (by omega)]
  simp only [V3.chainOffset, ftsOff, Nat.add_assoc]
theorem orig_lo {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (t c : Nat)
    (ht : t < 6) (hc : c + 16 ≤ 64) (ha : c % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original (ftsOff t + c)) =
      (wdig w (V3.chainOffset k.val t + c)).extractLsb' 0 64 := by
  rw [W9Machine.wdig_lo]; exact orig_block hu as t c ht (by omega) ha
theorem orig_hi {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (t c : Nat)
    (ht : t < 6) (hc : c + 16 ≤ 64) (ha : c % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original (ftsOff t + (c + 8))) =
      (wdig w (V3.chainOffset k.val t + c)).extractLsb' 64 64 := by
  rw [W9Machine.wdig_hi, Nat.add_assoc]; exact orig_block hu as t (c + 8) ht (by omega) (by omega)
/-- The value carried into step `s` of chain `t`: the revealed witness value at `s = 0`, otherwise the kept half of
the previous answer (high for interior G steps). -/
def stepValue (w : WBytes) (k : Fin 9) (digits : List Nat) (t s : Nat) (as : List (BitVec 256)) : Digest :=
  if s = 0 then V3.reveal w k.val t (digits.getD t 0)
  else SigGolfCandidate.T3.projHalf (ClaudeWCT.WCT9.ftsChainHigh t (4 - digits.getD t 0 + s - 1))
    (as.getD ((digits.take t).sum + s - 1) 0)
theorem query_bytes {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (digits : List Nat) (t s : Nat)
    (ht : t < 6) (hd4 : digits.getD t 0 ≤ 4) (hs : s < digits.getD t 0) (as : List (BitVec 256)) (v : Digest)
    (hv : v = stepValue w k digits t s as) :
    wordBytes ((chainQueryWords digits t s).map (chainValue (originalValue L u index k j) as)) =
      V3.chainInput index k.val j.val t (4 - digits.getD t 0 + s)
        (V3.chainPadA w k.val t) (V3.chainPadB w k.val t) (V3.chainPadC w k.val t) v := by
  rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
    (chainInput_length _ _ _ _ _ _ _ _ _), wordsOf_chainInput]
  congr 1
  have hd : digits.getD t 0 ≠ 0 := by omega
  have hB : V3.chainPadB w k.val t = chainValue (originalValue L u index k j) as (.original (ftsOff t + 24)) :=
    (orig_block hu as t 24 ht (by decide) (by decide)).symm
  by_cases hG : ClaudeWCT.WCT9.ftsIsG t = true
  · -- G: `value | header | a | c`, interior values are high halves
    have hA : V3.chainPadA w k.val t = wdig w (V3.chainOffset k.val t + 32) := by
      simp only [V3.chainPadA, ClaudeWCT.W9.T3M.wctPad0Off, hG, eq_self_iff_true, if_true, ↓reduceIte]
    have hC : V3.chainPadC w k.val t = wdig w (V3.chainOffset k.val t + 48) := by
      simp only [V3.chainPadC, ClaudeWCT.W9.T3M.wctPad1Off, hG, eq_self_iff_true, if_true, ↓reduceIte]
    have hlo : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t) else .answer ((digits.take t).sum + s - 1) 2) = v.extractLsb' 0 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_pos hG]
        exact orig_lo hu as t 0 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, (ClaudeWCT.WCT9.ftsChainHigh_eq_true (i := t)
          (step := 4 - digits.getD t 0 + s - 1)).mpr ⟨ClaudeWCT.WCT9.ftsIsG_eq_true.mp hG, by omega⟩, SigGolfCandidate.T3.projHalf_true, extract_hh_lo]
        rfl
    have hhi : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t + 8) else .answer ((digits.take t).sum + s - 1) 3) =
          v.extractLsb' 64 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_pos hG]
        exact orig_hi hu as t 0 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, (ClaudeWCT.WCT9.ftsChainHigh_eq_true (i := t)
          (step := 4 - digits.getD t 0 + s - 1)).mpr ⟨ClaudeWCT.WCT9.ftsIsG_eq_true.mp hG, by omega⟩, SigGolfCandidate.T3.projHalf_true, extract_hh_hi]
        rfl
    rw [if_pos hG, hA, hC, hB]
    simp only [chainQueryWords, hG, eq_self_iff_true, if_true, ↓reduceIte, List.map_cons, List.map_nil]
    rw [hlo, hhi, orig_lo hu as t 32 ht (by decide) (by decide),
      orig_lo hu as t 48 ht (by decide) (by decide),
      ← orig_hi hu as t 32 ht (by decide) (by decide), ← orig_hi hu as t 48 ht (by decide) (by decide)]
    rfl
  · -- F: `a | header | c | value`, every value is a low half
    have hF : ClaudeWCT.WCT9.ftsIsG t = false := by simpa using hG
    have hA : V3.chainPadA w k.val t = wdig w (V3.chainOffset k.val t + 0) := by
      simp only [V3.chainPadA, ClaudeWCT.W9.T3M.wctPad0Off, hF, Bool.false_eq_true, if_false, ↓reduceIte]
    have hC : V3.chainPadC w k.val t = wdig w (V3.chainOffset k.val t + 32) := by
      simp only [V3.chainPadC, ClaudeWCT.W9.T3M.wctPad1Off, hF, Bool.false_eq_true, if_false, ↓reduceIte]
    have hlo : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t + 48) else .answer ((digits.take t).sum + s - 1) 0) =
          v.extractLsb' 0 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_neg hG]
        exact orig_lo hu as t 48 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, ClaudeWCT.WCT9.ftsChainHigh_of_F hF, SigGolfCandidate.T3.projHalf_false,
          extract_lo]
        rfl
    have hhi : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t + 56) else .answer ((digits.take t).sum + s - 1) 1) =
          v.extractLsb' 64 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_neg hG]
        exact orig_hi hu as t 48 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, ClaudeWCT.WCT9.ftsChainHigh_of_F hF, SigGolfCandidate.T3.projHalf_false,
          extract_hi]
        rfl
    rw [if_neg hG, hA, hC, hB]
    simp only [chainQueryWords, hF, Bool.false_eq_true, if_false, ↓reduceIte, List.map_cons, List.map_nil]
    rw [hlo, hhi, ← orig_lo hu as t 0 ht (by decide) (by decide),
      ← orig_hi hu as t 0 ht (by decide) (by decide),
      ← orig_lo hu as t 32 ht (by decide) (by decide), ← orig_hi hu as t 32 ht (by decide) (by decide)]
    rfl
theorem sum_take_mono (l : List Nat) (a c : Nat) : (l.take a).sum ≤ (l.take (a + c)).sum := by
  induction c with
  | zero => exact le_refl _
  | succ c ih => rw [← Nat.add_assoc, sum_take_succ]; omega
theorem chain_cps {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (digits : List Nat) (t : Nat) (ht : t < 6)
    (hd4 : digits.getD t 0 ≤ 4)
    {β : Type} (r : Nat) : ∀ (s : Nat) (as : List (BitVec 256)) (v : Digest)
      (K : List (BitVec 256) → M β) (Kv : Digest → M β),
    s + r = digits.getD t 0 → as.length = (digits.take t).sum + s →
    v = stepValue w k digits t s as →
    (∀ new : List (BitVec 256), new.length = r →
      K (as ++ new) = Kv (if r = 0 then v else SigGolfCandidate.T3.projHalf
        (ClaudeWCT.WCT9.ftsChainHigh t (4 - digits.getD t 0 + s + r - 1)) (new.getD (r - 1) 0))) →
    (traceProgram (originalValue L u index k j) ((List.range' s r).map (chainQueryWords digits t)) as
        >>= K) =
      ((List.range' (4 - digits.getD t 0 + s) r).foldlM
        (fun value step => SigGolfCandidate.T3.projHash (ClaudeWCT.WCT9.ftsChainHigh t step)
          (V3.chainInput index k.val j.val t step
            (V3.chainPadA w k.val t) (V3.chainPadB w k.val t) (V3.chainPadC w k.val t) value)) v
        >>= Kv) := by
  induction r with
  | zero =>
    intro s as v K Kv _ _ _ hK
    simp only [List.range'_zero, List.map_nil, traceProgram, List.foldlM_nil, pure_bind]
    simpa using hK [] rfl
  | succ r ih =>
    intro s as v K Kv hsr hlen hv hK
    rw [List.range'_succ, List.map_cons, List.range'_succ, List.foldlM_cons]
    simp only [traceProgram, bind_assoc]
    rw [query_bytes hu digits t s ht hd4 (by omega) as v hv, projHash_def, bind_assoc]
    simp only [pure_bind]
    refine congrArg (publicHash _ >>= ·) (funext fun ans => ?_)
    rw [show 4 - digits.getD t 0 + s + 1 = 4 - digits.getD t 0 + (s + 1) by omega]
    refine ih (s + 1) (as ++ [ans]) _ K Kv (by omega) (by simp [hlen]; omega) ?_ ?_
    · rw [stepValue, if_neg (by omega), show (digits.take t).sum + (s + 1) - 1 = as.length by omega,
        List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
        show 4 - digits.getD t 0 + (s + 1) - 1 = 4 - digits.getD t 0 + s by omega]
      rfl
    · intro new hnew
      rw [List.append_assoc, List.singleton_append, hK (ans :: new) (by simp [hnew])]
      congr 1
      cases r with
      | zero =>
        rw [if_pos rfl, if_neg (by omega), show 4 - digits.getD t 0 + s + (0 + 1) - 1 =
          4 - digits.getD t 0 + s by omega]
        rfl
      | succ r =>
        rw [if_neg (by omega), if_neg (by omega), show 4 - digits.getD t 0 + s + (r + 1 + 1) - 1 =
          4 - digits.getD t 0 + (s + 1) + (r + 1) - 1 by omega]
        rfl
def endOf (w : WBytes) (k : Fin 9) (digits : List Nat) (as : List (BitVec 256)) (t : Nat) :
    Digest :=
  if digits.getD t 0 = 0 then wdig w (V3.regionOffset k.val + V3.leafSlot t)
  else (as.getD ((digits.take (t + 1)).sum - 1) 0).extractLsb' 0 128
def chainProg (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (digits : List Nat) (t : Nat) :
    M Digest :=
  V3.chainP index k.val j.val t (4 - digits.getD t 0) (digits.getD t 0)
    (V3.chainPadA w k.val t) (V3.chainPadB w k.val t) (V3.chainPadC w k.val t)
    (V3.reveal w k.val t (digits.getD t 0))
def chainQs (digits : List Nat) (t : Nat) : List (List ChainWord) :=
  (List.range (digits.getD t 0)).map (chainQueryWords digits t)
theorem outer_cps {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (digits : List Nat)
    (hdig : ∀ t, t < 6 → digits.getD t 0 ≤ 4) (m : Nat) :
    ∀ (t : Nat) (as : List (BitVec 256)) (acc : List Digest),
    t + m = 6 → as.length = (digits.take t).sum → acc.length = t →
    (∀ i, i < t → acc.getD i 0 = endOf w k digits as i) →
    (traceProgram (originalValue L u index k j) ((List.range' t m).flatMap (chainQs digits)) as
        >>= fun as' => pure ((List.finRange 6).map fun i => endOf w k digits as' i.val)) =
      ((List.range' t m).mapM (chainProg w index k j digits) >>= fun vs => pure (acc ++ vs)) := by
  induction m with
  | zero =>
    intro t as acc htm hlen hacc hE
    simp only [List.range'_zero, List.flatMap_nil, traceProgram, pure_bind, List.mapM_nil,
      List.append_nil]
    congr 1
    apply List.ext_getElem
    · simp [hacc]; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      rw [← hE i (by omega), List.getD_eq_getElem _ _ h2]
  | succ m ih =>
    intro t as acc htm hlen hacc hE
    rw [List.range'_succ, List.flatMap_cons, List.mapM_cons, traceProgram_append, bind_assoc]
    simp only [bind_assoc, pure_bind]
    unfold chainQs chainProg
    rw [List.range_eq_range', V3.chainP]
    refine chain_cps hu digits t (by omega) (hdig t (by omega)) (digits.getD t 0) 0 as _ _ _ (by omega)
      (by simpa using hlen) (by simp [stepValue]) ?_
    intro new hnew
    rw [show 4 - digits.getD t 0 + 0 + digits.getD t 0 - 1 = 3 by have := hdig t (by omega); omega,
      ClaudeWCT.WCT9.ftsChainHigh_three, SigGolfCandidate.T3.projHalf_false]
    refine (ih (t + 1) (as ++ new) (acc ++ [if digits.getD t 0 = 0 then
        V3.reveal w k.val t (digits.getD t 0)
        else (new.getD (digits.getD t 0 - 1) 0).extractLsb' 0 128]) (by omega)
        (by rw [sum_take_succ]; simp [hlen, hnew]) (by simp [hacc]) ?_).trans ?_
    · intro i hi
      by_cases hit : i < t
      · rw [List.getD_append _ _ _ _ (by omega), hE i hit]
        unfold endOf
        split_ifs with hd
        · rfl
        · have h1 := sum_take_succ digits i
          have h2 := sum_take_mono digits (i + 1) (t - (i + 1))
          rw [show i + 1 + (t - (i + 1)) = t by omega] at h2
          rw [List.getD_append _ _ _ _ (by omega)]
      · have hit : i = t := by omega
        subst hit
        rw [List.getD_append_right _ _ _ _ (by omega), hacc, Nat.sub_self]
        unfold endOf
        split_ifs with hd
        · simp only [List.getD_cons_zero, V3.reveal, if_pos hd]
        · have h1 := sum_take_succ digits i
          rw [List.getD_append_right _ _ _ _ (by omega)]
          simp only [List.getD_cons_zero]
          congr 2
          omega
    · simp only [List.append_assoc, List.singleton_append]
      rfl
theorem sourceEquivalent : W9Machine.Chain.SourceEquivalent := by
  intro L w index k j rank u hu
  have h := outer_cps hu (ClaudeWCT.WCT9.codeword rank)
    (fun t ht => ClaudeWCT.WCT9.digit_le_four rank ⟨t, ht⟩) 6 0 [] [] rfl rfl rfl
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  have hq : expectedQueries (ClaudeWCT.WCT9.codeword rank) =
      (List.range' 0 6).flatMap (chainQs (ClaudeWCT.WCT9.codeword rank)) := by
    rw [expectedQueries, List.range_eq_range']
    rfl
  have hp : program w index k j rank =
      (List.range' 0 6).mapM (chainProg w index k j (ClaudeWCT.WCT9.codeword rank)) := rfl
  rw [hq, hp]
  refine h.trans ?_
  simp only [List.nil_append, bind_pure]
end W9Machine.V3SourceEquiv
end
-- ==== merged from W9Machine_WctEndpoints ====
section

namespace W9Machine.V3Endpoints
open W9Machine W9Machine.Chain
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem extract_lo (X : BitVec 256) :
    (X.extractLsb' 0 128).extractLsb' 0 64 = X.extractLsb' 0 64 := by
  ext i hi
  have h : i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', Nat.zero_add, h,
    decide_true, Bool.true_and]
theorem extract_hi (X : BitVec 256) :
    (X.extractLsb' 0 128).extractLsb' 64 64 = X.extractLsb' 64 64 := by
  ext i hi
  have h : 64 + i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', h, decide_true,
    Bool.true_and, Nat.zero_add]
theorem traceLeafSlot_bound (t : Nat) (ht : t < 6) :
    traceLeafSlot t + 16 ≤ 768 ∧ traceLeafSlot t % 8 = 0 := by
  unfold traceLeafSlot; split <;> omega
theorem sourceEnds_getD (w : WBytes) (k : Fin 9) (rank : Fin 666)
    (answers : List (BitVec 256)) (t : Nat) (ht : t < 6) :
    (sourceEnds w k rank answers).getD t 0 =
      if (ClaudeWCT.WCT9.codeword rank).getD t 0 = 0 then wdig w (V3.regionOffset k.val + V3.leafSlot t)
      else (answers.getD (((ClaudeWCT.WCT9.codeword rank).take (t + 1)).sum - 1) 0).extractLsb'
        0 128 := by
  unfold sourceEnds
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa only [List.length_finRange] using ht)]
  simp only [Option.map_some, Option.getD_some, List.getElem_finRange, Fin.cast_mk]
theorem endpointsCorrect : W9Machine.Chain.EndpointsCorrect := by
  intro L w index k j rank u s tr answers hu hs hend t ht
  have hb := traceLeafSlot_bound t ht
  have hmem : ∀ word, word < 2 →
      s.getMem (BitVec.ofNat 64 (base L k + traceLeafSlot t + 8 * word)) =
        chainValue (originalValue L u index k j) answers
          (expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word) := by
    intro word hw
    rw [Nat.add_assoc, hs.memory _ (by omega), hend t ht word hw]
  have h0 := hmem 0 (by decide)
  have h1 := hmem 1 (by decide)
  rw [sourceEnds_getD w k rank answers t ht]
  unfold expectedEndpoint at h0 h1
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  split_ifs at h0 h1 ⊢ with hd
  · simp only [chainValue, originalValue] at h0 h1
    have hw0 : OrigWD L.shift w s (base L k + traceLeafSlot t) :=
      h0.trans (hu.origW _ (by omega) hb.2)
    have hw1 : OrigWD L.shift w s (base L k + traceLeafSlot t + 8) := by
      have := hu.origW (traceLeafSlot t + 8) (by omega) (by omega)
      rw [← Nat.add_assoc] at this
      exact h1.trans this
    have hdig := DigAt_origWD hw0 hw1 (by unfold base coordinateBase Layout.shift; omega)
    have he : base L k + traceLeafSlot t + L.shift - 0x10A0 = V3.regionOffset k.val + V3.leafSlot t := by
      unfold base coordinateBase Layout.shift traceLeafSlot V3.leafSlot V3.regionOffset
      split <;> omega
    rw [he] at hdig
    exact hdig
  · simp only [chainValue, Nat.mul_zero, Nat.mul_one] at h0 h1
    exact ⟨h0.trans (extract_lo _).symm, h1.trans (extract_hi _).symm⟩
end W9Machine.V3Endpoints
end
-- ==== merged from W9Machine_WctChainCertified ====
section

namespace W9Machine.N600
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
theorem bank_contained_of_all (r : ChainRoutine)
    (h : (r.pieces.all fun p => decide (195584 ≤ p.pc ∧ p.pc + p.words.length ≤ 254656)) = true) :
    ∀ p ∈ r.pieces, 195584 ≤ p.pc ∧ p.pc + p.words.length ≤ 254656 := by
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)
theorem allCertified_inSharedBank : ∀ rank : Fin 563, ∃ r : ChainRoutine,
    Chain.RoutineReady (embed rank) r ∧
    planCycles r.pieces ≤ rankCost rank ∧
    ∀ p ∈ r.pieces, 195584 ≤ p.pc ∧ p.pc + p.words.length ≤ 254656 := by
  intro rank
  by_cases h0 : rank.val < 281
  ·
    by_cases h1 : rank.val < 140
    ·
      by_cases h2 : rank.val < 70
      ·
        by_cases h3 : rank.val < 35
        ·
          by_cases h4 : rank.val < 17
          ·
            by_cases h5 : rank.val < 8
            ·
              by_cases h6 : rank.val < 4
              ·
                by_cases h7 : rank.val < 2
                ·
                  by_cases h8 : rank.val < 1
                  ·
                    have hr : rank = ⟨0, by decide⟩ := Fin.ext (by change rank.val = 0; omega)
                    subst rank
                    exact ⟨Checks.routine0, Checks.ready0.1, Checks.ready0.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨1, by decide⟩ := Fin.ext (by change rank.val = 1; omega)
                    subst rank
                    exact ⟨Checks.routine1, Checks.ready1.1, Checks.ready1.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h9 : rank.val < 3
                  ·
                    have hr : rank = ⟨2, by decide⟩ := Fin.ext (by change rank.val = 2; omega)
                    subst rank
                    exact ⟨Checks.routine2, Checks.ready2.1, Checks.ready2.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨3, by decide⟩ := Fin.ext (by change rank.val = 3; omega)
                    subst rank
                    exact ⟨Checks.routine3, Checks.ready3.1, Checks.ready3.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h10 : rank.val < 6
                ·
                  by_cases h11 : rank.val < 5
                  ·
                    have hr : rank = ⟨4, by decide⟩ := Fin.ext (by change rank.val = 4; omega)
                    subst rank
                    exact ⟨Checks.routine4, Checks.ready4.1, Checks.ready4.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨5, by decide⟩ := Fin.ext (by change rank.val = 5; omega)
                    subst rank
                    exact ⟨Checks.routine5, Checks.ready5.1, Checks.ready5.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h12 : rank.val < 7
                  ·
                    have hr : rank = ⟨6, by decide⟩ := Fin.ext (by change rank.val = 6; omega)
                    subst rank
                    exact ⟨Checks.routine6, Checks.ready6.1, Checks.ready6.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨7, by decide⟩ := Fin.ext (by change rank.val = 7; omega)
                    subst rank
                    exact ⟨Checks.routine7, Checks.ready7.1, Checks.ready7.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h13 : rank.val < 12
              ·
                by_cases h14 : rank.val < 10
                ·
                  by_cases h15 : rank.val < 9
                  ·
                    have hr : rank = ⟨8, by decide⟩ := Fin.ext (by change rank.val = 8; omega)
                    subst rank
                    exact ⟨Checks.routine8, Checks.ready8.1, Checks.ready8.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨9, by decide⟩ := Fin.ext (by change rank.val = 9; omega)
                    subst rank
                    exact ⟨Checks.routine9, Checks.ready9.1, Checks.ready9.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h16 : rank.val < 11
                  ·
                    have hr : rank = ⟨10, by decide⟩ := Fin.ext (by change rank.val = 10; omega)
                    subst rank
                    exact ⟨Checks.routine10, Checks.ready10.1, Checks.ready10.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨11, by decide⟩ := Fin.ext (by change rank.val = 11; omega)
                    subst rank
                    exact ⟨Checks.routine11, Checks.ready11.1, Checks.ready11.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h17 : rank.val < 14
                ·
                  by_cases h18 : rank.val < 13
                  ·
                    have hr : rank = ⟨12, by decide⟩ := Fin.ext (by change rank.val = 12; omega)
                    subst rank
                    exact ⟨Checks.routine12, Checks.ready12.1, Checks.ready12.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨13, by decide⟩ := Fin.ext (by change rank.val = 13; omega)
                    subst rank
                    exact ⟨Checks.routine13, Checks.ready13.1, Checks.ready13.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h19 : rank.val < 15
                  ·
                    have hr : rank = ⟨14, by decide⟩ := Fin.ext (by change rank.val = 14; omega)
                    subst rank
                    exact ⟨Checks.routine14, Checks.ready14.1, Checks.ready14.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h20 : rank.val < 16
                    ·
                      have hr : rank = ⟨15, by decide⟩ := Fin.ext (by change rank.val = 15; omega)
                      subst rank
                      exact ⟨Checks.routine15, Checks.ready15.1, Checks.ready15.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨16, by decide⟩ := Fin.ext (by change rank.val = 16; omega)
                      subst rank
                      exact ⟨Checks.routine16, Checks.ready16.1, Checks.ready16.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h21 : rank.val < 26
            ·
              by_cases h22 : rank.val < 21
              ·
                by_cases h23 : rank.val < 19
                ·
                  by_cases h24 : rank.val < 18
                  ·
                    have hr : rank = ⟨17, by decide⟩ := Fin.ext (by change rank.val = 17; omega)
                    subst rank
                    exact ⟨Checks.routine17, Checks.ready17.1, Checks.ready17.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨18, by decide⟩ := Fin.ext (by change rank.val = 18; omega)
                    subst rank
                    exact ⟨Checks.routine18, Checks.ready18.1, Checks.ready18.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h25 : rank.val < 20
                  ·
                    have hr : rank = ⟨19, by decide⟩ := Fin.ext (by change rank.val = 19; omega)
                    subst rank
                    exact ⟨Checks.routine19, Checks.ready19.1, Checks.ready19.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨20, by decide⟩ := Fin.ext (by change rank.val = 20; omega)
                    subst rank
                    exact ⟨Checks.routine20, Checks.ready20.1, Checks.ready20.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h26 : rank.val < 23
                ·
                  by_cases h27 : rank.val < 22
                  ·
                    have hr : rank = ⟨21, by decide⟩ := Fin.ext (by change rank.val = 21; omega)
                    subst rank
                    exact ⟨Checks.routine21, Checks.ready21.1, Checks.ready21.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨22, by decide⟩ := Fin.ext (by change rank.val = 22; omega)
                    subst rank
                    exact ⟨Checks.routine22, Checks.ready22.1, Checks.ready22.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h28 : rank.val < 24
                  ·
                    have hr : rank = ⟨23, by decide⟩ := Fin.ext (by change rank.val = 23; omega)
                    subst rank
                    exact ⟨Checks.routine23, Checks.ready23.1, Checks.ready23.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h29 : rank.val < 25
                    ·
                      have hr : rank = ⟨24, by decide⟩ := Fin.ext (by change rank.val = 24; omega)
                      subst rank
                      exact ⟨Checks.routine24, Checks.ready24.1, Checks.ready24.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨25, by decide⟩ := Fin.ext (by change rank.val = 25; omega)
                      subst rank
                      exact ⟨Checks.routine25, Checks.ready25.1, Checks.ready25.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h30 : rank.val < 30
              ·
                by_cases h31 : rank.val < 28
                ·
                  by_cases h32 : rank.val < 27
                  ·
                    have hr : rank = ⟨26, by decide⟩ := Fin.ext (by change rank.val = 26; omega)
                    subst rank
                    exact ⟨Checks.routine26, Checks.ready26.1, Checks.ready26.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨27, by decide⟩ := Fin.ext (by change rank.val = 27; omega)
                    subst rank
                    exact ⟨Checks.routine27, Checks.ready27.1, Checks.ready27.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h33 : rank.val < 29
                  ·
                    have hr : rank = ⟨28, by decide⟩ := Fin.ext (by change rank.val = 28; omega)
                    subst rank
                    exact ⟨Checks.routine28, Checks.ready28.1, Checks.ready28.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨29, by decide⟩ := Fin.ext (by change rank.val = 29; omega)
                    subst rank
                    exact ⟨Checks.routine29, Checks.ready29.1, Checks.ready29.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h34 : rank.val < 32
                ·
                  by_cases h35 : rank.val < 31
                  ·
                    have hr : rank = ⟨30, by decide⟩ := Fin.ext (by change rank.val = 30; omega)
                    subst rank
                    exact ⟨Checks.routine30, Checks.ready30.1, Checks.ready30.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨31, by decide⟩ := Fin.ext (by change rank.val = 31; omega)
                    subst rank
                    exact ⟨Checks.routine31, Checks.ready31.1, Checks.ready31.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h36 : rank.val < 33
                  ·
                    have hr : rank = ⟨32, by decide⟩ := Fin.ext (by change rank.val = 32; omega)
                    subst rank
                    exact ⟨Checks.routine32, Checks.ready32.1, Checks.ready32.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h37 : rank.val < 34
                    ·
                      have hr : rank = ⟨33, by decide⟩ := Fin.ext (by change rank.val = 33; omega)
                      subst rank
                      exact ⟨Checks.routine33, Checks.ready33.1, Checks.ready33.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨34, by decide⟩ := Fin.ext (by change rank.val = 34; omega)
                      subst rank
                      exact ⟨Checks.routine34, Checks.ready34.1, Checks.ready34.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h38 : rank.val < 52
          ·
            by_cases h39 : rank.val < 43
            ·
              by_cases h40 : rank.val < 39
              ·
                by_cases h41 : rank.val < 37
                ·
                  by_cases h42 : rank.val < 36
                  ·
                    have hr : rank = ⟨35, by decide⟩ := Fin.ext (by change rank.val = 35; omega)
                    subst rank
                    exact ⟨Checks.routine35, Checks.ready35.1, Checks.ready35.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨36, by decide⟩ := Fin.ext (by change rank.val = 36; omega)
                    subst rank
                    exact ⟨Checks.routine36, Checks.ready36.1, Checks.ready36.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h43 : rank.val < 38
                  ·
                    have hr : rank = ⟨37, by decide⟩ := Fin.ext (by change rank.val = 37; omega)
                    subst rank
                    exact ⟨Checks.routine37, Checks.ready37.1, Checks.ready37.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨38, by decide⟩ := Fin.ext (by change rank.val = 38; omega)
                    subst rank
                    exact ⟨Checks.routine38, Checks.ready38.1, Checks.ready38.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h44 : rank.val < 41
                ·
                  by_cases h45 : rank.val < 40
                  ·
                    have hr : rank = ⟨39, by decide⟩ := Fin.ext (by change rank.val = 39; omega)
                    subst rank
                    exact ⟨Checks.routine39, Checks.ready39.1, Checks.ready39.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨40, by decide⟩ := Fin.ext (by change rank.val = 40; omega)
                    subst rank
                    exact ⟨Checks.routine40, Checks.ready40.1, Checks.ready40.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h46 : rank.val < 42
                  ·
                    have hr : rank = ⟨41, by decide⟩ := Fin.ext (by change rank.val = 41; omega)
                    subst rank
                    exact ⟨Checks.routine41, Checks.ready41.1, Checks.ready41.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨42, by decide⟩ := Fin.ext (by change rank.val = 42; omega)
                    subst rank
                    exact ⟨Checks.routine42, Checks.ready42.1, Checks.ready42.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h47 : rank.val < 47
              ·
                by_cases h48 : rank.val < 45
                ·
                  by_cases h49 : rank.val < 44
                  ·
                    have hr : rank = ⟨43, by decide⟩ := Fin.ext (by change rank.val = 43; omega)
                    subst rank
                    exact ⟨Checks.routine43, Checks.ready43.1, Checks.ready43.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨44, by decide⟩ := Fin.ext (by change rank.val = 44; omega)
                    subst rank
                    exact ⟨Checks.routine44, Checks.ready44.1, Checks.ready44.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h50 : rank.val < 46
                  ·
                    have hr : rank = ⟨45, by decide⟩ := Fin.ext (by change rank.val = 45; omega)
                    subst rank
                    exact ⟨Checks.routine45, Checks.ready45.1, Checks.ready45.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨46, by decide⟩ := Fin.ext (by change rank.val = 46; omega)
                    subst rank
                    exact ⟨Checks.routine46, Checks.ready46.1, Checks.ready46.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h51 : rank.val < 49
                ·
                  by_cases h52 : rank.val < 48
                  ·
                    have hr : rank = ⟨47, by decide⟩ := Fin.ext (by change rank.val = 47; omega)
                    subst rank
                    exact ⟨Checks.routine47, Checks.ready47.1, Checks.ready47.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨48, by decide⟩ := Fin.ext (by change rank.val = 48; omega)
                    subst rank
                    exact ⟨Checks.routine48, Checks.ready48.1, Checks.ready48.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h53 : rank.val < 50
                  ·
                    have hr : rank = ⟨49, by decide⟩ := Fin.ext (by change rank.val = 49; omega)
                    subst rank
                    exact ⟨Checks.routine49, Checks.ready49.1, Checks.ready49.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h54 : rank.val < 51
                    ·
                      have hr : rank = ⟨50, by decide⟩ := Fin.ext (by change rank.val = 50; omega)
                      subst rank
                      exact ⟨Checks.routine50, Checks.ready50.1, Checks.ready50.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨51, by decide⟩ := Fin.ext (by change rank.val = 51; omega)
                      subst rank
                      exact ⟨Checks.routine51, Checks.ready51.1, Checks.ready51.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h55 : rank.val < 61
            ·
              by_cases h56 : rank.val < 56
              ·
                by_cases h57 : rank.val < 54
                ·
                  by_cases h58 : rank.val < 53
                  ·
                    have hr : rank = ⟨52, by decide⟩ := Fin.ext (by change rank.val = 52; omega)
                    subst rank
                    exact ⟨Checks.routine52, Checks.ready52.1, Checks.ready52.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨53, by decide⟩ := Fin.ext (by change rank.val = 53; omega)
                    subst rank
                    exact ⟨Checks.routine53, Checks.ready53.1, Checks.ready53.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h59 : rank.val < 55
                  ·
                    have hr : rank = ⟨54, by decide⟩ := Fin.ext (by change rank.val = 54; omega)
                    subst rank
                    exact ⟨Checks.routine54, Checks.ready54.1, Checks.ready54.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨55, by decide⟩ := Fin.ext (by change rank.val = 55; omega)
                    subst rank
                    exact ⟨Checks.routine55, Checks.ready55.1, Checks.ready55.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h60 : rank.val < 58
                ·
                  by_cases h61 : rank.val < 57
                  ·
                    have hr : rank = ⟨56, by decide⟩ := Fin.ext (by change rank.val = 56; omega)
                    subst rank
                    exact ⟨Checks.routine56, Checks.ready56.1, Checks.ready56.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨57, by decide⟩ := Fin.ext (by change rank.val = 57; omega)
                    subst rank
                    exact ⟨Checks.routine57, Checks.ready57.1, Checks.ready57.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h62 : rank.val < 59
                  ·
                    have hr : rank = ⟨58, by decide⟩ := Fin.ext (by change rank.val = 58; omega)
                    subst rank
                    exact ⟨Checks.routine58, Checks.ready58.1, Checks.ready58.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h63 : rank.val < 60
                    ·
                      have hr : rank = ⟨59, by decide⟩ := Fin.ext (by change rank.val = 59; omega)
                      subst rank
                      exact ⟨Checks.routine59, Checks.ready59.1, Checks.ready59.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨60, by decide⟩ := Fin.ext (by change rank.val = 60; omega)
                      subst rank
                      exact ⟨Checks.routine60, Checks.ready60.1, Checks.ready60.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h64 : rank.val < 65
              ·
                by_cases h65 : rank.val < 63
                ·
                  by_cases h66 : rank.val < 62
                  ·
                    have hr : rank = ⟨61, by decide⟩ := Fin.ext (by change rank.val = 61; omega)
                    subst rank
                    exact ⟨Checks.routine61, Checks.ready61.1, Checks.ready61.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨62, by decide⟩ := Fin.ext (by change rank.val = 62; omega)
                    subst rank
                    exact ⟨Checks.routine62, Checks.ready62.1, Checks.ready62.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h67 : rank.val < 64
                  ·
                    have hr : rank = ⟨63, by decide⟩ := Fin.ext (by change rank.val = 63; omega)
                    subst rank
                    exact ⟨Checks.routine63, Checks.ready63.1, Checks.ready63.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨64, by decide⟩ := Fin.ext (by change rank.val = 64; omega)
                    subst rank
                    exact ⟨Checks.routine64, Checks.ready64.1, Checks.ready64.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h68 : rank.val < 67
                ·
                  by_cases h69 : rank.val < 66
                  ·
                    have hr : rank = ⟨65, by decide⟩ := Fin.ext (by change rank.val = 65; omega)
                    subst rank
                    exact ⟨Checks.routine65, Checks.ready65.1, Checks.ready65.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨66, by decide⟩ := Fin.ext (by change rank.val = 66; omega)
                    subst rank
                    exact ⟨Checks.routine66, Checks.ready66.1, Checks.ready66.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h70 : rank.val < 68
                  ·
                    have hr : rank = ⟨67, by decide⟩ := Fin.ext (by change rank.val = 67; omega)
                    subst rank
                    exact ⟨Checks.routine67, Checks.ready67.1, Checks.ready67.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h71 : rank.val < 69
                    ·
                      have hr : rank = ⟨68, by decide⟩ := Fin.ext (by change rank.val = 68; omega)
                      subst rank
                      exact ⟨Checks.routine68, Checks.ready68.1, Checks.ready68.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨69, by decide⟩ := Fin.ext (by change rank.val = 69; omega)
                      subst rank
                      exact ⟨Checks.routine69, Checks.ready69.1, Checks.ready69.2, bank_contained_of_all _ (by decide +kernel)⟩
      ·
        by_cases h72 : rank.val < 105
        ·
          by_cases h73 : rank.val < 87
          ·
            by_cases h74 : rank.val < 78
            ·
              by_cases h75 : rank.val < 74
              ·
                by_cases h76 : rank.val < 72
                ·
                  by_cases h77 : rank.val < 71
                  ·
                    have hr : rank = ⟨70, by decide⟩ := Fin.ext (by change rank.val = 70; omega)
                    subst rank
                    exact ⟨Checks.routine70, Checks.ready70.1, Checks.ready70.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨71, by decide⟩ := Fin.ext (by change rank.val = 71; omega)
                    subst rank
                    exact ⟨Checks.routine71, Checks.ready71.1, Checks.ready71.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h78 : rank.val < 73
                  ·
                    have hr : rank = ⟨72, by decide⟩ := Fin.ext (by change rank.val = 72; omega)
                    subst rank
                    exact ⟨Checks.routine72, Checks.ready72.1, Checks.ready72.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨73, by decide⟩ := Fin.ext (by change rank.val = 73; omega)
                    subst rank
                    exact ⟨Checks.routine73, Checks.ready73.1, Checks.ready73.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h79 : rank.val < 76
                ·
                  by_cases h80 : rank.val < 75
                  ·
                    have hr : rank = ⟨74, by decide⟩ := Fin.ext (by change rank.val = 74; omega)
                    subst rank
                    exact ⟨Checks.routine74, Checks.ready74.1, Checks.ready74.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨75, by decide⟩ := Fin.ext (by change rank.val = 75; omega)
                    subst rank
                    exact ⟨Checks.routine75, Checks.ready75.1, Checks.ready75.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h81 : rank.val < 77
                  ·
                    have hr : rank = ⟨76, by decide⟩ := Fin.ext (by change rank.val = 76; omega)
                    subst rank
                    exact ⟨Checks.routine76, Checks.ready76.1, Checks.ready76.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨77, by decide⟩ := Fin.ext (by change rank.val = 77; omega)
                    subst rank
                    exact ⟨Checks.routine77, Checks.ready77.1, Checks.ready77.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h82 : rank.val < 82
              ·
                by_cases h83 : rank.val < 80
                ·
                  by_cases h84 : rank.val < 79
                  ·
                    have hr : rank = ⟨78, by decide⟩ := Fin.ext (by change rank.val = 78; omega)
                    subst rank
                    exact ⟨Checks.routine78, Checks.ready78.1, Checks.ready78.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨79, by decide⟩ := Fin.ext (by change rank.val = 79; omega)
                    subst rank
                    exact ⟨Checks.routine79, Checks.ready79.1, Checks.ready79.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h85 : rank.val < 81
                  ·
                    have hr : rank = ⟨80, by decide⟩ := Fin.ext (by change rank.val = 80; omega)
                    subst rank
                    exact ⟨Checks.routine80, Checks.ready80.1, Checks.ready80.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨81, by decide⟩ := Fin.ext (by change rank.val = 81; omega)
                    subst rank
                    exact ⟨Checks.routine81, Checks.ready81.1, Checks.ready81.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h86 : rank.val < 84
                ·
                  by_cases h87 : rank.val < 83
                  ·
                    have hr : rank = ⟨82, by decide⟩ := Fin.ext (by change rank.val = 82; omega)
                    subst rank
                    exact ⟨Checks.routine82, Checks.ready82.1, Checks.ready82.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨83, by decide⟩ := Fin.ext (by change rank.val = 83; omega)
                    subst rank
                    exact ⟨Checks.routine83, Checks.ready83.1, Checks.ready83.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h88 : rank.val < 85
                  ·
                    have hr : rank = ⟨84, by decide⟩ := Fin.ext (by change rank.val = 84; omega)
                    subst rank
                    exact ⟨Checks.routine84, Checks.ready84.1, Checks.ready84.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h89 : rank.val < 86
                    ·
                      have hr : rank = ⟨85, by decide⟩ := Fin.ext (by change rank.val = 85; omega)
                      subst rank
                      exact ⟨Checks.routine85, Checks.ready85.1, Checks.ready85.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨86, by decide⟩ := Fin.ext (by change rank.val = 86; omega)
                      subst rank
                      exact ⟨Checks.routine86, Checks.ready86.1, Checks.ready86.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h90 : rank.val < 96
            ·
              by_cases h91 : rank.val < 91
              ·
                by_cases h92 : rank.val < 89
                ·
                  by_cases h93 : rank.val < 88
                  ·
                    have hr : rank = ⟨87, by decide⟩ := Fin.ext (by change rank.val = 87; omega)
                    subst rank
                    exact ⟨Checks.routine87, Checks.ready87.1, Checks.ready87.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨88, by decide⟩ := Fin.ext (by change rank.val = 88; omega)
                    subst rank
                    exact ⟨Checks.routine88, Checks.ready88.1, Checks.ready88.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h94 : rank.val < 90
                  ·
                    have hr : rank = ⟨89, by decide⟩ := Fin.ext (by change rank.val = 89; omega)
                    subst rank
                    exact ⟨Checks.routine89, Checks.ready89.1, Checks.ready89.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨90, by decide⟩ := Fin.ext (by change rank.val = 90; omega)
                    subst rank
                    exact ⟨Checks.routine90, Checks.ready90.1, Checks.ready90.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h95 : rank.val < 93
                ·
                  by_cases h96 : rank.val < 92
                  ·
                    have hr : rank = ⟨91, by decide⟩ := Fin.ext (by change rank.val = 91; omega)
                    subst rank
                    exact ⟨Checks.routine91, Checks.ready91.1, Checks.ready91.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨92, by decide⟩ := Fin.ext (by change rank.val = 92; omega)
                    subst rank
                    exact ⟨Checks.routine92, Checks.ready92.1, Checks.ready92.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h97 : rank.val < 94
                  ·
                    have hr : rank = ⟨93, by decide⟩ := Fin.ext (by change rank.val = 93; omega)
                    subst rank
                    exact ⟨Checks.routine93, Checks.ready93.1, Checks.ready93.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h98 : rank.val < 95
                    ·
                      have hr : rank = ⟨94, by decide⟩ := Fin.ext (by change rank.val = 94; omega)
                      subst rank
                      exact ⟨Checks.routine94, Checks.ready94.1, Checks.ready94.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨95, by decide⟩ := Fin.ext (by change rank.val = 95; omega)
                      subst rank
                      exact ⟨Checks.routine95, Checks.ready95.1, Checks.ready95.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h99 : rank.val < 100
              ·
                by_cases h100 : rank.val < 98
                ·
                  by_cases h101 : rank.val < 97
                  ·
                    have hr : rank = ⟨96, by decide⟩ := Fin.ext (by change rank.val = 96; omega)
                    subst rank
                    exact ⟨Checks.routine96, Checks.ready96.1, Checks.ready96.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨97, by decide⟩ := Fin.ext (by change rank.val = 97; omega)
                    subst rank
                    exact ⟨Checks.routine97, Checks.ready97.1, Checks.ready97.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h102 : rank.val < 99
                  ·
                    have hr : rank = ⟨98, by decide⟩ := Fin.ext (by change rank.val = 98; omega)
                    subst rank
                    exact ⟨Checks.routine98, Checks.ready98.1, Checks.ready98.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨99, by decide⟩ := Fin.ext (by change rank.val = 99; omega)
                    subst rank
                    exact ⟨Checks.routine99, Checks.ready99.1, Checks.ready99.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h103 : rank.val < 102
                ·
                  by_cases h104 : rank.val < 101
                  ·
                    have hr : rank = ⟨100, by decide⟩ := Fin.ext (by change rank.val = 100; omega)
                    subst rank
                    exact ⟨Checks.routine100, Checks.ready100.1, Checks.ready100.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨101, by decide⟩ := Fin.ext (by change rank.val = 101; omega)
                    subst rank
                    exact ⟨Checks.routine101, Checks.ready101.1, Checks.ready101.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h105 : rank.val < 103
                  ·
                    have hr : rank = ⟨102, by decide⟩ := Fin.ext (by change rank.val = 102; omega)
                    subst rank
                    exact ⟨Checks.routine102, Checks.ready102.1, Checks.ready102.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h106 : rank.val < 104
                    ·
                      have hr : rank = ⟨103, by decide⟩ := Fin.ext (by change rank.val = 103; omega)
                      subst rank
                      exact ⟨Checks.routine103, Checks.ready103.1, Checks.ready103.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨104, by decide⟩ := Fin.ext (by change rank.val = 104; omega)
                      subst rank
                      exact ⟨Checks.routine104, Checks.ready104.1, Checks.ready104.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h107 : rank.val < 122
          ·
            by_cases h108 : rank.val < 113
            ·
              by_cases h109 : rank.val < 109
              ·
                by_cases h110 : rank.val < 107
                ·
                  by_cases h111 : rank.val < 106
                  ·
                    have hr : rank = ⟨105, by decide⟩ := Fin.ext (by change rank.val = 105; omega)
                    subst rank
                    exact ⟨Checks.routine105, Checks.ready105.1, Checks.ready105.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨106, by decide⟩ := Fin.ext (by change rank.val = 106; omega)
                    subst rank
                    exact ⟨Checks.routine106, Checks.ready106.1, Checks.ready106.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h112 : rank.val < 108
                  ·
                    have hr : rank = ⟨107, by decide⟩ := Fin.ext (by change rank.val = 107; omega)
                    subst rank
                    exact ⟨Checks.routine107, Checks.ready107.1, Checks.ready107.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨108, by decide⟩ := Fin.ext (by change rank.val = 108; omega)
                    subst rank
                    exact ⟨Checks.routine108, Checks.ready108.1, Checks.ready108.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h113 : rank.val < 111
                ·
                  by_cases h114 : rank.val < 110
                  ·
                    have hr : rank = ⟨109, by decide⟩ := Fin.ext (by change rank.val = 109; omega)
                    subst rank
                    exact ⟨Checks.routine109, Checks.ready109.1, Checks.ready109.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨110, by decide⟩ := Fin.ext (by change rank.val = 110; omega)
                    subst rank
                    exact ⟨Checks.routine110, Checks.ready110.1, Checks.ready110.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h115 : rank.val < 112
                  ·
                    have hr : rank = ⟨111, by decide⟩ := Fin.ext (by change rank.val = 111; omega)
                    subst rank
                    exact ⟨Checks.routine111, Checks.ready111.1, Checks.ready111.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨112, by decide⟩ := Fin.ext (by change rank.val = 112; omega)
                    subst rank
                    exact ⟨Checks.routine112, Checks.ready112.1, Checks.ready112.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h116 : rank.val < 117
              ·
                by_cases h117 : rank.val < 115
                ·
                  by_cases h118 : rank.val < 114
                  ·
                    have hr : rank = ⟨113, by decide⟩ := Fin.ext (by change rank.val = 113; omega)
                    subst rank
                    exact ⟨Checks.routine113, Checks.ready113.1, Checks.ready113.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨114, by decide⟩ := Fin.ext (by change rank.val = 114; omega)
                    subst rank
                    exact ⟨Checks.routine114, Checks.ready114.1, Checks.ready114.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h119 : rank.val < 116
                  ·
                    have hr : rank = ⟨115, by decide⟩ := Fin.ext (by change rank.val = 115; omega)
                    subst rank
                    exact ⟨Checks.routine115, Checks.ready115.1, Checks.ready115.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨116, by decide⟩ := Fin.ext (by change rank.val = 116; omega)
                    subst rank
                    exact ⟨Checks.routine116, Checks.ready116.1, Checks.ready116.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h120 : rank.val < 119
                ·
                  by_cases h121 : rank.val < 118
                  ·
                    have hr : rank = ⟨117, by decide⟩ := Fin.ext (by change rank.val = 117; omega)
                    subst rank
                    exact ⟨Checks.routine117, Checks.ready117.1, Checks.ready117.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨118, by decide⟩ := Fin.ext (by change rank.val = 118; omega)
                    subst rank
                    exact ⟨Checks.routine118, Checks.ready118.1, Checks.ready118.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h122 : rank.val < 120
                  ·
                    have hr : rank = ⟨119, by decide⟩ := Fin.ext (by change rank.val = 119; omega)
                    subst rank
                    exact ⟨Checks.routine119, Checks.ready119.1, Checks.ready119.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h123 : rank.val < 121
                    ·
                      have hr : rank = ⟨120, by decide⟩ := Fin.ext (by change rank.val = 120; omega)
                      subst rank
                      exact ⟨Checks.routine120, Checks.ready120.1, Checks.ready120.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨121, by decide⟩ := Fin.ext (by change rank.val = 121; omega)
                      subst rank
                      exact ⟨Checks.routine121, Checks.ready121.1, Checks.ready121.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h124 : rank.val < 131
            ·
              by_cases h125 : rank.val < 126
              ·
                by_cases h126 : rank.val < 124
                ·
                  by_cases h127 : rank.val < 123
                  ·
                    have hr : rank = ⟨122, by decide⟩ := Fin.ext (by change rank.val = 122; omega)
                    subst rank
                    exact ⟨Checks.routine122, Checks.ready122.1, Checks.ready122.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨123, by decide⟩ := Fin.ext (by change rank.val = 123; omega)
                    subst rank
                    exact ⟨Checks.routine123, Checks.ready123.1, Checks.ready123.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h128 : rank.val < 125
                  ·
                    have hr : rank = ⟨124, by decide⟩ := Fin.ext (by change rank.val = 124; omega)
                    subst rank
                    exact ⟨Checks.routine124, Checks.ready124.1, Checks.ready124.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨125, by decide⟩ := Fin.ext (by change rank.val = 125; omega)
                    subst rank
                    exact ⟨Checks.routine125, Checks.ready125.1, Checks.ready125.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h129 : rank.val < 128
                ·
                  by_cases h130 : rank.val < 127
                  ·
                    have hr : rank = ⟨126, by decide⟩ := Fin.ext (by change rank.val = 126; omega)
                    subst rank
                    exact ⟨Checks.routine126, Checks.ready126.1, Checks.ready126.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨127, by decide⟩ := Fin.ext (by change rank.val = 127; omega)
                    subst rank
                    exact ⟨Checks.routine127, Checks.ready127.1, Checks.ready127.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h131 : rank.val < 129
                  ·
                    have hr : rank = ⟨128, by decide⟩ := Fin.ext (by change rank.val = 128; omega)
                    subst rank
                    exact ⟨Checks.routine128, Checks.ready128.1, Checks.ready128.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h132 : rank.val < 130
                    ·
                      have hr : rank = ⟨129, by decide⟩ := Fin.ext (by change rank.val = 129; omega)
                      subst rank
                      exact ⟨Checks.routine129, Checks.ready129.1, Checks.ready129.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨130, by decide⟩ := Fin.ext (by change rank.val = 130; omega)
                      subst rank
                      exact ⟨Checks.routine130, Checks.ready130.1, Checks.ready130.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h133 : rank.val < 135
              ·
                by_cases h134 : rank.val < 133
                ·
                  by_cases h135 : rank.val < 132
                  ·
                    have hr : rank = ⟨131, by decide⟩ := Fin.ext (by change rank.val = 131; omega)
                    subst rank
                    exact ⟨Checks.routine131, Checks.ready131.1, Checks.ready131.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨132, by decide⟩ := Fin.ext (by change rank.val = 132; omega)
                    subst rank
                    exact ⟨Checks.routine132, Checks.ready132.1, Checks.ready132.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h136 : rank.val < 134
                  ·
                    have hr : rank = ⟨133, by decide⟩ := Fin.ext (by change rank.val = 133; omega)
                    subst rank
                    exact ⟨Checks.routine133, Checks.ready133.1, Checks.ready133.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨134, by decide⟩ := Fin.ext (by change rank.val = 134; omega)
                    subst rank
                    exact ⟨Checks.routine134, Checks.ready134.1, Checks.ready134.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h137 : rank.val < 137
                ·
                  by_cases h138 : rank.val < 136
                  ·
                    have hr : rank = ⟨135, by decide⟩ := Fin.ext (by change rank.val = 135; omega)
                    subst rank
                    exact ⟨Checks.routine135, Checks.ready135.1, Checks.ready135.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨136, by decide⟩ := Fin.ext (by change rank.val = 136; omega)
                    subst rank
                    exact ⟨Checks.routine136, Checks.ready136.1, Checks.ready136.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h139 : rank.val < 138
                  ·
                    have hr : rank = ⟨137, by decide⟩ := Fin.ext (by change rank.val = 137; omega)
                    subst rank
                    exact ⟨Checks.routine137, Checks.ready137.1, Checks.ready137.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h140 : rank.val < 139
                    ·
                      have hr : rank = ⟨138, by decide⟩ := Fin.ext (by change rank.val = 138; omega)
                      subst rank
                      exact ⟨Checks.routine138, Checks.ready138.1, Checks.ready138.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨139, by decide⟩ := Fin.ext (by change rank.val = 139; omega)
                      subst rank
                      exact ⟨Checks.routine139, Checks.ready139.1, Checks.ready139.2, bank_contained_of_all _ (by decide +kernel)⟩
    ·
      by_cases h141 : rank.val < 210
      ·
        by_cases h142 : rank.val < 175
        ·
          by_cases h143 : rank.val < 157
          ·
            by_cases h144 : rank.val < 148
            ·
              by_cases h145 : rank.val < 144
              ·
                by_cases h146 : rank.val < 142
                ·
                  by_cases h147 : rank.val < 141
                  ·
                    have hr : rank = ⟨140, by decide⟩ := Fin.ext (by change rank.val = 140; omega)
                    subst rank
                    exact ⟨Checks.routine140, Checks.ready140.1, Checks.ready140.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨141, by decide⟩ := Fin.ext (by change rank.val = 141; omega)
                    subst rank
                    exact ⟨Checks.routine141, Checks.ready141.1, Checks.ready141.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h148 : rank.val < 143
                  ·
                    have hr : rank = ⟨142, by decide⟩ := Fin.ext (by change rank.val = 142; omega)
                    subst rank
                    exact ⟨Checks.routine142, Checks.ready142.1, Checks.ready142.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨143, by decide⟩ := Fin.ext (by change rank.val = 143; omega)
                    subst rank
                    exact ⟨Checks.routine143, Checks.ready143.1, Checks.ready143.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h149 : rank.val < 146
                ·
                  by_cases h150 : rank.val < 145
                  ·
                    have hr : rank = ⟨144, by decide⟩ := Fin.ext (by change rank.val = 144; omega)
                    subst rank
                    exact ⟨Checks.routine144, Checks.ready144.1, Checks.ready144.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨145, by decide⟩ := Fin.ext (by change rank.val = 145; omega)
                    subst rank
                    exact ⟨Checks.routine145, Checks.ready145.1, Checks.ready145.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h151 : rank.val < 147
                  ·
                    have hr : rank = ⟨146, by decide⟩ := Fin.ext (by change rank.val = 146; omega)
                    subst rank
                    exact ⟨Checks.routine146, Checks.ready146.1, Checks.ready146.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨147, by decide⟩ := Fin.ext (by change rank.val = 147; omega)
                    subst rank
                    exact ⟨Checks.routine147, Checks.ready147.1, Checks.ready147.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h152 : rank.val < 152
              ·
                by_cases h153 : rank.val < 150
                ·
                  by_cases h154 : rank.val < 149
                  ·
                    have hr : rank = ⟨148, by decide⟩ := Fin.ext (by change rank.val = 148; omega)
                    subst rank
                    exact ⟨Checks.routine148, Checks.ready148.1, Checks.ready148.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨149, by decide⟩ := Fin.ext (by change rank.val = 149; omega)
                    subst rank
                    exact ⟨Checks.routine149, Checks.ready149.1, Checks.ready149.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h155 : rank.val < 151
                  ·
                    have hr : rank = ⟨150, by decide⟩ := Fin.ext (by change rank.val = 150; omega)
                    subst rank
                    exact ⟨Checks.routine150, Checks.ready150.1, Checks.ready150.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨151, by decide⟩ := Fin.ext (by change rank.val = 151; omega)
                    subst rank
                    exact ⟨Checks.routine151, Checks.ready151.1, Checks.ready151.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h156 : rank.val < 154
                ·
                  by_cases h157 : rank.val < 153
                  ·
                    have hr : rank = ⟨152, by decide⟩ := Fin.ext (by change rank.val = 152; omega)
                    subst rank
                    exact ⟨Checks.routine152, Checks.ready152.1, Checks.ready152.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨153, by decide⟩ := Fin.ext (by change rank.val = 153; omega)
                    subst rank
                    exact ⟨Checks.routine153, Checks.ready153.1, Checks.ready153.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h158 : rank.val < 155
                  ·
                    have hr : rank = ⟨154, by decide⟩ := Fin.ext (by change rank.val = 154; omega)
                    subst rank
                    exact ⟨Checks.routine154, Checks.ready154.1, Checks.ready154.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h159 : rank.val < 156
                    ·
                      have hr : rank = ⟨155, by decide⟩ := Fin.ext (by change rank.val = 155; omega)
                      subst rank
                      exact ⟨Checks.routine155, Checks.ready155.1, Checks.ready155.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨156, by decide⟩ := Fin.ext (by change rank.val = 156; omega)
                      subst rank
                      exact ⟨Checks.routine156, Checks.ready156.1, Checks.ready156.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h160 : rank.val < 166
            ·
              by_cases h161 : rank.val < 161
              ·
                by_cases h162 : rank.val < 159
                ·
                  by_cases h163 : rank.val < 158
                  ·
                    have hr : rank = ⟨157, by decide⟩ := Fin.ext (by change rank.val = 157; omega)
                    subst rank
                    exact ⟨Checks.routine157, Checks.ready157.1, Checks.ready157.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨158, by decide⟩ := Fin.ext (by change rank.val = 158; omega)
                    subst rank
                    exact ⟨Checks.routine158, Checks.ready158.1, Checks.ready158.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h164 : rank.val < 160
                  ·
                    have hr : rank = ⟨159, by decide⟩ := Fin.ext (by change rank.val = 159; omega)
                    subst rank
                    exact ⟨Checks.routine159, Checks.ready159.1, Checks.ready159.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨160, by decide⟩ := Fin.ext (by change rank.val = 160; omega)
                    subst rank
                    exact ⟨Checks.routine160, Checks.ready160.1, Checks.ready160.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h165 : rank.val < 163
                ·
                  by_cases h166 : rank.val < 162
                  ·
                    have hr : rank = ⟨161, by decide⟩ := Fin.ext (by change rank.val = 161; omega)
                    subst rank
                    exact ⟨Checks.routine161, Checks.ready161.1, Checks.ready161.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨162, by decide⟩ := Fin.ext (by change rank.val = 162; omega)
                    subst rank
                    exact ⟨Checks.routine162, Checks.ready162.1, Checks.ready162.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h167 : rank.val < 164
                  ·
                    have hr : rank = ⟨163, by decide⟩ := Fin.ext (by change rank.val = 163; omega)
                    subst rank
                    exact ⟨Checks.routine163, Checks.ready163.1, Checks.ready163.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h168 : rank.val < 165
                    ·
                      have hr : rank = ⟨164, by decide⟩ := Fin.ext (by change rank.val = 164; omega)
                      subst rank
                      exact ⟨Checks.routine164, Checks.ready164.1, Checks.ready164.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨165, by decide⟩ := Fin.ext (by change rank.val = 165; omega)
                      subst rank
                      exact ⟨Checks.routine165, Checks.ready165.1, Checks.ready165.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h169 : rank.val < 170
              ·
                by_cases h170 : rank.val < 168
                ·
                  by_cases h171 : rank.val < 167
                  ·
                    have hr : rank = ⟨166, by decide⟩ := Fin.ext (by change rank.val = 166; omega)
                    subst rank
                    exact ⟨Checks.routine166, Checks.ready166.1, Checks.ready166.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨167, by decide⟩ := Fin.ext (by change rank.val = 167; omega)
                    subst rank
                    exact ⟨Checks.routine167, Checks.ready167.1, Checks.ready167.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h172 : rank.val < 169
                  ·
                    have hr : rank = ⟨168, by decide⟩ := Fin.ext (by change rank.val = 168; omega)
                    subst rank
                    exact ⟨Checks.routine168, Checks.ready168.1, Checks.ready168.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨169, by decide⟩ := Fin.ext (by change rank.val = 169; omega)
                    subst rank
                    exact ⟨Checks.routine169, Checks.ready169.1, Checks.ready169.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h173 : rank.val < 172
                ·
                  by_cases h174 : rank.val < 171
                  ·
                    have hr : rank = ⟨170, by decide⟩ := Fin.ext (by change rank.val = 170; omega)
                    subst rank
                    exact ⟨Checks.routine170, Checks.ready170.1, Checks.ready170.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨171, by decide⟩ := Fin.ext (by change rank.val = 171; omega)
                    subst rank
                    exact ⟨Checks.routine171, Checks.ready171.1, Checks.ready171.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h175 : rank.val < 173
                  ·
                    have hr : rank = ⟨172, by decide⟩ := Fin.ext (by change rank.val = 172; omega)
                    subst rank
                    exact ⟨Checks.routine172, Checks.ready172.1, Checks.ready172.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h176 : rank.val < 174
                    ·
                      have hr : rank = ⟨173, by decide⟩ := Fin.ext (by change rank.val = 173; omega)
                      subst rank
                      exact ⟨Checks.routine173, Checks.ready173.1, Checks.ready173.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨174, by decide⟩ := Fin.ext (by change rank.val = 174; omega)
                      subst rank
                      exact ⟨Checks.routine174, Checks.ready174.1, Checks.ready174.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h177 : rank.val < 192
          ·
            by_cases h178 : rank.val < 183
            ·
              by_cases h179 : rank.val < 179
              ·
                by_cases h180 : rank.val < 177
                ·
                  by_cases h181 : rank.val < 176
                  ·
                    have hr : rank = ⟨175, by decide⟩ := Fin.ext (by change rank.val = 175; omega)
                    subst rank
                    exact ⟨Checks.routine175, Checks.ready175.1, Checks.ready175.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨176, by decide⟩ := Fin.ext (by change rank.val = 176; omega)
                    subst rank
                    exact ⟨Checks.routine176, Checks.ready176.1, Checks.ready176.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h182 : rank.val < 178
                  ·
                    have hr : rank = ⟨177, by decide⟩ := Fin.ext (by change rank.val = 177; omega)
                    subst rank
                    exact ⟨Checks.routine177, Checks.ready177.1, Checks.ready177.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨178, by decide⟩ := Fin.ext (by change rank.val = 178; omega)
                    subst rank
                    exact ⟨Checks.routine178, Checks.ready178.1, Checks.ready178.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h183 : rank.val < 181
                ·
                  by_cases h184 : rank.val < 180
                  ·
                    have hr : rank = ⟨179, by decide⟩ := Fin.ext (by change rank.val = 179; omega)
                    subst rank
                    exact ⟨Checks.routine179, Checks.ready179.1, Checks.ready179.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨180, by decide⟩ := Fin.ext (by change rank.val = 180; omega)
                    subst rank
                    exact ⟨Checks.routine180, Checks.ready180.1, Checks.ready180.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h185 : rank.val < 182
                  ·
                    have hr : rank = ⟨181, by decide⟩ := Fin.ext (by change rank.val = 181; omega)
                    subst rank
                    exact ⟨Checks.routine181, Checks.ready181.1, Checks.ready181.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨182, by decide⟩ := Fin.ext (by change rank.val = 182; omega)
                    subst rank
                    exact ⟨Checks.routine182, Checks.ready182.1, Checks.ready182.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h186 : rank.val < 187
              ·
                by_cases h187 : rank.val < 185
                ·
                  by_cases h188 : rank.val < 184
                  ·
                    have hr : rank = ⟨183, by decide⟩ := Fin.ext (by change rank.val = 183; omega)
                    subst rank
                    exact ⟨Checks.routine183, Checks.ready183.1, Checks.ready183.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨184, by decide⟩ := Fin.ext (by change rank.val = 184; omega)
                    subst rank
                    exact ⟨Checks.routine184, Checks.ready184.1, Checks.ready184.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h189 : rank.val < 186
                  ·
                    have hr : rank = ⟨185, by decide⟩ := Fin.ext (by change rank.val = 185; omega)
                    subst rank
                    exact ⟨Checks.routine185, Checks.ready185.1, Checks.ready185.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨186, by decide⟩ := Fin.ext (by change rank.val = 186; omega)
                    subst rank
                    exact ⟨Checks.routine186, Checks.ready186.1, Checks.ready186.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h190 : rank.val < 189
                ·
                  by_cases h191 : rank.val < 188
                  ·
                    have hr : rank = ⟨187, by decide⟩ := Fin.ext (by change rank.val = 187; omega)
                    subst rank
                    exact ⟨Checks.routine187, Checks.ready187.1, Checks.ready187.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨188, by decide⟩ := Fin.ext (by change rank.val = 188; omega)
                    subst rank
                    exact ⟨Checks.routine188, Checks.ready188.1, Checks.ready188.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h192 : rank.val < 190
                  ·
                    have hr : rank = ⟨189, by decide⟩ := Fin.ext (by change rank.val = 189; omega)
                    subst rank
                    exact ⟨Checks.routine189, Checks.ready189.1, Checks.ready189.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h193 : rank.val < 191
                    ·
                      have hr : rank = ⟨190, by decide⟩ := Fin.ext (by change rank.val = 190; omega)
                      subst rank
                      exact ⟨Checks.routine190, Checks.ready190.1, Checks.ready190.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨191, by decide⟩ := Fin.ext (by change rank.val = 191; omega)
                      subst rank
                      exact ⟨Checks.routine191, Checks.ready191.1, Checks.ready191.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h194 : rank.val < 201
            ·
              by_cases h195 : rank.val < 196
              ·
                by_cases h196 : rank.val < 194
                ·
                  by_cases h197 : rank.val < 193
                  ·
                    have hr : rank = ⟨192, by decide⟩ := Fin.ext (by change rank.val = 192; omega)
                    subst rank
                    exact ⟨Checks.routine192, Checks.ready192.1, Checks.ready192.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨193, by decide⟩ := Fin.ext (by change rank.val = 193; omega)
                    subst rank
                    exact ⟨Checks.routine193, Checks.ready193.1, Checks.ready193.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h198 : rank.val < 195
                  ·
                    have hr : rank = ⟨194, by decide⟩ := Fin.ext (by change rank.val = 194; omega)
                    subst rank
                    exact ⟨Checks.routine194, Checks.ready194.1, Checks.ready194.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨195, by decide⟩ := Fin.ext (by change rank.val = 195; omega)
                    subst rank
                    exact ⟨Checks.routine195, Checks.ready195.1, Checks.ready195.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h199 : rank.val < 198
                ·
                  by_cases h200 : rank.val < 197
                  ·
                    have hr : rank = ⟨196, by decide⟩ := Fin.ext (by change rank.val = 196; omega)
                    subst rank
                    exact ⟨Checks.routine196, Checks.ready196.1, Checks.ready196.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨197, by decide⟩ := Fin.ext (by change rank.val = 197; omega)
                    subst rank
                    exact ⟨Checks.routine197, Checks.ready197.1, Checks.ready197.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h201 : rank.val < 199
                  ·
                    have hr : rank = ⟨198, by decide⟩ := Fin.ext (by change rank.val = 198; omega)
                    subst rank
                    exact ⟨Checks.routine198, Checks.ready198.1, Checks.ready198.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h202 : rank.val < 200
                    ·
                      have hr : rank = ⟨199, by decide⟩ := Fin.ext (by change rank.val = 199; omega)
                      subst rank
                      exact ⟨Checks.routine199, Checks.ready199.1, Checks.ready199.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨200, by decide⟩ := Fin.ext (by change rank.val = 200; omega)
                      subst rank
                      exact ⟨Checks.routine200, Checks.ready200.1, Checks.ready200.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h203 : rank.val < 205
              ·
                by_cases h204 : rank.val < 203
                ·
                  by_cases h205 : rank.val < 202
                  ·
                    have hr : rank = ⟨201, by decide⟩ := Fin.ext (by change rank.val = 201; omega)
                    subst rank
                    exact ⟨Checks.routine201, Checks.ready201.1, Checks.ready201.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨202, by decide⟩ := Fin.ext (by change rank.val = 202; omega)
                    subst rank
                    exact ⟨Checks.routine202, Checks.ready202.1, Checks.ready202.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h206 : rank.val < 204
                  ·
                    have hr : rank = ⟨203, by decide⟩ := Fin.ext (by change rank.val = 203; omega)
                    subst rank
                    exact ⟨Checks.routine203, Checks.ready203.1, Checks.ready203.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨204, by decide⟩ := Fin.ext (by change rank.val = 204; omega)
                    subst rank
                    exact ⟨Checks.routine204, Checks.ready204.1, Checks.ready204.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h207 : rank.val < 207
                ·
                  by_cases h208 : rank.val < 206
                  ·
                    have hr : rank = ⟨205, by decide⟩ := Fin.ext (by change rank.val = 205; omega)
                    subst rank
                    exact ⟨Checks.routine205, Checks.ready205.1, Checks.ready205.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨206, by decide⟩ := Fin.ext (by change rank.val = 206; omega)
                    subst rank
                    exact ⟨Checks.routine206, Checks.ready206.1, Checks.ready206.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h209 : rank.val < 208
                  ·
                    have hr : rank = ⟨207, by decide⟩ := Fin.ext (by change rank.val = 207; omega)
                    subst rank
                    exact ⟨Checks.routine207, Checks.ready207.1, Checks.ready207.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h210 : rank.val < 209
                    ·
                      have hr : rank = ⟨208, by decide⟩ := Fin.ext (by change rank.val = 208; omega)
                      subst rank
                      exact ⟨Checks.routine208, Checks.ready208.1, Checks.ready208.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨209, by decide⟩ := Fin.ext (by change rank.val = 209; omega)
                      subst rank
                      exact ⟨Checks.routine209, Checks.ready209.1, Checks.ready209.2, bank_contained_of_all _ (by decide +kernel)⟩
      ·
        by_cases h211 : rank.val < 245
        ·
          by_cases h212 : rank.val < 227
          ·
            by_cases h213 : rank.val < 218
            ·
              by_cases h214 : rank.val < 214
              ·
                by_cases h215 : rank.val < 212
                ·
                  by_cases h216 : rank.val < 211
                  ·
                    have hr : rank = ⟨210, by decide⟩ := Fin.ext (by change rank.val = 210; omega)
                    subst rank
                    exact ⟨Checks.routine210, Checks.ready210.1, Checks.ready210.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨211, by decide⟩ := Fin.ext (by change rank.val = 211; omega)
                    subst rank
                    exact ⟨Checks.routine211, Checks.ready211.1, Checks.ready211.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h217 : rank.val < 213
                  ·
                    have hr : rank = ⟨212, by decide⟩ := Fin.ext (by change rank.val = 212; omega)
                    subst rank
                    exact ⟨Checks.routine212, Checks.ready212.1, Checks.ready212.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨213, by decide⟩ := Fin.ext (by change rank.val = 213; omega)
                    subst rank
                    exact ⟨Checks.routine213, Checks.ready213.1, Checks.ready213.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h218 : rank.val < 216
                ·
                  by_cases h219 : rank.val < 215
                  ·
                    have hr : rank = ⟨214, by decide⟩ := Fin.ext (by change rank.val = 214; omega)
                    subst rank
                    exact ⟨Checks.routine214, Checks.ready214.1, Checks.ready214.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨215, by decide⟩ := Fin.ext (by change rank.val = 215; omega)
                    subst rank
                    exact ⟨Checks.routine215, Checks.ready215.1, Checks.ready215.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h220 : rank.val < 217
                  ·
                    have hr : rank = ⟨216, by decide⟩ := Fin.ext (by change rank.val = 216; omega)
                    subst rank
                    exact ⟨Checks.routine216, Checks.ready216.1, Checks.ready216.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨217, by decide⟩ := Fin.ext (by change rank.val = 217; omega)
                    subst rank
                    exact ⟨Checks.routine217, Checks.ready217.1, Checks.ready217.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h221 : rank.val < 222
              ·
                by_cases h222 : rank.val < 220
                ·
                  by_cases h223 : rank.val < 219
                  ·
                    have hr : rank = ⟨218, by decide⟩ := Fin.ext (by change rank.val = 218; omega)
                    subst rank
                    exact ⟨Checks.routine218, Checks.ready218.1, Checks.ready218.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨219, by decide⟩ := Fin.ext (by change rank.val = 219; omega)
                    subst rank
                    exact ⟨Checks.routine219, Checks.ready219.1, Checks.ready219.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h224 : rank.val < 221
                  ·
                    have hr : rank = ⟨220, by decide⟩ := Fin.ext (by change rank.val = 220; omega)
                    subst rank
                    exact ⟨Checks.routine220, Checks.ready220.1, Checks.ready220.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨221, by decide⟩ := Fin.ext (by change rank.val = 221; omega)
                    subst rank
                    exact ⟨Checks.routine221, Checks.ready221.1, Checks.ready221.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h225 : rank.val < 224
                ·
                  by_cases h226 : rank.val < 223
                  ·
                    have hr : rank = ⟨222, by decide⟩ := Fin.ext (by change rank.val = 222; omega)
                    subst rank
                    exact ⟨Checks.routine222, Checks.ready222.1, Checks.ready222.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨223, by decide⟩ := Fin.ext (by change rank.val = 223; omega)
                    subst rank
                    exact ⟨Checks.routine223, Checks.ready223.1, Checks.ready223.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h227 : rank.val < 225
                  ·
                    have hr : rank = ⟨224, by decide⟩ := Fin.ext (by change rank.val = 224; omega)
                    subst rank
                    exact ⟨Checks.routine224, Checks.ready224.1, Checks.ready224.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h228 : rank.val < 226
                    ·
                      have hr : rank = ⟨225, by decide⟩ := Fin.ext (by change rank.val = 225; omega)
                      subst rank
                      exact ⟨Checks.routine225, Checks.ready225.1, Checks.ready225.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨226, by decide⟩ := Fin.ext (by change rank.val = 226; omega)
                      subst rank
                      exact ⟨Checks.routine226, Checks.ready226.1, Checks.ready226.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h229 : rank.val < 236
            ·
              by_cases h230 : rank.val < 231
              ·
                by_cases h231 : rank.val < 229
                ·
                  by_cases h232 : rank.val < 228
                  ·
                    have hr : rank = ⟨227, by decide⟩ := Fin.ext (by change rank.val = 227; omega)
                    subst rank
                    exact ⟨Checks.routine227, Checks.ready227.1, Checks.ready227.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨228, by decide⟩ := Fin.ext (by change rank.val = 228; omega)
                    subst rank
                    exact ⟨Checks.routine228, Checks.ready228.1, Checks.ready228.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h233 : rank.val < 230
                  ·
                    have hr : rank = ⟨229, by decide⟩ := Fin.ext (by change rank.val = 229; omega)
                    subst rank
                    exact ⟨Checks.routine229, Checks.ready229.1, Checks.ready229.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨230, by decide⟩ := Fin.ext (by change rank.val = 230; omega)
                    subst rank
                    exact ⟨Checks.routine230, Checks.ready230.1, Checks.ready230.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h234 : rank.val < 233
                ·
                  by_cases h235 : rank.val < 232
                  ·
                    have hr : rank = ⟨231, by decide⟩ := Fin.ext (by change rank.val = 231; omega)
                    subst rank
                    exact ⟨Checks.routine231, Checks.ready231.1, Checks.ready231.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨232, by decide⟩ := Fin.ext (by change rank.val = 232; omega)
                    subst rank
                    exact ⟨Checks.routine232, Checks.ready232.1, Checks.ready232.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h236 : rank.val < 234
                  ·
                    have hr : rank = ⟨233, by decide⟩ := Fin.ext (by change rank.val = 233; omega)
                    subst rank
                    exact ⟨Checks.routine233, Checks.ready233.1, Checks.ready233.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h237 : rank.val < 235
                    ·
                      have hr : rank = ⟨234, by decide⟩ := Fin.ext (by change rank.val = 234; omega)
                      subst rank
                      exact ⟨Checks.routine234, Checks.ready234.1, Checks.ready234.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨235, by decide⟩ := Fin.ext (by change rank.val = 235; omega)
                      subst rank
                      exact ⟨Checks.routine235, Checks.ready235.1, Checks.ready235.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h238 : rank.val < 240
              ·
                by_cases h239 : rank.val < 238
                ·
                  by_cases h240 : rank.val < 237
                  ·
                    have hr : rank = ⟨236, by decide⟩ := Fin.ext (by change rank.val = 236; omega)
                    subst rank
                    exact ⟨Checks.routine236, Checks.ready236.1, Checks.ready236.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨237, by decide⟩ := Fin.ext (by change rank.val = 237; omega)
                    subst rank
                    exact ⟨Checks.routine237, Checks.ready237.1, Checks.ready237.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h241 : rank.val < 239
                  ·
                    have hr : rank = ⟨238, by decide⟩ := Fin.ext (by change rank.val = 238; omega)
                    subst rank
                    exact ⟨Checks.routine238, Checks.ready238.1, Checks.ready238.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨239, by decide⟩ := Fin.ext (by change rank.val = 239; omega)
                    subst rank
                    exact ⟨Checks.routine239, Checks.ready239.1, Checks.ready239.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h242 : rank.val < 242
                ·
                  by_cases h243 : rank.val < 241
                  ·
                    have hr : rank = ⟨240, by decide⟩ := Fin.ext (by change rank.val = 240; omega)
                    subst rank
                    exact ⟨Checks.routine240, Checks.ready240.1, Checks.ready240.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨241, by decide⟩ := Fin.ext (by change rank.val = 241; omega)
                    subst rank
                    exact ⟨Checks.routine241, Checks.ready241.1, Checks.ready241.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h244 : rank.val < 243
                  ·
                    have hr : rank = ⟨242, by decide⟩ := Fin.ext (by change rank.val = 242; omega)
                    subst rank
                    exact ⟨Checks.routine242, Checks.ready242.1, Checks.ready242.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h245 : rank.val < 244
                    ·
                      have hr : rank = ⟨243, by decide⟩ := Fin.ext (by change rank.val = 243; omega)
                      subst rank
                      exact ⟨Checks.routine243, Checks.ready243.1, Checks.ready243.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨244, by decide⟩ := Fin.ext (by change rank.val = 244; omega)
                      subst rank
                      exact ⟨Checks.routine244, Checks.ready244.1, Checks.ready244.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h246 : rank.val < 263
          ·
            by_cases h247 : rank.val < 254
            ·
              by_cases h248 : rank.val < 249
              ·
                by_cases h249 : rank.val < 247
                ·
                  by_cases h250 : rank.val < 246
                  ·
                    have hr : rank = ⟨245, by decide⟩ := Fin.ext (by change rank.val = 245; omega)
                    subst rank
                    exact ⟨Checks.routine245, Checks.ready245.1, Checks.ready245.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨246, by decide⟩ := Fin.ext (by change rank.val = 246; omega)
                    subst rank
                    exact ⟨Checks.routine246, Checks.ready246.1, Checks.ready246.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h251 : rank.val < 248
                  ·
                    have hr : rank = ⟨247, by decide⟩ := Fin.ext (by change rank.val = 247; omega)
                    subst rank
                    exact ⟨Checks.routine247, Checks.ready247.1, Checks.ready247.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨248, by decide⟩ := Fin.ext (by change rank.val = 248; omega)
                    subst rank
                    exact ⟨Checks.routine248, Checks.ready248.1, Checks.ready248.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h252 : rank.val < 251
                ·
                  by_cases h253 : rank.val < 250
                  ·
                    have hr : rank = ⟨249, by decide⟩ := Fin.ext (by change rank.val = 249; omega)
                    subst rank
                    exact ⟨Checks.routine249, Checks.ready249.1, Checks.ready249.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨250, by decide⟩ := Fin.ext (by change rank.val = 250; omega)
                    subst rank
                    exact ⟨Checks.routine250, Checks.ready250.1, Checks.ready250.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h254 : rank.val < 252
                  ·
                    have hr : rank = ⟨251, by decide⟩ := Fin.ext (by change rank.val = 251; omega)
                    subst rank
                    exact ⟨Checks.routine251, Checks.ready251.1, Checks.ready251.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h255 : rank.val < 253
                    ·
                      have hr : rank = ⟨252, by decide⟩ := Fin.ext (by change rank.val = 252; omega)
                      subst rank
                      exact ⟨Checks.routine252, Checks.ready252.1, Checks.ready252.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨253, by decide⟩ := Fin.ext (by change rank.val = 253; omega)
                      subst rank
                      exact ⟨Checks.routine253, Checks.ready253.1, Checks.ready253.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h256 : rank.val < 258
              ·
                by_cases h257 : rank.val < 256
                ·
                  by_cases h258 : rank.val < 255
                  ·
                    have hr : rank = ⟨254, by decide⟩ := Fin.ext (by change rank.val = 254; omega)
                    subst rank
                    exact ⟨Checks.routine254, Checks.ready254.1, Checks.ready254.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨255, by decide⟩ := Fin.ext (by change rank.val = 255; omega)
                    subst rank
                    exact ⟨Checks.routine255, Checks.ready255.1, Checks.ready255.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h259 : rank.val < 257
                  ·
                    have hr : rank = ⟨256, by decide⟩ := Fin.ext (by change rank.val = 256; omega)
                    subst rank
                    exact ⟨Checks.routine256, Checks.ready256.1, Checks.ready256.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨257, by decide⟩ := Fin.ext (by change rank.val = 257; omega)
                    subst rank
                    exact ⟨Checks.routine257, Checks.ready257.1, Checks.ready257.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h260 : rank.val < 260
                ·
                  by_cases h261 : rank.val < 259
                  ·
                    have hr : rank = ⟨258, by decide⟩ := Fin.ext (by change rank.val = 258; omega)
                    subst rank
                    exact ⟨Checks.routine258, Checks.ready258.1, Checks.ready258.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨259, by decide⟩ := Fin.ext (by change rank.val = 259; omega)
                    subst rank
                    exact ⟨Checks.routine259, Checks.ready259.1, Checks.ready259.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h262 : rank.val < 261
                  ·
                    have hr : rank = ⟨260, by decide⟩ := Fin.ext (by change rank.val = 260; omega)
                    subst rank
                    exact ⟨Checks.routine260, Checks.ready260.1, Checks.ready260.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h263 : rank.val < 262
                    ·
                      have hr : rank = ⟨261, by decide⟩ := Fin.ext (by change rank.val = 261; omega)
                      subst rank
                      exact ⟨Checks.routine261, Checks.ready261.1, Checks.ready261.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨262, by decide⟩ := Fin.ext (by change rank.val = 262; omega)
                      subst rank
                      exact ⟨Checks.routine262, Checks.ready262.1, Checks.ready262.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h264 : rank.val < 272
            ·
              by_cases h265 : rank.val < 267
              ·
                by_cases h266 : rank.val < 265
                ·
                  by_cases h267 : rank.val < 264
                  ·
                    have hr : rank = ⟨263, by decide⟩ := Fin.ext (by change rank.val = 263; omega)
                    subst rank
                    exact ⟨Checks.routine263, Checks.ready263.1, Checks.ready263.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨264, by decide⟩ := Fin.ext (by change rank.val = 264; omega)
                    subst rank
                    exact ⟨Checks.routine264, Checks.ready264.1, Checks.ready264.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h268 : rank.val < 266
                  ·
                    have hr : rank = ⟨265, by decide⟩ := Fin.ext (by change rank.val = 265; omega)
                    subst rank
                    exact ⟨Checks.routine265, Checks.ready265.1, Checks.ready265.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨266, by decide⟩ := Fin.ext (by change rank.val = 266; omega)
                    subst rank
                    exact ⟨Checks.routine266, Checks.ready266.1, Checks.ready266.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h269 : rank.val < 269
                ·
                  by_cases h270 : rank.val < 268
                  ·
                    have hr : rank = ⟨267, by decide⟩ := Fin.ext (by change rank.val = 267; omega)
                    subst rank
                    exact ⟨Checks.routine267, Checks.ready267.1, Checks.ready267.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨268, by decide⟩ := Fin.ext (by change rank.val = 268; omega)
                    subst rank
                    exact ⟨Checks.routine268, Checks.ready268.1, Checks.ready268.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h271 : rank.val < 270
                  ·
                    have hr : rank = ⟨269, by decide⟩ := Fin.ext (by change rank.val = 269; omega)
                    subst rank
                    exact ⟨Checks.routine269, Checks.ready269.1, Checks.ready269.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h272 : rank.val < 271
                    ·
                      have hr : rank = ⟨270, by decide⟩ := Fin.ext (by change rank.val = 270; omega)
                      subst rank
                      exact ⟨Checks.routine270, Checks.ready270.1, Checks.ready270.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨271, by decide⟩ := Fin.ext (by change rank.val = 271; omega)
                      subst rank
                      exact ⟨Checks.routine271, Checks.ready271.1, Checks.ready271.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h273 : rank.val < 276
              ·
                by_cases h274 : rank.val < 274
                ·
                  by_cases h275 : rank.val < 273
                  ·
                    have hr : rank = ⟨272, by decide⟩ := Fin.ext (by change rank.val = 272; omega)
                    subst rank
                    exact ⟨Checks.routine272, Checks.ready272.1, Checks.ready272.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨273, by decide⟩ := Fin.ext (by change rank.val = 273; omega)
                    subst rank
                    exact ⟨Checks.routine273, Checks.ready273.1, Checks.ready273.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h276 : rank.val < 275
                  ·
                    have hr : rank = ⟨274, by decide⟩ := Fin.ext (by change rank.val = 274; omega)
                    subst rank
                    exact ⟨Checks.routine274, Checks.ready274.1, Checks.ready274.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨275, by decide⟩ := Fin.ext (by change rank.val = 275; omega)
                    subst rank
                    exact ⟨Checks.routine275, Checks.ready275.1, Checks.ready275.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h277 : rank.val < 278
                ·
                  by_cases h278 : rank.val < 277
                  ·
                    have hr : rank = ⟨276, by decide⟩ := Fin.ext (by change rank.val = 276; omega)
                    subst rank
                    exact ⟨Checks.routine276, Checks.ready276.1, Checks.ready276.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨277, by decide⟩ := Fin.ext (by change rank.val = 277; omega)
                    subst rank
                    exact ⟨Checks.routine277, Checks.ready277.1, Checks.ready277.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h279 : rank.val < 279
                  ·
                    have hr : rank = ⟨278, by decide⟩ := Fin.ext (by change rank.val = 278; omega)
                    subst rank
                    exact ⟨Checks.routine278, Checks.ready278.1, Checks.ready278.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h280 : rank.val < 280
                    ·
                      have hr : rank = ⟨279, by decide⟩ := Fin.ext (by change rank.val = 279; omega)
                      subst rank
                      exact ⟨Checks.routine279, Checks.ready279.1, Checks.ready279.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨280, by decide⟩ := Fin.ext (by change rank.val = 280; omega)
                      subst rank
                      exact ⟨Checks.routine280, Checks.ready280.1, Checks.ready280.2, bank_contained_of_all _ (by decide +kernel)⟩
  ·
    by_cases h281 : rank.val < 422
    ·
      by_cases h282 : rank.val < 351
      ·
        by_cases h283 : rank.val < 316
        ·
          by_cases h284 : rank.val < 298
          ·
            by_cases h285 : rank.val < 289
            ·
              by_cases h286 : rank.val < 285
              ·
                by_cases h287 : rank.val < 283
                ·
                  by_cases h288 : rank.val < 282
                  ·
                    have hr : rank = ⟨281, by decide⟩ := Fin.ext (by change rank.val = 281; omega)
                    subst rank
                    exact ⟨Checks.routine281, Checks.ready281.1, Checks.ready281.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨282, by decide⟩ := Fin.ext (by change rank.val = 282; omega)
                    subst rank
                    exact ⟨Checks.routine282, Checks.ready282.1, Checks.ready282.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h289 : rank.val < 284
                  ·
                    have hr : rank = ⟨283, by decide⟩ := Fin.ext (by change rank.val = 283; omega)
                    subst rank
                    exact ⟨Checks.routine283, Checks.ready283.1, Checks.ready283.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨284, by decide⟩ := Fin.ext (by change rank.val = 284; omega)
                    subst rank
                    exact ⟨Checks.routine284, Checks.ready284.1, Checks.ready284.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h290 : rank.val < 287
                ·
                  by_cases h291 : rank.val < 286
                  ·
                    have hr : rank = ⟨285, by decide⟩ := Fin.ext (by change rank.val = 285; omega)
                    subst rank
                    exact ⟨Checks.routine285, Checks.ready285.1, Checks.ready285.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨286, by decide⟩ := Fin.ext (by change rank.val = 286; omega)
                    subst rank
                    exact ⟨Checks.routine286, Checks.ready286.1, Checks.ready286.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h292 : rank.val < 288
                  ·
                    have hr : rank = ⟨287, by decide⟩ := Fin.ext (by change rank.val = 287; omega)
                    subst rank
                    exact ⟨Checks.routine287, Checks.ready287.1, Checks.ready287.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨288, by decide⟩ := Fin.ext (by change rank.val = 288; omega)
                    subst rank
                    exact ⟨Checks.routine288, Checks.ready288.1, Checks.ready288.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h293 : rank.val < 293
              ·
                by_cases h294 : rank.val < 291
                ·
                  by_cases h295 : rank.val < 290
                  ·
                    have hr : rank = ⟨289, by decide⟩ := Fin.ext (by change rank.val = 289; omega)
                    subst rank
                    exact ⟨Checks.routine289, Checks.ready289.1, Checks.ready289.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨290, by decide⟩ := Fin.ext (by change rank.val = 290; omega)
                    subst rank
                    exact ⟨Checks.routine290, Checks.ready290.1, Checks.ready290.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h296 : rank.val < 292
                  ·
                    have hr : rank = ⟨291, by decide⟩ := Fin.ext (by change rank.val = 291; omega)
                    subst rank
                    exact ⟨Checks.routine291, Checks.ready291.1, Checks.ready291.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨292, by decide⟩ := Fin.ext (by change rank.val = 292; omega)
                    subst rank
                    exact ⟨Checks.routine292, Checks.ready292.1, Checks.ready292.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h297 : rank.val < 295
                ·
                  by_cases h298 : rank.val < 294
                  ·
                    have hr : rank = ⟨293, by decide⟩ := Fin.ext (by change rank.val = 293; omega)
                    subst rank
                    exact ⟨Checks.routine293, Checks.ready293.1, Checks.ready293.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨294, by decide⟩ := Fin.ext (by change rank.val = 294; omega)
                    subst rank
                    exact ⟨Checks.routine294, Checks.ready294.1, Checks.ready294.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h299 : rank.val < 296
                  ·
                    have hr : rank = ⟨295, by decide⟩ := Fin.ext (by change rank.val = 295; omega)
                    subst rank
                    exact ⟨Checks.routine295, Checks.ready295.1, Checks.ready295.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h300 : rank.val < 297
                    ·
                      have hr : rank = ⟨296, by decide⟩ := Fin.ext (by change rank.val = 296; omega)
                      subst rank
                      exact ⟨Checks.routine296, Checks.ready296.1, Checks.ready296.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨297, by decide⟩ := Fin.ext (by change rank.val = 297; omega)
                      subst rank
                      exact ⟨Checks.routine297, Checks.ready297.1, Checks.ready297.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h301 : rank.val < 307
            ·
              by_cases h302 : rank.val < 302
              ·
                by_cases h303 : rank.val < 300
                ·
                  by_cases h304 : rank.val < 299
                  ·
                    have hr : rank = ⟨298, by decide⟩ := Fin.ext (by change rank.val = 298; omega)
                    subst rank
                    exact ⟨Checks.routine298, Checks.ready298.1, Checks.ready298.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨299, by decide⟩ := Fin.ext (by change rank.val = 299; omega)
                    subst rank
                    exact ⟨Checks.routine299, Checks.ready299.1, Checks.ready299.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h305 : rank.val < 301
                  ·
                    have hr : rank = ⟨300, by decide⟩ := Fin.ext (by change rank.val = 300; omega)
                    subst rank
                    exact ⟨Checks.routine300, Checks.ready300.1, Checks.ready300.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨301, by decide⟩ := Fin.ext (by change rank.val = 301; omega)
                    subst rank
                    exact ⟨Checks.routine301, Checks.ready301.1, Checks.ready301.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h306 : rank.val < 304
                ·
                  by_cases h307 : rank.val < 303
                  ·
                    have hr : rank = ⟨302, by decide⟩ := Fin.ext (by change rank.val = 302; omega)
                    subst rank
                    exact ⟨Checks.routine302, Checks.ready302.1, Checks.ready302.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨303, by decide⟩ := Fin.ext (by change rank.val = 303; omega)
                    subst rank
                    exact ⟨Checks.routine303, Checks.ready303.1, Checks.ready303.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h308 : rank.val < 305
                  ·
                    have hr : rank = ⟨304, by decide⟩ := Fin.ext (by change rank.val = 304; omega)
                    subst rank
                    exact ⟨Checks.routine304, Checks.ready304.1, Checks.ready304.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h309 : rank.val < 306
                    ·
                      have hr : rank = ⟨305, by decide⟩ := Fin.ext (by change rank.val = 305; omega)
                      subst rank
                      exact ⟨Checks.routine305, Checks.ready305.1, Checks.ready305.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨306, by decide⟩ := Fin.ext (by change rank.val = 306; omega)
                      subst rank
                      exact ⟨Checks.routine306, Checks.ready306.1, Checks.ready306.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h310 : rank.val < 311
              ·
                by_cases h311 : rank.val < 309
                ·
                  by_cases h312 : rank.val < 308
                  ·
                    have hr : rank = ⟨307, by decide⟩ := Fin.ext (by change rank.val = 307; omega)
                    subst rank
                    exact ⟨Checks.routine307, Checks.ready307.1, Checks.ready307.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨308, by decide⟩ := Fin.ext (by change rank.val = 308; omega)
                    subst rank
                    exact ⟨Checks.routine308, Checks.ready308.1, Checks.ready308.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h313 : rank.val < 310
                  ·
                    have hr : rank = ⟨309, by decide⟩ := Fin.ext (by change rank.val = 309; omega)
                    subst rank
                    exact ⟨Checks.routine309, Checks.ready309.1, Checks.ready309.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨310, by decide⟩ := Fin.ext (by change rank.val = 310; omega)
                    subst rank
                    exact ⟨Checks.routine310, Checks.ready310.1, Checks.ready310.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h314 : rank.val < 313
                ·
                  by_cases h315 : rank.val < 312
                  ·
                    have hr : rank = ⟨311, by decide⟩ := Fin.ext (by change rank.val = 311; omega)
                    subst rank
                    exact ⟨Checks.routine311, Checks.ready311.1, Checks.ready311.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨312, by decide⟩ := Fin.ext (by change rank.val = 312; omega)
                    subst rank
                    exact ⟨Checks.routine312, Checks.ready312.1, Checks.ready312.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h316 : rank.val < 314
                  ·
                    have hr : rank = ⟨313, by decide⟩ := Fin.ext (by change rank.val = 313; omega)
                    subst rank
                    exact ⟨Checks.routine313, Checks.ready313.1, Checks.ready313.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h317 : rank.val < 315
                    ·
                      have hr : rank = ⟨314, by decide⟩ := Fin.ext (by change rank.val = 314; omega)
                      subst rank
                      exact ⟨Checks.routine314, Checks.ready314.1, Checks.ready314.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨315, by decide⟩ := Fin.ext (by change rank.val = 315; omega)
                      subst rank
                      exact ⟨Checks.routine315, Checks.ready315.1, Checks.ready315.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h318 : rank.val < 333
          ·
            by_cases h319 : rank.val < 324
            ·
              by_cases h320 : rank.val < 320
              ·
                by_cases h321 : rank.val < 318
                ·
                  by_cases h322 : rank.val < 317
                  ·
                    have hr : rank = ⟨316, by decide⟩ := Fin.ext (by change rank.val = 316; omega)
                    subst rank
                    exact ⟨Checks.routine316, Checks.ready316.1, Checks.ready316.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨317, by decide⟩ := Fin.ext (by change rank.val = 317; omega)
                    subst rank
                    exact ⟨Checks.routine317, Checks.ready317.1, Checks.ready317.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h323 : rank.val < 319
                  ·
                    have hr : rank = ⟨318, by decide⟩ := Fin.ext (by change rank.val = 318; omega)
                    subst rank
                    exact ⟨Checks.routine318, Checks.ready318.1, Checks.ready318.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨319, by decide⟩ := Fin.ext (by change rank.val = 319; omega)
                    subst rank
                    exact ⟨Checks.routine319, Checks.ready319.1, Checks.ready319.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h324 : rank.val < 322
                ·
                  by_cases h325 : rank.val < 321
                  ·
                    have hr : rank = ⟨320, by decide⟩ := Fin.ext (by change rank.val = 320; omega)
                    subst rank
                    exact ⟨Checks.routine320, Checks.ready320.1, Checks.ready320.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨321, by decide⟩ := Fin.ext (by change rank.val = 321; omega)
                    subst rank
                    exact ⟨Checks.routine321, Checks.ready321.1, Checks.ready321.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h326 : rank.val < 323
                  ·
                    have hr : rank = ⟨322, by decide⟩ := Fin.ext (by change rank.val = 322; omega)
                    subst rank
                    exact ⟨Checks.routine322, Checks.ready322.1, Checks.ready322.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨323, by decide⟩ := Fin.ext (by change rank.val = 323; omega)
                    subst rank
                    exact ⟨Checks.routine323, Checks.ready323.1, Checks.ready323.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h327 : rank.val < 328
              ·
                by_cases h328 : rank.val < 326
                ·
                  by_cases h329 : rank.val < 325
                  ·
                    have hr : rank = ⟨324, by decide⟩ := Fin.ext (by change rank.val = 324; omega)
                    subst rank
                    exact ⟨Checks.routine324, Checks.ready324.1, Checks.ready324.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨325, by decide⟩ := Fin.ext (by change rank.val = 325; omega)
                    subst rank
                    exact ⟨Checks.routine325, Checks.ready325.1, Checks.ready325.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h330 : rank.val < 327
                  ·
                    have hr : rank = ⟨326, by decide⟩ := Fin.ext (by change rank.val = 326; omega)
                    subst rank
                    exact ⟨Checks.routine326, Checks.ready326.1, Checks.ready326.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨327, by decide⟩ := Fin.ext (by change rank.val = 327; omega)
                    subst rank
                    exact ⟨Checks.routine327, Checks.ready327.1, Checks.ready327.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h331 : rank.val < 330
                ·
                  by_cases h332 : rank.val < 329
                  ·
                    have hr : rank = ⟨328, by decide⟩ := Fin.ext (by change rank.val = 328; omega)
                    subst rank
                    exact ⟨Checks.routine328, Checks.ready328.1, Checks.ready328.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨329, by decide⟩ := Fin.ext (by change rank.val = 329; omega)
                    subst rank
                    exact ⟨Checks.routine329, Checks.ready329.1, Checks.ready329.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h333 : rank.val < 331
                  ·
                    have hr : rank = ⟨330, by decide⟩ := Fin.ext (by change rank.val = 330; omega)
                    subst rank
                    exact ⟨Checks.routine330, Checks.ready330.1, Checks.ready330.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h334 : rank.val < 332
                    ·
                      have hr : rank = ⟨331, by decide⟩ := Fin.ext (by change rank.val = 331; omega)
                      subst rank
                      exact ⟨Checks.routine331, Checks.ready331.1, Checks.ready331.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨332, by decide⟩ := Fin.ext (by change rank.val = 332; omega)
                      subst rank
                      exact ⟨Checks.routine332, Checks.ready332.1, Checks.ready332.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h335 : rank.val < 342
            ·
              by_cases h336 : rank.val < 337
              ·
                by_cases h337 : rank.val < 335
                ·
                  by_cases h338 : rank.val < 334
                  ·
                    have hr : rank = ⟨333, by decide⟩ := Fin.ext (by change rank.val = 333; omega)
                    subst rank
                    exact ⟨Checks.routine333, Checks.ready333.1, Checks.ready333.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨334, by decide⟩ := Fin.ext (by change rank.val = 334; omega)
                    subst rank
                    exact ⟨Checks.routine334, Checks.ready334.1, Checks.ready334.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h339 : rank.val < 336
                  ·
                    have hr : rank = ⟨335, by decide⟩ := Fin.ext (by change rank.val = 335; omega)
                    subst rank
                    exact ⟨Checks.routine335, Checks.ready335.1, Checks.ready335.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨336, by decide⟩ := Fin.ext (by change rank.val = 336; omega)
                    subst rank
                    exact ⟨Checks.routine336, Checks.ready336.1, Checks.ready336.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h340 : rank.val < 339
                ·
                  by_cases h341 : rank.val < 338
                  ·
                    have hr : rank = ⟨337, by decide⟩ := Fin.ext (by change rank.val = 337; omega)
                    subst rank
                    exact ⟨Checks.routine337, Checks.ready337.1, Checks.ready337.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨338, by decide⟩ := Fin.ext (by change rank.val = 338; omega)
                    subst rank
                    exact ⟨Checks.routine338, Checks.ready338.1, Checks.ready338.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h342 : rank.val < 340
                  ·
                    have hr : rank = ⟨339, by decide⟩ := Fin.ext (by change rank.val = 339; omega)
                    subst rank
                    exact ⟨Checks.routine339, Checks.ready339.1, Checks.ready339.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h343 : rank.val < 341
                    ·
                      have hr : rank = ⟨340, by decide⟩ := Fin.ext (by change rank.val = 340; omega)
                      subst rank
                      exact ⟨Checks.routine340, Checks.ready340.1, Checks.ready340.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨341, by decide⟩ := Fin.ext (by change rank.val = 341; omega)
                      subst rank
                      exact ⟨Checks.routine341, Checks.ready341.1, Checks.ready341.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h344 : rank.val < 346
              ·
                by_cases h345 : rank.val < 344
                ·
                  by_cases h346 : rank.val < 343
                  ·
                    have hr : rank = ⟨342, by decide⟩ := Fin.ext (by change rank.val = 342; omega)
                    subst rank
                    exact ⟨Checks.routine342, Checks.ready342.1, Checks.ready342.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨343, by decide⟩ := Fin.ext (by change rank.val = 343; omega)
                    subst rank
                    exact ⟨Checks.routine343, Checks.ready343.1, Checks.ready343.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h347 : rank.val < 345
                  ·
                    have hr : rank = ⟨344, by decide⟩ := Fin.ext (by change rank.val = 344; omega)
                    subst rank
                    exact ⟨Checks.routine344, Checks.ready344.1, Checks.ready344.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨345, by decide⟩ := Fin.ext (by change rank.val = 345; omega)
                    subst rank
                    exact ⟨Checks.routine345, Checks.ready345.1, Checks.ready345.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h348 : rank.val < 348
                ·
                  by_cases h349 : rank.val < 347
                  ·
                    have hr : rank = ⟨346, by decide⟩ := Fin.ext (by change rank.val = 346; omega)
                    subst rank
                    exact ⟨Checks.routine346, Checks.ready346.1, Checks.ready346.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨347, by decide⟩ := Fin.ext (by change rank.val = 347; omega)
                    subst rank
                    exact ⟨Checks.routine347, Checks.ready347.1, Checks.ready347.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h350 : rank.val < 349
                  ·
                    have hr : rank = ⟨348, by decide⟩ := Fin.ext (by change rank.val = 348; omega)
                    subst rank
                    exact ⟨Checks.routine348, Checks.ready348.1, Checks.ready348.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h351 : rank.val < 350
                    ·
                      have hr : rank = ⟨349, by decide⟩ := Fin.ext (by change rank.val = 349; omega)
                      subst rank
                      exact ⟨Checks.routine349, Checks.ready349.1, Checks.ready349.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨350, by decide⟩ := Fin.ext (by change rank.val = 350; omega)
                      subst rank
                      exact ⟨Checks.routine350, Checks.ready350.1, Checks.ready350.2, bank_contained_of_all _ (by decide +kernel)⟩
      ·
        by_cases h352 : rank.val < 386
        ·
          by_cases h353 : rank.val < 368
          ·
            by_cases h354 : rank.val < 359
            ·
              by_cases h355 : rank.val < 355
              ·
                by_cases h356 : rank.val < 353
                ·
                  by_cases h357 : rank.val < 352
                  ·
                    have hr : rank = ⟨351, by decide⟩ := Fin.ext (by change rank.val = 351; omega)
                    subst rank
                    exact ⟨Checks.routine351, Checks.ready351.1, Checks.ready351.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨352, by decide⟩ := Fin.ext (by change rank.val = 352; omega)
                    subst rank
                    exact ⟨Checks.routine352, Checks.ready352.1, Checks.ready352.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h358 : rank.val < 354
                  ·
                    have hr : rank = ⟨353, by decide⟩ := Fin.ext (by change rank.val = 353; omega)
                    subst rank
                    exact ⟨Checks.routine353, Checks.ready353.1, Checks.ready353.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨354, by decide⟩ := Fin.ext (by change rank.val = 354; omega)
                    subst rank
                    exact ⟨Checks.routine354, Checks.ready354.1, Checks.ready354.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h359 : rank.val < 357
                ·
                  by_cases h360 : rank.val < 356
                  ·
                    have hr : rank = ⟨355, by decide⟩ := Fin.ext (by change rank.val = 355; omega)
                    subst rank
                    exact ⟨Checks.routine355, Checks.ready355.1, Checks.ready355.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨356, by decide⟩ := Fin.ext (by change rank.val = 356; omega)
                    subst rank
                    exact ⟨Checks.routine356, Checks.ready356.1, Checks.ready356.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h361 : rank.val < 358
                  ·
                    have hr : rank = ⟨357, by decide⟩ := Fin.ext (by change rank.val = 357; omega)
                    subst rank
                    exact ⟨Checks.routine357, Checks.ready357.1, Checks.ready357.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨358, by decide⟩ := Fin.ext (by change rank.val = 358; omega)
                    subst rank
                    exact ⟨Checks.routine358, Checks.ready358.1, Checks.ready358.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h362 : rank.val < 363
              ·
                by_cases h363 : rank.val < 361
                ·
                  by_cases h364 : rank.val < 360
                  ·
                    have hr : rank = ⟨359, by decide⟩ := Fin.ext (by change rank.val = 359; omega)
                    subst rank
                    exact ⟨Checks.routine359, Checks.ready359.1, Checks.ready359.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨360, by decide⟩ := Fin.ext (by change rank.val = 360; omega)
                    subst rank
                    exact ⟨Checks.routine360, Checks.ready360.1, Checks.ready360.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h365 : rank.val < 362
                  ·
                    have hr : rank = ⟨361, by decide⟩ := Fin.ext (by change rank.val = 361; omega)
                    subst rank
                    exact ⟨Checks.routine361, Checks.ready361.1, Checks.ready361.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨362, by decide⟩ := Fin.ext (by change rank.val = 362; omega)
                    subst rank
                    exact ⟨Checks.routine362, Checks.ready362.1, Checks.ready362.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h366 : rank.val < 365
                ·
                  by_cases h367 : rank.val < 364
                  ·
                    have hr : rank = ⟨363, by decide⟩ := Fin.ext (by change rank.val = 363; omega)
                    subst rank
                    exact ⟨Checks.routine363, Checks.ready363.1, Checks.ready363.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨364, by decide⟩ := Fin.ext (by change rank.val = 364; omega)
                    subst rank
                    exact ⟨Checks.routine364, Checks.ready364.1, Checks.ready364.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h368 : rank.val < 366
                  ·
                    have hr : rank = ⟨365, by decide⟩ := Fin.ext (by change rank.val = 365; omega)
                    subst rank
                    exact ⟨Checks.routine365, Checks.ready365.1, Checks.ready365.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h369 : rank.val < 367
                    ·
                      have hr : rank = ⟨366, by decide⟩ := Fin.ext (by change rank.val = 366; omega)
                      subst rank
                      exact ⟨Checks.routine366, Checks.ready366.1, Checks.ready366.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨367, by decide⟩ := Fin.ext (by change rank.val = 367; omega)
                      subst rank
                      exact ⟨Checks.routine367, Checks.ready367.1, Checks.ready367.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h370 : rank.val < 377
            ·
              by_cases h371 : rank.val < 372
              ·
                by_cases h372 : rank.val < 370
                ·
                  by_cases h373 : rank.val < 369
                  ·
                    have hr : rank = ⟨368, by decide⟩ := Fin.ext (by change rank.val = 368; omega)
                    subst rank
                    exact ⟨Checks.routine368, Checks.ready368.1, Checks.ready368.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨369, by decide⟩ := Fin.ext (by change rank.val = 369; omega)
                    subst rank
                    exact ⟨Checks.routine369, Checks.ready369.1, Checks.ready369.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h374 : rank.val < 371
                  ·
                    have hr : rank = ⟨370, by decide⟩ := Fin.ext (by change rank.val = 370; omega)
                    subst rank
                    exact ⟨Checks.routine370, Checks.ready370.1, Checks.ready370.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨371, by decide⟩ := Fin.ext (by change rank.val = 371; omega)
                    subst rank
                    exact ⟨Checks.routine371, Checks.ready371.1, Checks.ready371.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h375 : rank.val < 374
                ·
                  by_cases h376 : rank.val < 373
                  ·
                    have hr : rank = ⟨372, by decide⟩ := Fin.ext (by change rank.val = 372; omega)
                    subst rank
                    exact ⟨Checks.routine372, Checks.ready372.1, Checks.ready372.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨373, by decide⟩ := Fin.ext (by change rank.val = 373; omega)
                    subst rank
                    exact ⟨Checks.routine373, Checks.ready373.1, Checks.ready373.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h377 : rank.val < 375
                  ·
                    have hr : rank = ⟨374, by decide⟩ := Fin.ext (by change rank.val = 374; omega)
                    subst rank
                    exact ⟨Checks.routine374, Checks.ready374.1, Checks.ready374.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h378 : rank.val < 376
                    ·
                      have hr : rank = ⟨375, by decide⟩ := Fin.ext (by change rank.val = 375; omega)
                      subst rank
                      exact ⟨Checks.routine375, Checks.ready375.1, Checks.ready375.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨376, by decide⟩ := Fin.ext (by change rank.val = 376; omega)
                      subst rank
                      exact ⟨Checks.routine376, Checks.ready376.1, Checks.ready376.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h379 : rank.val < 381
              ·
                by_cases h380 : rank.val < 379
                ·
                  by_cases h381 : rank.val < 378
                  ·
                    have hr : rank = ⟨377, by decide⟩ := Fin.ext (by change rank.val = 377; omega)
                    subst rank
                    exact ⟨Checks.routine377, Checks.ready377.1, Checks.ready377.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨378, by decide⟩ := Fin.ext (by change rank.val = 378; omega)
                    subst rank
                    exact ⟨Checks.routine378, Checks.ready378.1, Checks.ready378.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h382 : rank.val < 380
                  ·
                    have hr : rank = ⟨379, by decide⟩ := Fin.ext (by change rank.val = 379; omega)
                    subst rank
                    exact ⟨Checks.routine379, Checks.ready379.1, Checks.ready379.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨380, by decide⟩ := Fin.ext (by change rank.val = 380; omega)
                    subst rank
                    exact ⟨Checks.routine380, Checks.ready380.1, Checks.ready380.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h383 : rank.val < 383
                ·
                  by_cases h384 : rank.val < 382
                  ·
                    have hr : rank = ⟨381, by decide⟩ := Fin.ext (by change rank.val = 381; omega)
                    subst rank
                    exact ⟨Checks.routine381, Checks.ready381.1, Checks.ready381.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨382, by decide⟩ := Fin.ext (by change rank.val = 382; omega)
                    subst rank
                    exact ⟨Checks.routine382, Checks.ready382.1, Checks.ready382.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h385 : rank.val < 384
                  ·
                    have hr : rank = ⟨383, by decide⟩ := Fin.ext (by change rank.val = 383; omega)
                    subst rank
                    exact ⟨Checks.routine383, Checks.ready383.1, Checks.ready383.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h386 : rank.val < 385
                    ·
                      have hr : rank = ⟨384, by decide⟩ := Fin.ext (by change rank.val = 384; omega)
                      subst rank
                      exact ⟨Checks.routine384, Checks.ready384.1, Checks.ready384.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨385, by decide⟩ := Fin.ext (by change rank.val = 385; omega)
                      subst rank
                      exact ⟨Checks.routine385, Checks.ready385.1, Checks.ready385.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h387 : rank.val < 404
          ·
            by_cases h388 : rank.val < 395
            ·
              by_cases h389 : rank.val < 390
              ·
                by_cases h390 : rank.val < 388
                ·
                  by_cases h391 : rank.val < 387
                  ·
                    have hr : rank = ⟨386, by decide⟩ := Fin.ext (by change rank.val = 386; omega)
                    subst rank
                    exact ⟨Checks.routine386, Checks.ready386.1, Checks.ready386.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨387, by decide⟩ := Fin.ext (by change rank.val = 387; omega)
                    subst rank
                    exact ⟨Checks.routine387, Checks.ready387.1, Checks.ready387.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h392 : rank.val < 389
                  ·
                    have hr : rank = ⟨388, by decide⟩ := Fin.ext (by change rank.val = 388; omega)
                    subst rank
                    exact ⟨Checks.routine388, Checks.ready388.1, Checks.ready388.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨389, by decide⟩ := Fin.ext (by change rank.val = 389; omega)
                    subst rank
                    exact ⟨Checks.routine389, Checks.ready389.1, Checks.ready389.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h393 : rank.val < 392
                ·
                  by_cases h394 : rank.val < 391
                  ·
                    have hr : rank = ⟨390, by decide⟩ := Fin.ext (by change rank.val = 390; omega)
                    subst rank
                    exact ⟨Checks.routine390, Checks.ready390.1, Checks.ready390.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨391, by decide⟩ := Fin.ext (by change rank.val = 391; omega)
                    subst rank
                    exact ⟨Checks.routine391, Checks.ready391.1, Checks.ready391.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h395 : rank.val < 393
                  ·
                    have hr : rank = ⟨392, by decide⟩ := Fin.ext (by change rank.val = 392; omega)
                    subst rank
                    exact ⟨Checks.routine392, Checks.ready392.1, Checks.ready392.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h396 : rank.val < 394
                    ·
                      have hr : rank = ⟨393, by decide⟩ := Fin.ext (by change rank.val = 393; omega)
                      subst rank
                      exact ⟨Checks.routine393, Checks.ready393.1, Checks.ready393.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨394, by decide⟩ := Fin.ext (by change rank.val = 394; omega)
                      subst rank
                      exact ⟨Checks.routine394, Checks.ready394.1, Checks.ready394.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h397 : rank.val < 399
              ·
                by_cases h398 : rank.val < 397
                ·
                  by_cases h399 : rank.val < 396
                  ·
                    have hr : rank = ⟨395, by decide⟩ := Fin.ext (by change rank.val = 395; omega)
                    subst rank
                    exact ⟨Checks.routine395, Checks.ready395.1, Checks.ready395.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨396, by decide⟩ := Fin.ext (by change rank.val = 396; omega)
                    subst rank
                    exact ⟨Checks.routine396, Checks.ready396.1, Checks.ready396.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h400 : rank.val < 398
                  ·
                    have hr : rank = ⟨397, by decide⟩ := Fin.ext (by change rank.val = 397; omega)
                    subst rank
                    exact ⟨Checks.routine397, Checks.ready397.1, Checks.ready397.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨398, by decide⟩ := Fin.ext (by change rank.val = 398; omega)
                    subst rank
                    exact ⟨Checks.routine398, Checks.ready398.1, Checks.ready398.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h401 : rank.val < 401
                ·
                  by_cases h402 : rank.val < 400
                  ·
                    have hr : rank = ⟨399, by decide⟩ := Fin.ext (by change rank.val = 399; omega)
                    subst rank
                    exact ⟨Checks.routine399, Checks.ready399.1, Checks.ready399.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨400, by decide⟩ := Fin.ext (by change rank.val = 400; omega)
                    subst rank
                    exact ⟨Checks.routine400, Checks.ready400.1, Checks.ready400.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h403 : rank.val < 402
                  ·
                    have hr : rank = ⟨401, by decide⟩ := Fin.ext (by change rank.val = 401; omega)
                    subst rank
                    exact ⟨Checks.routine401, Checks.ready401.1, Checks.ready401.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h404 : rank.val < 403
                    ·
                      have hr : rank = ⟨402, by decide⟩ := Fin.ext (by change rank.val = 402; omega)
                      subst rank
                      exact ⟨Checks.routine402, Checks.ready402.1, Checks.ready402.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨403, by decide⟩ := Fin.ext (by change rank.val = 403; omega)
                      subst rank
                      exact ⟨Checks.routine403, Checks.ready403.1, Checks.ready403.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h405 : rank.val < 413
            ·
              by_cases h406 : rank.val < 408
              ·
                by_cases h407 : rank.val < 406
                ·
                  by_cases h408 : rank.val < 405
                  ·
                    have hr : rank = ⟨404, by decide⟩ := Fin.ext (by change rank.val = 404; omega)
                    subst rank
                    exact ⟨Checks.routine404, Checks.ready404.1, Checks.ready404.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨405, by decide⟩ := Fin.ext (by change rank.val = 405; omega)
                    subst rank
                    exact ⟨Checks.routine405, Checks.ready405.1, Checks.ready405.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h409 : rank.val < 407
                  ·
                    have hr : rank = ⟨406, by decide⟩ := Fin.ext (by change rank.val = 406; omega)
                    subst rank
                    exact ⟨Checks.routine406, Checks.ready406.1, Checks.ready406.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨407, by decide⟩ := Fin.ext (by change rank.val = 407; omega)
                    subst rank
                    exact ⟨Checks.routine407, Checks.ready407.1, Checks.ready407.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h410 : rank.val < 410
                ·
                  by_cases h411 : rank.val < 409
                  ·
                    have hr : rank = ⟨408, by decide⟩ := Fin.ext (by change rank.val = 408; omega)
                    subst rank
                    exact ⟨Checks.routine408, Checks.ready408.1, Checks.ready408.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨409, by decide⟩ := Fin.ext (by change rank.val = 409; omega)
                    subst rank
                    exact ⟨Checks.routine409, Checks.ready409.1, Checks.ready409.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h412 : rank.val < 411
                  ·
                    have hr : rank = ⟨410, by decide⟩ := Fin.ext (by change rank.val = 410; omega)
                    subst rank
                    exact ⟨Checks.routine410, Checks.ready410.1, Checks.ready410.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h413 : rank.val < 412
                    ·
                      have hr : rank = ⟨411, by decide⟩ := Fin.ext (by change rank.val = 411; omega)
                      subst rank
                      exact ⟨Checks.routine411, Checks.ready411.1, Checks.ready411.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨412, by decide⟩ := Fin.ext (by change rank.val = 412; omega)
                      subst rank
                      exact ⟨Checks.routine412, Checks.ready412.1, Checks.ready412.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h414 : rank.val < 417
              ·
                by_cases h415 : rank.val < 415
                ·
                  by_cases h416 : rank.val < 414
                  ·
                    have hr : rank = ⟨413, by decide⟩ := Fin.ext (by change rank.val = 413; omega)
                    subst rank
                    exact ⟨Checks.routine413, Checks.ready413.1, Checks.ready413.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨414, by decide⟩ := Fin.ext (by change rank.val = 414; omega)
                    subst rank
                    exact ⟨Checks.routine414, Checks.ready414.1, Checks.ready414.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h417 : rank.val < 416
                  ·
                    have hr : rank = ⟨415, by decide⟩ := Fin.ext (by change rank.val = 415; omega)
                    subst rank
                    exact ⟨Checks.routine415, Checks.ready415.1, Checks.ready415.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨416, by decide⟩ := Fin.ext (by change rank.val = 416; omega)
                    subst rank
                    exact ⟨Checks.routine416, Checks.ready416.1, Checks.ready416.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h418 : rank.val < 419
                ·
                  by_cases h419 : rank.val < 418
                  ·
                    have hr : rank = ⟨417, by decide⟩ := Fin.ext (by change rank.val = 417; omega)
                    subst rank
                    exact ⟨Checks.routine417, Checks.ready417.1, Checks.ready417.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨418, by decide⟩ := Fin.ext (by change rank.val = 418; omega)
                    subst rank
                    exact ⟨Checks.routine418, Checks.ready418.1, Checks.ready418.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h420 : rank.val < 420
                  ·
                    have hr : rank = ⟨419, by decide⟩ := Fin.ext (by change rank.val = 419; omega)
                    subst rank
                    exact ⟨Checks.routine419, Checks.ready419.1, Checks.ready419.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h421 : rank.val < 421
                    ·
                      have hr : rank = ⟨420, by decide⟩ := Fin.ext (by change rank.val = 420; omega)
                      subst rank
                      exact ⟨Checks.routine420, Checks.ready420.1, Checks.ready420.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨421, by decide⟩ := Fin.ext (by change rank.val = 421; omega)
                      subst rank
                      exact ⟨Checks.routine421, Checks.ready421.1, Checks.ready421.2, bank_contained_of_all _ (by decide +kernel)⟩
    ·
      by_cases h422 : rank.val < 492
      ·
        by_cases h423 : rank.val < 457
        ·
          by_cases h424 : rank.val < 439
          ·
            by_cases h425 : rank.val < 430
            ·
              by_cases h426 : rank.val < 426
              ·
                by_cases h427 : rank.val < 424
                ·
                  by_cases h428 : rank.val < 423
                  ·
                    have hr : rank = ⟨422, by decide⟩ := Fin.ext (by change rank.val = 422; omega)
                    subst rank
                    exact ⟨Checks.routine422, Checks.ready422.1, Checks.ready422.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨423, by decide⟩ := Fin.ext (by change rank.val = 423; omega)
                    subst rank
                    exact ⟨Checks.routine423, Checks.ready423.1, Checks.ready423.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h429 : rank.val < 425
                  ·
                    have hr : rank = ⟨424, by decide⟩ := Fin.ext (by change rank.val = 424; omega)
                    subst rank
                    exact ⟨Checks.routine424, Checks.ready424.1, Checks.ready424.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨425, by decide⟩ := Fin.ext (by change rank.val = 425; omega)
                    subst rank
                    exact ⟨Checks.routine425, Checks.ready425.1, Checks.ready425.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h430 : rank.val < 428
                ·
                  by_cases h431 : rank.val < 427
                  ·
                    have hr : rank = ⟨426, by decide⟩ := Fin.ext (by change rank.val = 426; omega)
                    subst rank
                    exact ⟨Checks.routine426, Checks.ready426.1, Checks.ready426.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨427, by decide⟩ := Fin.ext (by change rank.val = 427; omega)
                    subst rank
                    exact ⟨Checks.routine427, Checks.ready427.1, Checks.ready427.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h432 : rank.val < 429
                  ·
                    have hr : rank = ⟨428, by decide⟩ := Fin.ext (by change rank.val = 428; omega)
                    subst rank
                    exact ⟨Checks.routine428, Checks.ready428.1, Checks.ready428.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨429, by decide⟩ := Fin.ext (by change rank.val = 429; omega)
                    subst rank
                    exact ⟨Checks.routine429, Checks.ready429.1, Checks.ready429.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h433 : rank.val < 434
              ·
                by_cases h434 : rank.val < 432
                ·
                  by_cases h435 : rank.val < 431
                  ·
                    have hr : rank = ⟨430, by decide⟩ := Fin.ext (by change rank.val = 430; omega)
                    subst rank
                    exact ⟨Checks.routine430, Checks.ready430.1, Checks.ready430.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨431, by decide⟩ := Fin.ext (by change rank.val = 431; omega)
                    subst rank
                    exact ⟨Checks.routine431, Checks.ready431.1, Checks.ready431.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h436 : rank.val < 433
                  ·
                    have hr : rank = ⟨432, by decide⟩ := Fin.ext (by change rank.val = 432; omega)
                    subst rank
                    exact ⟨Checks.routine432, Checks.ready432.1, Checks.ready432.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨433, by decide⟩ := Fin.ext (by change rank.val = 433; omega)
                    subst rank
                    exact ⟨Checks.routine433, Checks.ready433.1, Checks.ready433.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h437 : rank.val < 436
                ·
                  by_cases h438 : rank.val < 435
                  ·
                    have hr : rank = ⟨434, by decide⟩ := Fin.ext (by change rank.val = 434; omega)
                    subst rank
                    exact ⟨Checks.routine434, Checks.ready434.1, Checks.ready434.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨435, by decide⟩ := Fin.ext (by change rank.val = 435; omega)
                    subst rank
                    exact ⟨Checks.routine435, Checks.ready435.1, Checks.ready435.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h439 : rank.val < 437
                  ·
                    have hr : rank = ⟨436, by decide⟩ := Fin.ext (by change rank.val = 436; omega)
                    subst rank
                    exact ⟨Checks.routine436, Checks.ready436.1, Checks.ready436.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h440 : rank.val < 438
                    ·
                      have hr : rank = ⟨437, by decide⟩ := Fin.ext (by change rank.val = 437; omega)
                      subst rank
                      exact ⟨Checks.routine437, Checks.ready437.1, Checks.ready437.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨438, by decide⟩ := Fin.ext (by change rank.val = 438; omega)
                      subst rank
                      exact ⟨Checks.routine438, Checks.ready438.1, Checks.ready438.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h441 : rank.val < 448
            ·
              by_cases h442 : rank.val < 443
              ·
                by_cases h443 : rank.val < 441
                ·
                  by_cases h444 : rank.val < 440
                  ·
                    have hr : rank = ⟨439, by decide⟩ := Fin.ext (by change rank.val = 439; omega)
                    subst rank
                    exact ⟨Checks.routine439, Checks.ready439.1, Checks.ready439.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨440, by decide⟩ := Fin.ext (by change rank.val = 440; omega)
                    subst rank
                    exact ⟨Checks.routine440, Checks.ready440.1, Checks.ready440.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h445 : rank.val < 442
                  ·
                    have hr : rank = ⟨441, by decide⟩ := Fin.ext (by change rank.val = 441; omega)
                    subst rank
                    exact ⟨Checks.routine441, Checks.ready441.1, Checks.ready441.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨442, by decide⟩ := Fin.ext (by change rank.val = 442; omega)
                    subst rank
                    exact ⟨Checks.routine442, Checks.ready442.1, Checks.ready442.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h446 : rank.val < 445
                ·
                  by_cases h447 : rank.val < 444
                  ·
                    have hr : rank = ⟨443, by decide⟩ := Fin.ext (by change rank.val = 443; omega)
                    subst rank
                    exact ⟨Checks.routine443, Checks.ready443.1, Checks.ready443.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨444, by decide⟩ := Fin.ext (by change rank.val = 444; omega)
                    subst rank
                    exact ⟨Checks.routine444, Checks.ready444.1, Checks.ready444.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h448 : rank.val < 446
                  ·
                    have hr : rank = ⟨445, by decide⟩ := Fin.ext (by change rank.val = 445; omega)
                    subst rank
                    exact ⟨Checks.routine445, Checks.ready445.1, Checks.ready445.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h449 : rank.val < 447
                    ·
                      have hr : rank = ⟨446, by decide⟩ := Fin.ext (by change rank.val = 446; omega)
                      subst rank
                      exact ⟨Checks.routine446, Checks.ready446.1, Checks.ready446.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨447, by decide⟩ := Fin.ext (by change rank.val = 447; omega)
                      subst rank
                      exact ⟨Checks.routine447, Checks.ready447.1, Checks.ready447.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h450 : rank.val < 452
              ·
                by_cases h451 : rank.val < 450
                ·
                  by_cases h452 : rank.val < 449
                  ·
                    have hr : rank = ⟨448, by decide⟩ := Fin.ext (by change rank.val = 448; omega)
                    subst rank
                    exact ⟨Checks.routine448, Checks.ready448.1, Checks.ready448.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨449, by decide⟩ := Fin.ext (by change rank.val = 449; omega)
                    subst rank
                    exact ⟨Checks.routine449, Checks.ready449.1, Checks.ready449.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h453 : rank.val < 451
                  ·
                    have hr : rank = ⟨450, by decide⟩ := Fin.ext (by change rank.val = 450; omega)
                    subst rank
                    exact ⟨Checks.routine450, Checks.ready450.1, Checks.ready450.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨451, by decide⟩ := Fin.ext (by change rank.val = 451; omega)
                    subst rank
                    exact ⟨Checks.routine451, Checks.ready451.1, Checks.ready451.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h454 : rank.val < 454
                ·
                  by_cases h455 : rank.val < 453
                  ·
                    have hr : rank = ⟨452, by decide⟩ := Fin.ext (by change rank.val = 452; omega)
                    subst rank
                    exact ⟨Checks.routine452, Checks.ready452.1, Checks.ready452.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨453, by decide⟩ := Fin.ext (by change rank.val = 453; omega)
                    subst rank
                    exact ⟨Checks.routine453, Checks.ready453.1, Checks.ready453.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h456 : rank.val < 455
                  ·
                    have hr : rank = ⟨454, by decide⟩ := Fin.ext (by change rank.val = 454; omega)
                    subst rank
                    exact ⟨Checks.routine454, Checks.ready454.1, Checks.ready454.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h457 : rank.val < 456
                    ·
                      have hr : rank = ⟨455, by decide⟩ := Fin.ext (by change rank.val = 455; omega)
                      subst rank
                      exact ⟨Checks.routine455, Checks.ready455.1, Checks.ready455.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨456, by decide⟩ := Fin.ext (by change rank.val = 456; omega)
                      subst rank
                      exact ⟨Checks.routine456, Checks.ready456.1, Checks.ready456.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h458 : rank.val < 474
          ·
            by_cases h459 : rank.val < 465
            ·
              by_cases h460 : rank.val < 461
              ·
                by_cases h461 : rank.val < 459
                ·
                  by_cases h462 : rank.val < 458
                  ·
                    have hr : rank = ⟨457, by decide⟩ := Fin.ext (by change rank.val = 457; omega)
                    subst rank
                    exact ⟨Checks.routine457, Checks.ready457.1, Checks.ready457.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨458, by decide⟩ := Fin.ext (by change rank.val = 458; omega)
                    subst rank
                    exact ⟨Checks.routine458, Checks.ready458.1, Checks.ready458.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h463 : rank.val < 460
                  ·
                    have hr : rank = ⟨459, by decide⟩ := Fin.ext (by change rank.val = 459; omega)
                    subst rank
                    exact ⟨Checks.routine459, Checks.ready459.1, Checks.ready459.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨460, by decide⟩ := Fin.ext (by change rank.val = 460; omega)
                    subst rank
                    exact ⟨Checks.routine460, Checks.ready460.1, Checks.ready460.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h464 : rank.val < 463
                ·
                  by_cases h465 : rank.val < 462
                  ·
                    have hr : rank = ⟨461, by decide⟩ := Fin.ext (by change rank.val = 461; omega)
                    subst rank
                    exact ⟨Checks.routine461, Checks.ready461.1, Checks.ready461.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨462, by decide⟩ := Fin.ext (by change rank.val = 462; omega)
                    subst rank
                    exact ⟨Checks.routine462, Checks.ready462.1, Checks.ready462.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h466 : rank.val < 464
                  ·
                    have hr : rank = ⟨463, by decide⟩ := Fin.ext (by change rank.val = 463; omega)
                    subst rank
                    exact ⟨Checks.routine463, Checks.ready463.1, Checks.ready463.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨464, by decide⟩ := Fin.ext (by change rank.val = 464; omega)
                    subst rank
                    exact ⟨Checks.routine464, Checks.ready464.1, Checks.ready464.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h467 : rank.val < 469
              ·
                by_cases h468 : rank.val < 467
                ·
                  by_cases h469 : rank.val < 466
                  ·
                    have hr : rank = ⟨465, by decide⟩ := Fin.ext (by change rank.val = 465; omega)
                    subst rank
                    exact ⟨Checks.routine465, Checks.ready465.1, Checks.ready465.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨466, by decide⟩ := Fin.ext (by change rank.val = 466; omega)
                    subst rank
                    exact ⟨Checks.routine466, Checks.ready466.1, Checks.ready466.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h470 : rank.val < 468
                  ·
                    have hr : rank = ⟨467, by decide⟩ := Fin.ext (by change rank.val = 467; omega)
                    subst rank
                    exact ⟨Checks.routine467, Checks.ready467.1, Checks.ready467.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨468, by decide⟩ := Fin.ext (by change rank.val = 468; omega)
                    subst rank
                    exact ⟨Checks.routine468, Checks.ready468.1, Checks.ready468.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h471 : rank.val < 471
                ·
                  by_cases h472 : rank.val < 470
                  ·
                    have hr : rank = ⟨469, by decide⟩ := Fin.ext (by change rank.val = 469; omega)
                    subst rank
                    exact ⟨Checks.routine469, Checks.ready469.1, Checks.ready469.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨470, by decide⟩ := Fin.ext (by change rank.val = 470; omega)
                    subst rank
                    exact ⟨Checks.routine470, Checks.ready470.1, Checks.ready470.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h473 : rank.val < 472
                  ·
                    have hr : rank = ⟨471, by decide⟩ := Fin.ext (by change rank.val = 471; omega)
                    subst rank
                    exact ⟨Checks.routine471, Checks.ready471.1, Checks.ready471.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h474 : rank.val < 473
                    ·
                      have hr : rank = ⟨472, by decide⟩ := Fin.ext (by change rank.val = 472; omega)
                      subst rank
                      exact ⟨Checks.routine472, Checks.ready472.1, Checks.ready472.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨473, by decide⟩ := Fin.ext (by change rank.val = 473; omega)
                      subst rank
                      exact ⟨Checks.routine473, Checks.ready473.1, Checks.ready473.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h475 : rank.val < 483
            ·
              by_cases h476 : rank.val < 478
              ·
                by_cases h477 : rank.val < 476
                ·
                  by_cases h478 : rank.val < 475
                  ·
                    have hr : rank = ⟨474, by decide⟩ := Fin.ext (by change rank.val = 474; omega)
                    subst rank
                    exact ⟨Checks.routine474, Checks.ready474.1, Checks.ready474.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨475, by decide⟩ := Fin.ext (by change rank.val = 475; omega)
                    subst rank
                    exact ⟨Checks.routine475, Checks.ready475.1, Checks.ready475.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h479 : rank.val < 477
                  ·
                    have hr : rank = ⟨476, by decide⟩ := Fin.ext (by change rank.val = 476; omega)
                    subst rank
                    exact ⟨Checks.routine476, Checks.ready476.1, Checks.ready476.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨477, by decide⟩ := Fin.ext (by change rank.val = 477; omega)
                    subst rank
                    exact ⟨Checks.routine477, Checks.ready477.1, Checks.ready477.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h480 : rank.val < 480
                ·
                  by_cases h481 : rank.val < 479
                  ·
                    have hr : rank = ⟨478, by decide⟩ := Fin.ext (by change rank.val = 478; omega)
                    subst rank
                    exact ⟨Checks.routine478, Checks.ready478.1, Checks.ready478.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨479, by decide⟩ := Fin.ext (by change rank.val = 479; omega)
                    subst rank
                    exact ⟨Checks.routine479, Checks.ready479.1, Checks.ready479.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h482 : rank.val < 481
                  ·
                    have hr : rank = ⟨480, by decide⟩ := Fin.ext (by change rank.val = 480; omega)
                    subst rank
                    exact ⟨Checks.routine480, Checks.ready480.1, Checks.ready480.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h483 : rank.val < 482
                    ·
                      have hr : rank = ⟨481, by decide⟩ := Fin.ext (by change rank.val = 481; omega)
                      subst rank
                      exact ⟨Checks.routine481, Checks.ready481.1, Checks.ready481.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨482, by decide⟩ := Fin.ext (by change rank.val = 482; omega)
                      subst rank
                      exact ⟨Checks.routine482, Checks.ready482.1, Checks.ready482.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h484 : rank.val < 487
              ·
                by_cases h485 : rank.val < 485
                ·
                  by_cases h486 : rank.val < 484
                  ·
                    have hr : rank = ⟨483, by decide⟩ := Fin.ext (by change rank.val = 483; omega)
                    subst rank
                    exact ⟨Checks.routine483, Checks.ready483.1, Checks.ready483.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨484, by decide⟩ := Fin.ext (by change rank.val = 484; omega)
                    subst rank
                    exact ⟨Checks.routine484, Checks.ready484.1, Checks.ready484.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h487 : rank.val < 486
                  ·
                    have hr : rank = ⟨485, by decide⟩ := Fin.ext (by change rank.val = 485; omega)
                    subst rank
                    exact ⟨Checks.routine485, Checks.ready485.1, Checks.ready485.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨486, by decide⟩ := Fin.ext (by change rank.val = 486; omega)
                    subst rank
                    exact ⟨Checks.routine486, Checks.ready486.1, Checks.ready486.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h488 : rank.val < 489
                ·
                  by_cases h489 : rank.val < 488
                  ·
                    have hr : rank = ⟨487, by decide⟩ := Fin.ext (by change rank.val = 487; omega)
                    subst rank
                    exact ⟨Checks.routine487, Checks.ready487.1, Checks.ready487.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨488, by decide⟩ := Fin.ext (by change rank.val = 488; omega)
                    subst rank
                    exact ⟨Checks.routine488, Checks.ready488.1, Checks.ready488.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h490 : rank.val < 490
                  ·
                    have hr : rank = ⟨489, by decide⟩ := Fin.ext (by change rank.val = 489; omega)
                    subst rank
                    exact ⟨Checks.routine489, Checks.ready489.1, Checks.ready489.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h491 : rank.val < 491
                    ·
                      have hr : rank = ⟨490, by decide⟩ := Fin.ext (by change rank.val = 490; omega)
                      subst rank
                      exact ⟨Checks.routine490, Checks.ready490.1, Checks.ready490.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨491, by decide⟩ := Fin.ext (by change rank.val = 491; omega)
                      subst rank
                      exact ⟨Checks.routine491, Checks.ready491.1, Checks.ready491.2, bank_contained_of_all _ (by decide +kernel)⟩
      ·
        by_cases h492 : rank.val < 527
        ·
          by_cases h493 : rank.val < 509
          ·
            by_cases h494 : rank.val < 500
            ·
              by_cases h495 : rank.val < 496
              ·
                by_cases h496 : rank.val < 494
                ·
                  by_cases h497 : rank.val < 493
                  ·
                    have hr : rank = ⟨492, by decide⟩ := Fin.ext (by change rank.val = 492; omega)
                    subst rank
                    exact ⟨Checks.routine492, Checks.ready492.1, Checks.ready492.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨493, by decide⟩ := Fin.ext (by change rank.val = 493; omega)
                    subst rank
                    exact ⟨Checks.routine493, Checks.ready493.1, Checks.ready493.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h498 : rank.val < 495
                  ·
                    have hr : rank = ⟨494, by decide⟩ := Fin.ext (by change rank.val = 494; omega)
                    subst rank
                    exact ⟨Checks.routine494, Checks.ready494.1, Checks.ready494.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨495, by decide⟩ := Fin.ext (by change rank.val = 495; omega)
                    subst rank
                    exact ⟨Checks.routine495, Checks.ready495.1, Checks.ready495.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h499 : rank.val < 498
                ·
                  by_cases h500 : rank.val < 497
                  ·
                    have hr : rank = ⟨496, by decide⟩ := Fin.ext (by change rank.val = 496; omega)
                    subst rank
                    exact ⟨Checks.routine496, Checks.ready496.1, Checks.ready496.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨497, by decide⟩ := Fin.ext (by change rank.val = 497; omega)
                    subst rank
                    exact ⟨Checks.routine497, Checks.ready497.1, Checks.ready497.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h501 : rank.val < 499
                  ·
                    have hr : rank = ⟨498, by decide⟩ := Fin.ext (by change rank.val = 498; omega)
                    subst rank
                    exact ⟨Checks.routine498, Checks.ready498.1, Checks.ready498.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨499, by decide⟩ := Fin.ext (by change rank.val = 499; omega)
                    subst rank
                    exact ⟨Checks.routine499, Checks.ready499.1, Checks.ready499.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h502 : rank.val < 504
              ·
                by_cases h503 : rank.val < 502
                ·
                  by_cases h504 : rank.val < 501
                  ·
                    have hr : rank = ⟨500, by decide⟩ := Fin.ext (by change rank.val = 500; omega)
                    subst rank
                    exact ⟨Checks.routine500, Checks.ready500.1, Checks.ready500.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨501, by decide⟩ := Fin.ext (by change rank.val = 501; omega)
                    subst rank
                    exact ⟨Checks.routine501, Checks.ready501.1, Checks.ready501.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h505 : rank.val < 503
                  ·
                    have hr : rank = ⟨502, by decide⟩ := Fin.ext (by change rank.val = 502; omega)
                    subst rank
                    exact ⟨Checks.routine502, Checks.ready502.1, Checks.ready502.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨503, by decide⟩ := Fin.ext (by change rank.val = 503; omega)
                    subst rank
                    exact ⟨Checks.routine503, Checks.ready503.1, Checks.ready503.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h506 : rank.val < 506
                ·
                  by_cases h507 : rank.val < 505
                  ·
                    have hr : rank = ⟨504, by decide⟩ := Fin.ext (by change rank.val = 504; omega)
                    subst rank
                    exact ⟨Checks.routine504, Checks.ready504.1, Checks.ready504.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨505, by decide⟩ := Fin.ext (by change rank.val = 505; omega)
                    subst rank
                    exact ⟨Checks.routine505, Checks.ready505.1, Checks.ready505.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h508 : rank.val < 507
                  ·
                    have hr : rank = ⟨506, by decide⟩ := Fin.ext (by change rank.val = 506; omega)
                    subst rank
                    exact ⟨Checks.routine506, Checks.ready506.1, Checks.ready506.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h509 : rank.val < 508
                    ·
                      have hr : rank = ⟨507, by decide⟩ := Fin.ext (by change rank.val = 507; omega)
                      subst rank
                      exact ⟨Checks.routine507, Checks.ready507.1, Checks.ready507.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨508, by decide⟩ := Fin.ext (by change rank.val = 508; omega)
                      subst rank
                      exact ⟨Checks.routine508, Checks.ready508.1, Checks.ready508.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h510 : rank.val < 518
            ·
              by_cases h511 : rank.val < 513
              ·
                by_cases h512 : rank.val < 511
                ·
                  by_cases h513 : rank.val < 510
                  ·
                    have hr : rank = ⟨509, by decide⟩ := Fin.ext (by change rank.val = 509; omega)
                    subst rank
                    exact ⟨Checks.routine509, Checks.ready509.1, Checks.ready509.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨510, by decide⟩ := Fin.ext (by change rank.val = 510; omega)
                    subst rank
                    exact ⟨Checks.routine510, Checks.ready510.1, Checks.ready510.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h514 : rank.val < 512
                  ·
                    have hr : rank = ⟨511, by decide⟩ := Fin.ext (by change rank.val = 511; omega)
                    subst rank
                    exact ⟨Checks.routine511, Checks.ready511.1, Checks.ready511.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨512, by decide⟩ := Fin.ext (by change rank.val = 512; omega)
                    subst rank
                    exact ⟨Checks.routine512, Checks.ready512.1, Checks.ready512.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h515 : rank.val < 515
                ·
                  by_cases h516 : rank.val < 514
                  ·
                    have hr : rank = ⟨513, by decide⟩ := Fin.ext (by change rank.val = 513; omega)
                    subst rank
                    exact ⟨Checks.routine513, Checks.ready513.1, Checks.ready513.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨514, by decide⟩ := Fin.ext (by change rank.val = 514; omega)
                    subst rank
                    exact ⟨Checks.routine514, Checks.ready514.1, Checks.ready514.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h517 : rank.val < 516
                  ·
                    have hr : rank = ⟨515, by decide⟩ := Fin.ext (by change rank.val = 515; omega)
                    subst rank
                    exact ⟨Checks.routine515, Checks.ready515.1, Checks.ready515.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h518 : rank.val < 517
                    ·
                      have hr : rank = ⟨516, by decide⟩ := Fin.ext (by change rank.val = 516; omega)
                      subst rank
                      exact ⟨Checks.routine516, Checks.ready516.1, Checks.ready516.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨517, by decide⟩ := Fin.ext (by change rank.val = 517; omega)
                      subst rank
                      exact ⟨Checks.routine517, Checks.ready517.1, Checks.ready517.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h519 : rank.val < 522
              ·
                by_cases h520 : rank.val < 520
                ·
                  by_cases h521 : rank.val < 519
                  ·
                    have hr : rank = ⟨518, by decide⟩ := Fin.ext (by change rank.val = 518; omega)
                    subst rank
                    exact ⟨Checks.routine518, Checks.ready518.1, Checks.ready518.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨519, by decide⟩ := Fin.ext (by change rank.val = 519; omega)
                    subst rank
                    exact ⟨Checks.routine519, Checks.ready519.1, Checks.ready519.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h522 : rank.val < 521
                  ·
                    have hr : rank = ⟨520, by decide⟩ := Fin.ext (by change rank.val = 520; omega)
                    subst rank
                    exact ⟨Checks.routine520, Checks.ready520.1, Checks.ready520.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨521, by decide⟩ := Fin.ext (by change rank.val = 521; omega)
                    subst rank
                    exact ⟨Checks.routine521, Checks.ready521.1, Checks.ready521.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h523 : rank.val < 524
                ·
                  by_cases h524 : rank.val < 523
                  ·
                    have hr : rank = ⟨522, by decide⟩ := Fin.ext (by change rank.val = 522; omega)
                    subst rank
                    exact ⟨Checks.routine522, Checks.ready522.1, Checks.ready522.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨523, by decide⟩ := Fin.ext (by change rank.val = 523; omega)
                    subst rank
                    exact ⟨Checks.routine523, Checks.ready523.1, Checks.ready523.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h525 : rank.val < 525
                  ·
                    have hr : rank = ⟨524, by decide⟩ := Fin.ext (by change rank.val = 524; omega)
                    subst rank
                    exact ⟨Checks.routine524, Checks.ready524.1, Checks.ready524.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h526 : rank.val < 526
                    ·
                      have hr : rank = ⟨525, by decide⟩ := Fin.ext (by change rank.val = 525; omega)
                      subst rank
                      exact ⟨Checks.routine525, Checks.ready525.1, Checks.ready525.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨526, by decide⟩ := Fin.ext (by change rank.val = 526; omega)
                      subst rank
                      exact ⟨Checks.routine526, Checks.ready526.1, Checks.ready526.2, bank_contained_of_all _ (by decide +kernel)⟩
        ·
          by_cases h527 : rank.val < 545
          ·
            by_cases h528 : rank.val < 536
            ·
              by_cases h529 : rank.val < 531
              ·
                by_cases h530 : rank.val < 529
                ·
                  by_cases h531 : rank.val < 528
                  ·
                    have hr : rank = ⟨527, by decide⟩ := Fin.ext (by change rank.val = 527; omega)
                    subst rank
                    exact ⟨Checks.routine527, Checks.ready527.1, Checks.ready527.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨528, by decide⟩ := Fin.ext (by change rank.val = 528; omega)
                    subst rank
                    exact ⟨Checks.routine528, Checks.ready528.1, Checks.ready528.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h532 : rank.val < 530
                  ·
                    have hr : rank = ⟨529, by decide⟩ := Fin.ext (by change rank.val = 529; omega)
                    subst rank
                    exact ⟨Checks.routine529, Checks.ready529.1, Checks.ready529.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨530, by decide⟩ := Fin.ext (by change rank.val = 530; omega)
                    subst rank
                    exact ⟨Checks.routine530, Checks.ready530.1, Checks.ready530.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h533 : rank.val < 533
                ·
                  by_cases h534 : rank.val < 532
                  ·
                    have hr : rank = ⟨531, by decide⟩ := Fin.ext (by change rank.val = 531; omega)
                    subst rank
                    exact ⟨Checks.routine531, Checks.ready531.1, Checks.ready531.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨532, by decide⟩ := Fin.ext (by change rank.val = 532; omega)
                    subst rank
                    exact ⟨Checks.routine532, Checks.ready532.1, Checks.ready532.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h535 : rank.val < 534
                  ·
                    have hr : rank = ⟨533, by decide⟩ := Fin.ext (by change rank.val = 533; omega)
                    subst rank
                    exact ⟨Checks.routine533, Checks.ready533.1, Checks.ready533.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h536 : rank.val < 535
                    ·
                      have hr : rank = ⟨534, by decide⟩ := Fin.ext (by change rank.val = 534; omega)
                      subst rank
                      exact ⟨Checks.routine534, Checks.ready534.1, Checks.ready534.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨535, by decide⟩ := Fin.ext (by change rank.val = 535; omega)
                      subst rank
                      exact ⟨Checks.routine535, Checks.ready535.1, Checks.ready535.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h537 : rank.val < 540
              ·
                by_cases h538 : rank.val < 538
                ·
                  by_cases h539 : rank.val < 537
                  ·
                    have hr : rank = ⟨536, by decide⟩ := Fin.ext (by change rank.val = 536; omega)
                    subst rank
                    exact ⟨Checks.routine536, Checks.ready536.1, Checks.ready536.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨537, by decide⟩ := Fin.ext (by change rank.val = 537; omega)
                    subst rank
                    exact ⟨Checks.routine537, Checks.ready537.1, Checks.ready537.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h540 : rank.val < 539
                  ·
                    have hr : rank = ⟨538, by decide⟩ := Fin.ext (by change rank.val = 538; omega)
                    subst rank
                    exact ⟨Checks.routine538, Checks.ready538.1, Checks.ready538.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨539, by decide⟩ := Fin.ext (by change rank.val = 539; omega)
                    subst rank
                    exact ⟨Checks.routine539, Checks.ready539.1, Checks.ready539.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h541 : rank.val < 542
                ·
                  by_cases h542 : rank.val < 541
                  ·
                    have hr : rank = ⟨540, by decide⟩ := Fin.ext (by change rank.val = 540; omega)
                    subst rank
                    exact ⟨Checks.routine540, Checks.ready540.1, Checks.ready540.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨541, by decide⟩ := Fin.ext (by change rank.val = 541; omega)
                    subst rank
                    exact ⟨Checks.routine541, Checks.ready541.1, Checks.ready541.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h543 : rank.val < 543
                  ·
                    have hr : rank = ⟨542, by decide⟩ := Fin.ext (by change rank.val = 542; omega)
                    subst rank
                    exact ⟨Checks.routine542, Checks.ready542.1, Checks.ready542.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h544 : rank.val < 544
                    ·
                      have hr : rank = ⟨543, by decide⟩ := Fin.ext (by change rank.val = 543; omega)
                      subst rank
                      exact ⟨Checks.routine543, Checks.ready543.1, Checks.ready543.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨544, by decide⟩ := Fin.ext (by change rank.val = 544; omega)
                      subst rank
                      exact ⟨Checks.routine544, Checks.ready544.1, Checks.ready544.2, bank_contained_of_all _ (by decide +kernel)⟩
          ·
            by_cases h545 : rank.val < 554
            ·
              by_cases h546 : rank.val < 549
              ·
                by_cases h547 : rank.val < 547
                ·
                  by_cases h548 : rank.val < 546
                  ·
                    have hr : rank = ⟨545, by decide⟩ := Fin.ext (by change rank.val = 545; omega)
                    subst rank
                    exact ⟨Checks.routine545, Checks.ready545.1, Checks.ready545.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨546, by decide⟩ := Fin.ext (by change rank.val = 546; omega)
                    subst rank
                    exact ⟨Checks.routine546, Checks.ready546.1, Checks.ready546.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h549 : rank.val < 548
                  ·
                    have hr : rank = ⟨547, by decide⟩ := Fin.ext (by change rank.val = 547; omega)
                    subst rank
                    exact ⟨Checks.routine547, Checks.ready547.1, Checks.ready547.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨548, by decide⟩ := Fin.ext (by change rank.val = 548; omega)
                    subst rank
                    exact ⟨Checks.routine548, Checks.ready548.1, Checks.ready548.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h550 : rank.val < 551
                ·
                  by_cases h551 : rank.val < 550
                  ·
                    have hr : rank = ⟨549, by decide⟩ := Fin.ext (by change rank.val = 549; omega)
                    subst rank
                    exact ⟨Checks.routine549, Checks.ready549.1, Checks.ready549.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨550, by decide⟩ := Fin.ext (by change rank.val = 550; omega)
                    subst rank
                    exact ⟨Checks.routine550, Checks.ready550.1, Checks.ready550.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h552 : rank.val < 552
                  ·
                    have hr : rank = ⟨551, by decide⟩ := Fin.ext (by change rank.val = 551; omega)
                    subst rank
                    exact ⟨Checks.routine551, Checks.ready551.1, Checks.ready551.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h553 : rank.val < 553
                    ·
                      have hr : rank = ⟨552, by decide⟩ := Fin.ext (by change rank.val = 552; omega)
                      subst rank
                      exact ⟨Checks.routine552, Checks.ready552.1, Checks.ready552.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨553, by decide⟩ := Fin.ext (by change rank.val = 553; omega)
                      subst rank
                      exact ⟨Checks.routine553, Checks.ready553.1, Checks.ready553.2, bank_contained_of_all _ (by decide +kernel)⟩
            ·
              by_cases h554 : rank.val < 558
              ·
                by_cases h555 : rank.val < 556
                ·
                  by_cases h556 : rank.val < 555
                  ·
                    have hr : rank = ⟨554, by decide⟩ := Fin.ext (by change rank.val = 554; omega)
                    subst rank
                    exact ⟨Checks.routine554, Checks.ready554.1, Checks.ready554.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨555, by decide⟩ := Fin.ext (by change rank.val = 555; omega)
                    subst rank
                    exact ⟨Checks.routine555, Checks.ready555.1, Checks.ready555.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h557 : rank.val < 557
                  ·
                    have hr : rank = ⟨556, by decide⟩ := Fin.ext (by change rank.val = 556; omega)
                    subst rank
                    exact ⟨Checks.routine556, Checks.ready556.1, Checks.ready556.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨557, by decide⟩ := Fin.ext (by change rank.val = 557; omega)
                    subst rank
                    exact ⟨Checks.routine557, Checks.ready557.1, Checks.ready557.2, bank_contained_of_all _ (by decide +kernel)⟩
              ·
                by_cases h558 : rank.val < 560
                ·
                  by_cases h559 : rank.val < 559
                  ·
                    have hr : rank = ⟨558, by decide⟩ := Fin.ext (by change rank.val = 558; omega)
                    subst rank
                    exact ⟨Checks.routine558, Checks.ready558.1, Checks.ready558.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    have hr : rank = ⟨559, by decide⟩ := Fin.ext (by change rank.val = 559; omega)
                    subst rank
                    exact ⟨Checks.routine559, Checks.ready559.1, Checks.ready559.2, bank_contained_of_all _ (by decide +kernel)⟩
                ·
                  by_cases h560 : rank.val < 561
                  ·
                    have hr : rank = ⟨560, by decide⟩ := Fin.ext (by change rank.val = 560; omega)
                    subst rank
                    exact ⟨Checks.routine560, Checks.ready560.1, Checks.ready560.2, bank_contained_of_all _ (by decide +kernel)⟩
                  ·
                    by_cases h561 : rank.val < 562
                    ·
                      have hr : rank = ⟨561, by decide⟩ := Fin.ext (by change rank.val = 561; omega)
                      subst rank
                      exact ⟨Checks.routine561, Checks.ready561.1, Checks.ready561.2, bank_contained_of_all _ (by decide +kernel)⟩
                    ·
                      have hr : rank = ⟨562, by decide⟩ := Fin.ext (by change rank.val = 562; omega)
                      subst rank
                      exact ⟨Checks.routine562, Checks.ready562.1, Checks.ready562.2, bank_contained_of_all _ (by decide +kernel)⟩

theorem allGood_layout (L : Layout) (himage : L.image = Frozen.image)
    (hchain : ∀ r, L.chainWord r = Frozen.layout.chainWord r) : AllGood L (P := P) := by
  intro rank
  obtain ⟨r,hr,hcost,_⟩ := allCertified_inSharedBank rank
  exact good_of_ready_layout L himage hchain V3SourceEquiv.sourceEquivalent
    V3Endpoints.endpointsCorrect rank r hr hcost

theorem allGood : AllGood Frozen.layout := allGood_layout Frozen.layout rfl (fun _ => rfl)

end W9Machine.N600
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem allGood : N600.AllGood Frozen.layout := N600.allGood
end W9Machine.Chain

namespace W9Machine.N600
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
/-- All 563 existing chain certificates stay inside the copied producer bank. -/
theorem allReady_inSharedBank : ∀ rank : Fin 563, ∃ r : ChainRoutine,
    Chain.RoutineReady (embed rank) r ∧
    ∀ p ∈ r.pieces, 195584 ≤ p.pc ∧ p.pc + p.words.length ≤ 254656 := by
  intro rank
  obtain ⟨r,hr,_,hbank⟩ := allCertified_inSharedBank rank
  exact ⟨r,hr,hbank⟩

end W9Machine.N600

namespace W9Machine.N600
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxHeartbeats 1000000
/-- The complete bank semantics applies to any image sharing the certified
instruction window, including the expansion producer. -/
theorem tbsim_sharedBank (L : Layout) (sk : BitVec 256)
    (hwindow : (Frozen.image.code.drop 195584).take 59072 = (L.image.code.drop 195584).take 59072)
    (hchain : ∀ rank, L.chainWord rank = Frozen.layout.chainWord rank)
    (rank : Fin 563) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (hu : Pre L w index k j rank u) :
    TBSim L.image sk u 89 (program w index k j rank) (Post L w index k j u) := by
  obtain ⟨r,hr,hbounds⟩ := allReady_inSharedBank rank
  apply tbsim_of_ready_layout L sk hchain V3SourceEquiv.sourceEquivalent V3Endpoints.endpointsCorrect
    rank r hr ?_ w index k j u hu
  intro p hp
  exact codeAt_of_window_eq (source := Frozen.image) (target := L.image)
    (start := 195584) (count := 59072) (hbounds p hp).1 (hbounds p hp).2
    (by decide) hwindow (slice_at p.pc p.words (hr.linked p hp).1)
end W9Machine.N600
end
