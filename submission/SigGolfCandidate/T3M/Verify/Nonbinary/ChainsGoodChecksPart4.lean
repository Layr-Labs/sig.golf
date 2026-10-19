import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheckParts

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem guard6All_0 : guard6All 0 = true := by decide +kernel
theorem guard6All_1 : guard6All 1 = true := by decide +kernel
theorem guard6All_2 : guard6All 2 = true := by decide +kernel
theorem guard6All_3 : guard6All 3 = true := by decide +kernel
theorem guard6All_4 : guard6All 4 = true := by decide +kernel
theorem guard6All_5 : guard6All 5 = true := by decide +kernel
theorem guard6All_6 : guard6All 6 = true := by decide +kernel
theorem guard6All_7 : guard6All 7 = true := by decide +kernel
theorem ckGuardAll_ok : ckGuardAll = true := by decide +kernel
theorem ckArmAll_ok : ckArmAll = true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end
end
