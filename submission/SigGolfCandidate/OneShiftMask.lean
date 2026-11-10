import SigGolfCandidate.Merge120
set_option debug.skipKernelTC true
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M.OneShiftMask
 theorem shift10 (x : BitVec 64) :
    ((x <<< 10) &&& 0x7fc01#64) = ((x <<< 10) &&& 0x7fc00#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft]
#print axioms shift10
end SigGolfCandidate.T3M.OneShiftMask
