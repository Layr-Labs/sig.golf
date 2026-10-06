import SigGolfCandidate.T3M.Images.DataParts
import SigGolfCandidate.T3M.Images.Lengths
import SigGolfCandidate.T3M.Images.Keygen
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineChunkLengths
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineNativeBinding

namespace SigGolfCandidate.T3M.Images
theorem keygenCode_length : keygenCode.length = 1149 := by
  set_option maxRecDepth 100000 in decide +kernel
theorem keygenData_length : keygenData.length = 0 := by
  set_option maxRecDepth 100000 in decide +kernel
theorem signCode_length : signCode.length = 20771 := by
  rw [signCode, foldl_append_length]
  set_option maxRecDepth 100000 in decide +kernel
theorem signData_length : signData.length = 86016 := by
  rw [signData, List.length_append, signPrefixData_length, signLegacyData_length]
theorem expandCode_length : expandCode.length = 41066 := by
  rw [expandCode, foldl_append_length]
  set_option maxRecDepth 100000 in decide +kernel
theorem expandData_length : expandData.length = 25088 := by
  rw [expandData, List.length_append, expandPrefixData_length, expandLegacyData_length]
set_option maxRecDepth 100000 in
theorem verifyCode_length : verifyCode.length = 251927 := by
  exact SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.code_length_eq_original.symm.trans
    SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.native_code_length
theorem verifyData_length : verifyData.length = 16832 := by
  rw [verifyData, List.length_append, verifyRawRankData, verifyPackedData, List.length_flatten]
  set_option maxRecDepth 100000 in decide +kernel
end SigGolfCandidate.T3M.Images
