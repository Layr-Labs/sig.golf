import SigGolfCandidate.W9Machine.WctImage
import SigGolfCandidate.T3M.Verify.ChainRuns

namespace W9Machine.Frozen
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem codeChunks_length : codeChunks.length = 992 :=
  SigGolfCandidate.T3M.Verify.vChunks_length
theorem codeChunks_ok : (codeChunks.dropLast.all fun c ↦ c.length == 256) = true :=
  SigGolfCandidate.T3M.Verify.vChunks_ok
theorem codeChunks_le : (codeChunks.all fun c ↦ decide (c.length ≤ 256)) = true :=
  SigGolfCandidate.T3M.Verify.vChunks_le
theorem image_code_eq : image.code = SigGolfCandidate.T3M.Images.verifyCode := by
  change SigGolfCandidate.T3M.Verify.vChunks.flatten = _
  exact SigGolfCandidate.T3M.Verify.verifyCode_eq.symm
def codeFrom (p : Nat) : List (BitVec 32) := SigGolfCandidate.T3M.Verify.codeFrom p
theorem codeFrom_eq (p : Nat) (hp : p < 253807) : codeFrom p = image.code.drop p := by
  rw [image_code_eq]
  exact SigGolfCandidate.T3M.Verify.codeFrom_eq p (by omega)
theorem codeFrom_at (p : Nat) (hp : p < 253807) : CodeAt image (pcOf p) (codeFrom p) := by
  have hl : image.code.length ≤ 256 * 992 := by
    rw [image_code_eq]
    exact SigGolfCandidate.T3M.Verify.verifyCode_length
  have hp' : (pcOf p).toNat = 0x1000 + 4 * p := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  rw [codeFrom_eq p hp]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hp', List.length_drop]
    omega
  · rw [hp', show (0x1000 + 4 * p - 0x1000) / 4 = p by omega]
end W9Machine.Frozen
