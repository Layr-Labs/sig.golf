import SigGolfCandidate.W9Machine.WctImage
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineNativeBinding

namespace W9Machine.Frozen
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem codeChunks_length : codeChunks.length = 985 :=
  SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.native_chunk_count
theorem codeChunks_ok : (codeChunks.dropLast.all fun c ↦ c.length == 256) = true :=
  SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.native_chunks_ok
theorem codeChunks_le : (codeChunks.all fun c ↦ decide (c.length ≤ 256)) = true :=
  SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.native_chunks_le
def codeFrom (p : Nat) : List (BitVec 32) :=
  (codeChunks.drop (p / 256)).flatten.drop (p % 256)
theorem codeFrom_eq (p : Nat) (hp : p < 251927) : codeFrom p = image.code.drop p := by
  simpa only [codeFrom, image, List.drop_drop,
    show 256 * (p / 256) + p % 256 = p by omega] using
      (congrArg (List.drop (p % 256))
        (drop_chunks' codeChunks (p / 256) codeChunks_ok
          (by rw [codeChunks_length]; omega))).symm
theorem codeFrom_at (p : Nat) (hp : p < 251927) : CodeAt image (pcOf p) (codeFrom p) := by
  have hl : image.code.length ≤ 256 * 985 := by
    simpa only [image, codeChunks_length] using flatten_len_le' codeChunks codeChunks_le
  have hp' : (pcOf p).toNat = 0x1000 + 4 * p := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  rw [codeFrom_eq p hp]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hp', List.length_drop]
    omega
  · rw [hp', show (0x1000 + 4 * p - 0x1000) / 4 = p by omega]
end W9Machine.Frozen
