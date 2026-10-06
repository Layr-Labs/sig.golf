import SigGolfCandidate.T3M.Submission
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineNativeBinding

namespace SigGolfCandidate.T3M.Native
open SigGolfCandidate.Legacy

def submission : Submission where
  sizes := T3M.submission.sizes
  layout := T3M.submission.layout
  image
    | .verify => Images.InlineNative.image
    | p => T3M.submission.image p

@[simp] theorem submission_sizes : submission.sizes = T3M.submission.sizes := rfl
@[simp] theorem submission_layout : submission.layout = T3M.submission.layout := rfl
@[simp] theorem submission_keygen : submission.image .keygen = T3M.submission.image .keygen := rfl
@[simp] theorem submission_sign : submission.image .sign = T3M.submission.image .sign := rfl
@[simp] theorem submission_expand : submission.image .expand = T3M.submission.image .expand := rfl
@[simp] theorem submission_verify : submission.image .verify = Images.InlineNative.image := rfl

 theorem image_valid : Images.InlineNative.image.Valid submission.sizes submission.layout := by
  rw [Riscv.Image.Valid, Riscv.Image.byteSize,
    Nonbinary.InlineNativeBinding.code_length_eq_original,
    Nonbinary.InlineNativeBinding.data_eq_original]
  have old := T3M.submission_verify_valid
  rw [T3M.submission_verify, Riscv.Image.Valid, Riscv.Image.byteSize] at old
  refine ⟨old.1, ?_⟩
  have hd : Images.InlineNative.image.data.length = 16832 := by
    rw [Nonbinary.InlineNativeBinding.data_eq_original]
    exact Images.verifyData_length
  have ho : Images.verifyImage.data.length = 16832 := Images.verifyData_length
  rw [layoutValid_of_data_length _ _ _ 16832 hd]
  rw [layoutValid_of_data_length _ _ _ 16832 ho] at old
  exact old.2

 theorem submission_admissible : submission.Admissible := by
  refine ⟨T3M.submission_admissible.1, ?_⟩
  intro phase
  cases phase
  · exact T3M.submission_keygen_valid
  · exact T3M.submission_sign_valid
  · exact T3M.submission_expand_valid
  · exact image_valid

end SigGolfCandidate.T3M.Native
