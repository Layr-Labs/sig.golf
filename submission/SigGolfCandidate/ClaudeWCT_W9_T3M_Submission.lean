import SigGolfCandidate.T3M_Images_Keygen

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy
structure Images where
  sign : Riscv.Image
  expand : Riscv.Image
  verify : Riscv.Image
def submission (I : Images) : Submission where
  sizes := ⟨5310, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image
    | .keygen => SigGolfCandidate.T3M.Images.keygenImage
    | .sign => I.sign
    | .expand => I.expand
    | .verify => I.verify
variable (I : Images)
@[simp] theorem submission_sizes : (submission I).sizes = ⟨5310, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : (submission I).layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
theorem message_after_witness : (submission I).layout.message = (submission I).layout.witness + 22016 := by
  rw [submission_layout]
@[simp] theorem submission_keygen : (submission I).image .keygen = SigGolfCandidate.T3M.Images.keygenImage := rfl
@[simp] theorem submission_sign : (submission I).image .sign = I.sign := rfl
@[simp] theorem submission_expand : (submission I).image .expand = I.expand := rfl
@[simp] theorem submission_verify : (submission I).image .verify = I.verify := rfl
end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.Legacy

def submission (I : Images) : Submission where
  sizes := ⟨5239, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image := (ClaudeWCT.W9.T3M.submission I).image

variable (I : Images)
@[simp] theorem submission_sizes : (submission I).sizes = ⟨5239, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : (submission I).layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
@[simp] theorem submission_image : (submission I).image = (ClaudeWCT.W9.T3M.submission I).image := rfl
@[simp] theorem submission_keygen : (submission I).image .keygen = SigGolfCandidate.T3M.Images.keygenImage := rfl
@[simp] theorem submission_sign : (submission I).image .sign = I.sign := rfl
@[simp] theorem submission_expand : (submission I).image .expand = I.expand := rfl
@[simp] theorem submission_verify : (submission I).image .verify = I.verify := rfl

end ClaudeWCT.W9.T3M.Paired
