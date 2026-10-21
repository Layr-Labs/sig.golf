import SigGolfCandidate.T3M_Images_Sizes

section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy
theorem layoutValid_of_data_length (image : Riscv.Image) (layout : Layout)
    (sizes : Sizes) (d : Nat) (hd : image.data.length = d) :
    Riscv.layoutValid layout sizes image ↔
      (Riscv.layoutBuffers layout sizes).all (fun buffer =>
        decide (buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤
          16 * ((MEMORY_BYTES - d) / 16))) = true ∧
      Riscv.buffersDisjoint (Riscv.layoutBuffers layout sizes) = true := by
  unfold Riscv.layoutValid Riscv.dataBase
  rw [hd]
end SigGolfCandidate.T3M
end
section
set_option maxRecDepth 10000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy
def submission : Submission where
  sizes := ⟨5310, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image
    | .keygen => Images.keygenImage
    | .sign => Images.signImage
    | .expand => Images.expandImage
    | .verify => Images.verifyImage
@[simp] theorem submission_sizes : submission.sizes = ⟨5310, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : submission.layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
@[simp] theorem submission_keygen : submission.image .keygen = Images.keygenImage := rfl
@[simp] theorem submission_sign : submission.image .sign = Images.signImage := rfl
@[simp] theorem submission_expand : submission.image .expand = Images.expandImage := rfl
@[simp] theorem submission_verify : submission.image .verify = Images.verifyImage := rfl
theorem submission_keygen_valid :
    (submission.image .keygen).Valid submission.sizes submission.layout := by
  rw [submission_keygen, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.keygenImage.code.length = 1177 from Images.keygenCode_length,
    show Images.keygenImage.data.length = 0 from Images.keygenData_length]
  rw [layoutValid_of_data_length _ _ _ 0 Images.keygenData_length]
  decide +kernel
theorem submission_sign_valid :
    (submission.image .sign).Valid submission.sizes submission.layout := by
  rw [submission_sign, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.signImage.code.length = 25046 from Images.signCode_length,
    show Images.signImage.data.length = 86144 from Images.signData_length]
  rw [layoutValid_of_data_length _ _ _ 86144 Images.signData_length]
  decide +kernel
theorem submission_expand_valid :
    (submission.image .expand).Valid submission.sizes submission.layout := by
  rw [submission_expand, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.expandImage.code.length = 254656 from Images.expandCode_length,
    show Images.expandImage.data.length = 29936 from Images.expandData_length]
  rw [layoutValid_of_data_length _ _ _ 29936 Images.expandData_length]
  decide +kernel
set_option maxRecDepth 200000 in
theorem submission_verify_valid :
    (submission.image .verify).Valid submission.sizes submission.layout := by
  rw [submission_verify, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.verifyImage.code.length = 257258 from Images.verifyCode_length,
    show Images.verifyImage.data.length = 16928 from Images.verifyData_length]
  rw [layoutValid_of_data_length _ _ _ 16928 Images.verifyData_length]
  decide +kernel
theorem submission_admissible : submission.Admissible := by
  refine ⟨by unfold Sizes.Valid; decide, ?_⟩
  intro phase
  cases phase
  · exact submission_keygen_valid
  · exact submission_sign_valid
  · exact submission_expand_valid
  · exact submission_verify_valid
end SigGolfCandidate.T3M
end

/-! Concrete image wrapper for the paired forest candidate. The exported
challenge submission remains separate until every certificate premise is closed. -/
namespace SigGolfCandidate.T3M.Paired
open SigGolfCandidate.Legacy

def submission : Submission where
  sizes := ⟨5195, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image := SigGolfCandidate.T3M.submission.image

@[simp] theorem submission_sizes : submission.sizes = ⟨5195, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : submission.layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
@[simp] theorem submission_image : submission.image = SigGolfCandidate.T3M.submission.image := rfl
@[simp] theorem submission_keygen : submission.image .keygen = Images.keygenImage := rfl
@[simp] theorem submission_sign : submission.image .sign = Images.signImage := rfl
@[simp] theorem submission_expand : submission.image .expand = Images.expandImage := rfl
@[simp] theorem submission_verify : submission.image .verify = Images.verifyImage := rfl

end SigGolfCandidate.T3M.Paired

namespace SigGolfCandidate.T3M.Paired
open SigGolfCandidate.Legacy
set_option maxRecDepth 200000
theorem submission_keygen_valid :
    (submission.image .keygen).Valid submission.sizes submission.layout := by
  rw [submission_keygen, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.keygenImage.code.length = 1177 from Images.keygenCode_length,
    show Images.keygenImage.data.length = 0 from Images.keygenData_length]
  rw [layoutValid_of_data_length _ _ _ 0 Images.keygenData_length]
  decide +kernel
theorem submission_sign_valid :
    (submission.image .sign).Valid submission.sizes submission.layout := by
  rw [submission_sign, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.signImage.code.length = 25046 from Images.signCode_length,
    show Images.signImage.data.length = 86144 from Images.signData_length]
  rw [layoutValid_of_data_length _ _ _ 86144 Images.signData_length]
  decide +kernel
theorem submission_expand_valid :
    (submission.image .expand).Valid submission.sizes submission.layout := by
  rw [submission_expand, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.expandImage.code.length = 254656 from Images.expandCode_length,
    show Images.expandImage.data.length = 29936 from Images.expandData_length]
  rw [layoutValid_of_data_length _ _ _ 29936 Images.expandData_length]
  decide +kernel
set_option maxRecDepth 200000 in
theorem submission_verify_valid :
    (submission.image .verify).Valid submission.sizes submission.layout := by
  rw [submission_verify, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.verifyImage.code.length = 257258 from Images.verifyCode_length,
    show Images.verifyImage.data.length = 16928 from Images.verifyData_length]
  rw [layoutValid_of_data_length _ _ _ 16928 Images.verifyData_length]
  decide +kernel
theorem submission_admissible : submission.Admissible := by
  refine ⟨by unfold Sizes.Valid; decide, ?_⟩
  intro phase
  cases phase
  · exact submission_keygen_valid
  · exact submission_sign_valid
  · exact submission_expand_valid
  · exact submission_verify_valid
end SigGolfCandidate.T3M.Paired
