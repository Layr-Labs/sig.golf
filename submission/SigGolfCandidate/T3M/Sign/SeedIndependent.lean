import SigGolfCandidate.T3M.Sign.Basic

namespace SigGolfCandidate.T3M.Sign.SeedIndependent
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open Keygen
def SeedIndependentAt (image : Image) (b : Nat) : Prop :=
  (∀ off code, (off, code) ∈ subL → off ≠ 42 → CodeAt image (pcOf (b + off)) code) ∧
  (b = 117 ∨ b = 1013) ∧
  (CodeAt image (pcOf (b + 1000)) maxDigitCode ∧
   CodeAt image (pcOf (b + 1004)) revCode ∧
   ((image = Images.keygenImage ∧ b = 117) ∨ (image = Images.signImage ∧ b = 1013)))
theorem of_subAt {image : Image} {b : Nat} (h : SubAt image b) :
    SeedIndependentAt image b := by
  refine ⟨?_, h.2⟩
  intro off code hm _
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact codeAt_sublayout h.1 subL_ok hi
private def patchedL : Rv.Layout :=
  subL.map fun p => if p.1 = 42 then (p.1, [0x3ac1306f, 67310179]) else p
private theorem patchedL_ok : layoutOk 0 patchedL = true := by decide +kernel
private theorem patchedAt : CodeAt Images.signImage (pcOf 1013) (layoutCode patchedL) :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem seedIndependentAt_sign : SeedIndependentAt Images.signImage 1013 := by
  refine ⟨?_, Or.inr rfl, Sign.codeAt_maxDigit, Sign.codeAt_2017, Or.inr ⟨rfl, rfl⟩⟩
  intro off code hm hn
  have hp : (off, code) ∈ patchedL := by
    apply List.mem_map.mpr
    exact ⟨(off, code), hm, by simp [hn]⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  exact codeAt_sublayout patchedAt patchedL_ok hi
theorem seedIndependentAt_keygen : SeedIndependentAt Images.keygenImage 117 :=
  of_subAt subAt_keygen
theorem codeAt_sub_0 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 0)) sub_0 :=
  h.1 0 sub_0 (by decide +kernel) (by decide)
theorem codeAt_sub_1 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1)) sub_1 :=
  h.1 1 sub_1 (by decide +kernel) (by decide)
theorem codeAt_sub_2 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 2)) sub_2 :=
  h.1 2 sub_2 (by decide +kernel) (by decide)
theorem codeAt_sub_8 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 8)) sub_8 :=
  h.1 8 sub_8 (by decide +kernel) (by decide)
theorem codeAt_sub_9 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 9)) sub_9 :=
  h.1 9 sub_9 (by decide +kernel) (by decide)
theorem codeAt_sub_23 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 23)) sub_23 :=
  h.1 23 sub_23 (by decide +kernel) (by decide)
theorem codeAt_sub_24 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 24)) sub_24 :=
  h.1 24 sub_24 (by decide +kernel) (by decide)
theorem codeAt_sub_26 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 26)) sub_26 :=
  h.1 26 sub_26 (by decide +kernel) (by decide)
theorem codeAt_sub_27 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 27)) sub_27 :=
  h.1 27 sub_27 (by decide +kernel) (by decide)
theorem codeAt_sub_41 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 41)) sub_41 :=
  h.1 41 sub_41 (by decide +kernel) (by decide)
theorem codeAt_sub_44 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 44)) sub_44 :=
  h.1 44 sub_44 (by decide +kernel) (by decide)
theorem codeAt_sub_59 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 59)) sub_59 :=
  h.1 59 sub_59 (by decide +kernel) (by decide)
theorem codeAt_sub_60 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 60)) sub_60 :=
  h.1 60 sub_60 (by decide +kernel) (by decide)
theorem codeAt_sub_72 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 72)) sub_72 :=
  h.1 72 sub_72 (by decide +kernel) (by decide)
theorem codeAt_sub_73 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 73)) sub_73 :=
  h.1 73 sub_73 (by decide +kernel) (by decide)
theorem codeAt_sub_75 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 75)) sub_75 :=
  h.1 75 sub_75 (by decide +kernel) (by decide)
theorem codeAt_sub_76 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 76)) sub_76 :=
  h.1 76 sub_76 (by decide +kernel) (by decide)
theorem codeAt_sub_77 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 77)) sub_77 :=
  h.1 77 sub_77 (by decide +kernel) (by decide)
theorem codeAt_sub_78 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 78)) sub_78 :=
  h.1 78 sub_78 (by decide +kernel) (by decide)
theorem codeAt_sub_79 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 79)) sub_79 :=
  h.1 79 sub_79 (by decide +kernel) (by decide)
theorem codeAt_sub_80 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 80)) sub_80 :=
  h.1 80 sub_80 (by decide +kernel) (by decide)
theorem codeAt_sub_82 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 82)) sub_82 :=
  h.1 82 sub_82 (by decide +kernel) (by decide)
theorem codeAt_sub_83 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 83)) sub_83 :=
  h.1 83 sub_83 (by decide +kernel) (by decide)
theorem codeAt_sub_92 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 92)) sub_92 :=
  h.1 92 sub_92 (by decide +kernel) (by decide)
theorem codeAt_sub_95 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 95)) sub_95 :=
  h.1 95 sub_95 (by decide +kernel) (by decide)
theorem codeAt_sub_96 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 96)) sub_96 :=
  h.1 96 sub_96 (by decide +kernel) (by decide)
theorem codeAt_sub_105 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 105)) sub_105 :=
  h.1 105 sub_105 (by decide +kernel) (by decide)
theorem codeAt_sub_106 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 106)) sub_106 :=
  h.1 106 sub_106 (by decide +kernel) (by decide)
theorem codeAt_sub_112 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 112)) sub_112 :=
  h.1 112 sub_112 (by decide +kernel) (by decide)
theorem codeAt_sub_113 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 113)) sub_113 :=
  h.1 113 sub_113 (by decide +kernel) (by decide)
theorem codeAt_sub_116 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 116)) sub_116 :=
  h.1 116 sub_116 (by decide +kernel) (by decide)
theorem codeAt_sub_117 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 117)) sub_117 :=
  h.1 117 sub_117 (by decide +kernel) (by decide)
theorem codeAt_sub_118 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 118)) sub_118 :=
  h.1 118 sub_118 (by decide +kernel) (by decide)
theorem codeAt_sub_120 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 120)) sub_120 :=
  h.1 120 sub_120 (by decide +kernel) (by decide)
theorem codeAt_sub_140 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 140)) sub_140 :=
  h.1 140 sub_140 (by decide +kernel) (by decide)
theorem codeAt_sub_146 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 146)) sub_146 :=
  h.1 146 sub_146 (by decide +kernel) (by decide)
theorem codeAt_sub_147 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 147)) sub_147 :=
  h.1 147 sub_147 (by decide +kernel) (by decide)
theorem codeAt_sub_157 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 157)) sub_157 :=
  h.1 157 sub_157 (by decide +kernel) (by decide)
theorem codeAt_sub_159 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 159)) sub_159 :=
  h.1 159 sub_159 (by decide +kernel) (by decide)
theorem codeAt_rev {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1004)) revCode := h.2.2.2.1
theorem codeAt_maxLow {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1000)) maxLow := by
  have q := codeAt_sublayout (L := maxLayout) (b := b + 1000) h.2.2.1 maxLayout_ok
    (i := 0) (o := 0) (seg := maxLow) (by kernel_rfl)
  simpa only [Nat.add_zero] using q
theorem codeAt_maxHigh {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1002)) maxHigh := by
  have q := codeAt_sublayout (L := maxLayout) (b := b + 1000) h.2.2.1 maxLayout_ok
    (i := 1) (o := 2) (seg := maxHigh) (by kernel_rfl)
  simpa [Nat.add_assoc] using q
theorem codeAt_sub_43 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 43)) (sub_42.drop 1) := by
  rcases h.2.2.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact codeAt_slice (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_sub_61 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 61)) (sub_60.drop 1) := by
  rcases h.2.2.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact codeAt_slice (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
end SigGolfCandidate.T3M.Sign.SeedIndependent
