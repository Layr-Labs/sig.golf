import SigGolfCandidate.OuterImageCopies
import SigGolfCandidate.OuterInstalledDispatch
import SigGolfCandidate.OuterImagePatchWindows
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageTransfers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterImages

theorem gap_at : CodeAt expandImage (pcOf 243968) gap := by
  apply CodeAt.of_append (image:=expandImage) (code:=gap) (pre:=expandPrefix++cBank) (post:=bBank)
    (by simp only [expandImage,expandCode,List.append_assoc])
  · simp only [List.length_append,prefix_length,banks_length.2,pcOf]
    decide +kernel
  · simp only [List.length_append,prefix_length,banks_length.2,gap_length]
    decide +kernel

theorem gap_window : (expandImage.code.drop 243968).take 2496=(Images.expandImage.code.drop 243968).take 2496 := by
  have h:=OuterImagePatchWindows.slice (by decide : 243968<2^40) gap_at
  rw [gap_length] at h
  exact h

def Clean (b n : Nat) : Prop := (1≤b ∧ b+n≤54334) ∨ (54335≤b ∧ b+n≤84218) ∨
  (84219≤b ∧ b+n≤88260) ∨ (88339≤b ∧ b+n≤235776) ∨ (243968≤b ∧ b+n≤246464)
instance (b n : Nat) : Decidable (Clean b n) := by unfold Clean;infer_instance

theorem code {b : Nat} {words : List (BitVec 32)} (hb : Clean b words.length)
    (hc : CodeAt Images.expandImage (pcOf b) words) : CodeAt expandImage (pcOf b) words := by
  rcases hb with h|h|h|h|h
  · exact codeAt_of_window_eq (source:=Images.expandImage) (target:=expandImage) (start:=1) (count:=54333)
      h.1 h.2 (by decide) OuterInstalledDispatch.window.symm hc
  · exact OuterImageCopies.mid_code h.1 h.2 hc
  · exact OuterImageCopies.late_code h.1 h.2 hc
  · exact codeAt_of_window_eq (source:=Images.expandImage) (target:=expandImage) (start:=88339) (count:=147437)
      h.1 h.2 (by decide) (OuterImageWindows.high_window 88339 147437 (by decide) (by decide)).symm hc
  · exact codeAt_of_window_eq (source:=Images.expandImage) (target:=expandImage) (start:=243968) (count:=2496)
      h.1 h.2 (by decide) gap_window.symm hc

#print axioms code
end OuterImageTransfers
