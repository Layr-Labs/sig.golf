import SigGolfCandidate.OuterImageSignWindows
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignTransfers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind ClaudeWCT.W9.Machine.Expand

def Clean (b n : Nat) : Prop := b+n≤26156 ∧ (b+n≤1977 ∨ 1978≤b) ∧ (b+n≤25338 ∨ 25339≤b) ∧ (b+n≤25963 ∨ 25964≤b)
instance (b n : Nat) : Decidable (Clean b n) := by unfold Clean;infer_instance

theorem window (b n : Nat) (h : Clean b n) :
    (OuterImages.signImage.code.drop b).take n=(Images.signImage.code.drop b).take n := by
  apply OuterImageSignWindows.unchanged_window b n h.1
  intro i hlo hhi w
  simp only [OuterImages.signPatch,if_neg (by rcases h.2.1 with h|h <;> omega : i≠1977),
    if_neg (by rcases h.2.2.1 with h|h <;> omega : i≠25338),if_neg (by rcases h.2.2.2 with h|h <;> omega : i≠25963)]

theorem code {b : Nat} {words : List (BitVec 32)} (hb : Clean b words.length)
    (hc : CodeAt Images.signImage (pcOf b) words) : CodeAt OuterImages.signImage (pcOf b) words := by
  exact codeAt_of_window_eq (source:=Images.signImage) (target:=OuterImages.signImage) (start:=b) (count:=words.length)
    le_rfl (by omega) (by have:=hb.1;omega) (window b words.length hb).symm hc
theorem tail_window (b n : Nat) (hb : 26241≤b) :
    (OuterImages.signImage.code.drop b).take n=(Images.signImage.code.drop b).take n := by
  let pre := (Images.signCode.take 26156).mapIdx OuterImages.signPatch ++
    OuterSignImageLayout.code ++ OuterCodecMachine.packCode ++ [0x73]
  have hp : pre.length=26241 := by
    simp only [pre,List.length_append,List.length_mapIdx,List.length_take,Images.signCode_length]
    decide +kernel
  have he : OuterImages.signImage.code=pre++Images.signCode.drop 26241 := by
    simp [OuterImages.signImage,OuterImages.signCode,pre,List.append_assoc]
  rw [he,List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,List.drop_drop,hp]
  rw [show 26241+(b-26241)=b by omega]
  rfl

theorem code_tail {b : Nat} {words : List (BitVec 32)} (hb : 26241≤b) (he : b+words.length≤26415)
    (hc : CodeAt Images.signImage (pcOf b) words) : CodeAt OuterImages.signImage (pcOf b) words := by
  exact codeAt_of_window_eq (source:=Images.signImage) (target:=OuterImages.signImage) (start:=b) (count:=words.length)
    le_rfl (by omega) (by omega) (tail_window b words.length hb).symm hc

#print axioms code
end OuterSignTransfers
