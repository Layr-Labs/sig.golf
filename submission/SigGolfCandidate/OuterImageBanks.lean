import SigGolfCandidate.OuterImages
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageBanks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterImages

theorem b_slices : ∀ j : Fin 128,
    (bBank.drop (64*(2*(j.val%64)+j.val/64))).take 64=OuterNodeBankLayout.bWords j.val := by decide +kernel

theorem c_slices : ∀ j : Fin 128,
    (cBank.drop (64*(2*(j.val%64)+j.val/64))).take 64=OuterNodeBankLayout.cWords j.val := by decide +kernel

theorem b_bank : CodeAt expandImage (pcOf 246464) bBank := by
  apply CodeAt.of_append (pre:=expandPrefix++cBank++gap) (post:=[]) (by simp [expandImage,expandCode,List.append_assoc])
  · simp only [pcOf,List.length_append,prefix_length,banks_length.2,gap_length]
    decide +kernel
  · rw [List.length_append,List.length_append,prefix_length,banks_length.2,gap_length,banks_length.1]
    decide +kernel

theorem c_bank : CodeAt expandImage (pcOf 235776) cBank := by
  apply CodeAt.of_append (pre:=expandPrefix) (post:=gap++bBank) (by simp [expandImage,expandCode,List.append_assoc])
  · simp only [pcOf,prefix_length]
    decide +kernel
  · rw [prefix_length,banks_length.2]
    decide +kernel

theorem b_child (j : Fin 128) : CodeAt expandImage (pcOf (W9Drv.SharedBProof.childBase j.val)) (OuterNodeBankLayout.bWords j.val) := by
  have hl:=(OuterNodeBankLayout.b_slices j).1
  have hs:=b_slices j
  have hs' : (bBank.drop (64*(2*(j.val%64)+j.val/64))).take (OuterNodeBankLayout.bWords j.val).length=OuterNodeBankLayout.bWords j.val := by simpa only [hl] using hs
  exact SigGolfCandidate.FtsGrind.codeAt_sub (64*(2*(j.val%64)+j.val/64)) b_bank (by rw [banks_length.1]; have :=j.isLt; omega) hs'

theorem c_child (j : Fin 128) : CodeAt expandImage (pcOf (W9Drv.SharedCProof.childBase j.val)) (OuterNodeBankLayout.cWords j.val) := by
  have hl:=(OuterNodeBankLayout.c_slices j).1
  have hs:=c_slices j
  have hs' : (cBank.drop (64*(2*(j.val%64)+j.val/64))).take (OuterNodeBankLayout.cWords j.val).length=OuterNodeBankLayout.cWords j.val := by simpa only [hl] using hs
  exact SigGolfCandidate.FtsGrind.codeAt_sub (64*(2*(j.val%64)+j.val/64)) c_bank (by rw [banks_length.2]; have :=j.isLt; omega) hs'

#print axioms b_child
#print axioms c_child
end OuterImageBanks
