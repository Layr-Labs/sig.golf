import SigGolfCandidate.OuterImageWindows
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageBankA
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M W9Machine W9Drv

theorem bounds : ∀ j : Fin 128,
    88339≤SharedAProof.childBase j.val ∧ SharedAProof.childBase j.val+(SharedAProof.childWords j.val).length≤235776 := by decide +kernel

theorem code (j : Nat) (hj : j<128) : SharedAProof.ChildCodeAt OuterImages.expandImage j := by
  have hwin : (Frozen.image.code.drop 195584).take 59072=(Images.expandImage.code.drop 195584).take 59072 := by
    rw [Frozen.image_eq]
    exact Images.expand_banks_eq_verify.symm
  have hold:=SharedAProof.childCodeAt_transfer j hj hwin (SharedAProof.shared_code j hj)
  intro i w hi
  have hb:=bounds ⟨j,hj⟩
  dsimp only at hb
  obtain ⟨hil,hival⟩:=List.getElem?_eq_some_iff.mp hi
  rw [OuterImageWindows.high_word (SharedAProof.childBase j+i) (by omega) (by omega)]
  exact hold i w hi

#print axioms code
end OuterImageBankA
