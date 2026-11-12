import SigGolfCandidate.OuterSignTransfers
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignLook
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify ClaudeWCT.W9.Machine.Sign

theorem transfer (L : Nat→Option (BitVec 32)) (hL : LookOK Images.signImage L)
    (h0 : L 1977=none) (h1 : L 25338=none) (h2 : L 25963=none) : LookOK OuterImages.signImage L := by
  intro n w hw
  have hold:=hL n w hw
  have hn : n<26156 := by
    have hh : n<Images.signImage.code.length := List.getElem?_eq_some_iff.mp hold |>.1
    simpa only [Images.signImage,Images.signCode_length] using hh
  have he0 : n≠1977 := by intro he;subst n;rw [h0] at hw;contradiction
  have he1 : n≠25338 := by intro he;subst n;rw [h1] at hw;contradiction
  have he2 : n≠25963 := by intro he;subst n;rw [h2] at hw;contradiction
  have hc : CodeAt Images.signImage (pcOf n) [w] :=
    ClaudeWCT.W9.Machine.Expand.codeAt_of_look hL n [w] (by simp only [List.length_singleton];omega) (by
      intro i hi
      have hi0 : i=0 := by simp only [List.length_singleton] at hi;omega
      subst i
      simpa using hw)
  have hnew:=OuterSignTransfers.code (b:=n) (words:=[w]) (by unfold OuterSignTransfers.Clean;simp only [List.length_singleton];omega) hc
  have he:=SharedReuse.codeAt_get_word (i:=0) (w:=w) (by omega : n<2^30) hnew (by simp)
  simpa using he

theorem node (c : Nat) (hc : c<9) : LookOK OuterImages.signImage (SharedNode.look c) := by
  have h : ∀c:Fin 9,SharedNode.look c.val 1977=none ∧ SharedNode.look c.val 25338=none ∧ SharedNode.look c.val 25963=none := by decide +kernel
  exact transfer _ (SharedNode.installed_look c hc) (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2

theorem tail (c : Nat) (hc : c<9) : LookOK OuterImages.signImage (SharedTail.look c) := by
  have h : ∀c:Fin 9,SharedTail.look c.val 1977=none ∧ SharedTail.look c.val 25338=none ∧ SharedTail.look c.val 25963=none := by decide +kernel
  exact transfer _ (SharedTail.installed_look c hc) (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
#print axioms transfer
#print axioms node
#print axioms tail
end OuterSignLook
