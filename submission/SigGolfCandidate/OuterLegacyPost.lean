import SigGolfCandidate.OuterImageCopies
import SigGolfCandidate.OuterImageControlTransfers
import SigGolfCandidate.FtsExpandPost
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLegacyPost
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind

def body16 : List (BitVec 32) := post16Words.take 18
sym_block post16Block := symRun cfgP body16 (pcOf POST16) 18

theorem run16 {im : Image} (hc : CodeAt im (pcOf POST16) body16) (s : MachineState)
    (hpc : s.pc=pcOf POST16) (addr : Nat → Nat)
    (hm : ∀ k,k<4 → s.getMem (BitVec.ofNat 64 (slot16 (sB k)))=BitVec.ofNat 64 (addr k))
    (hb : ∀ k,k<4 → addr k%8=0 ∧ addr k+8≤SCR) :
    ∃ t,Steps im s 18 18 t ∧ t.pc=pcOf (POST16+18) ∧ RegsExcept s t [.x29,.x30,.x31] ∧
      (∀ A,t.getMem A=postMem16 s.getMem A) := by
  have h0:=hm 0 (by decide);have h1:=hm 1 (by decide);have h2:=hm 2 (by decide);have h3:=hm 3 (by decide)
  have b0:=hb 0 (by decide);have b1:=hb 1 (by decide);have b2:=hb 2 (by decide);have b3:=hb 3 (by decide)
  simp only [sB,slot16,SCR16,SCR,Nat.reduceMul,Nat.reduceSub,Nat.reduceAdd] at h0 h1 h2 h3 b0 b1 b2 b3
  have hob : post16Block.res.obligs s := by
    simp only [post16Block.res]
    pn [h0,h1,h2,h3]
    omega
  refine ⟨_,symRun_sound post16Block hc s hpc hob,?_,?_,?_⟩
  · simp [post16Block.res,Result.toState_pc,E.eval,POST16]
  · intro r hr
    simp at hr
    cases r <;> simp_all [post16Block.res] <;> first | rfl | (pn [];rfl)
  · intro A
    simp only [Result.toState_getMem,post16Block.res,postMem16,upd,List.range,List.range.loop,List.foldl,sB,slot16,SCR16]
    pn [h0,h1,h2,h3]

theorem installed16 : CodeAt OuterImages.expandImage (pcOf POST16) body16 := by
  apply OuterImageCopies.mid_code (by decide) (by decide +kernel)
  have H:=SigGolfCandidate.FtsGrind.codeAt_sub 0 W9Drv.SharedBank.codeAt_post16 (seg:=body16) (by decide +kernel) (by decide +kernel)
  simpa only [Nat.add_zero] using H

theorem installed3 : CodeAt OuterImages.expandImage (pcOf POST) postWords :=
  OuterImageCopies.mid_code (by decide) (by rw [postWords_length];decide) W9Drv.SharedBank.codeAt_post

#print axioms run16
#print axioms installed16
#print axioms installed3
end OuterLegacyPost
