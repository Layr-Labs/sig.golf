import SigGolfCandidate.OuterImageControlTransfers
import SigGolfCandidate.OuterNoncePostRecords
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterControlRun
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind

theorem jump {im : Image} (a t : Nat) (ha : a<2^18) (ht : t<2^18)
    (hc : CodeAt im (pcOf a) [OuterImages.jump a t]) (s : MachineState) (hp : s.pc=pcOf a) :
    ∃ u,Steps im s 1 1 u ∧ u.pc=pcOf t ∧ (∀ r,u.getReg r=s.getReg r) ∧ (∀ X,u.getMem X=s.getMem X) := by
  refine ⟨_,jal_step (rd:=0) (r:=.x0) (by decide) rfl hc ha ht s hp,rfl,?_,?_⟩
  · intro r
    cases r <;> rfl
  · intro X
    rfl

theorem post (s : MachineState) (hp : s.pc=pcOf 84218) :
    ∃ t,Steps OuterImages.expandImage s 21 21 t ∧ t.pc=pcOf 88280 ∧
      fetch OuterImages.expandImage t=some (.base .ECALL) ∧ RegsExcept s t [.x6,.x7] ∧
      t.getMem 11088=s.getMem 8323072 ∧ t.getMem 9392=s.getMem 8331264 ∧
      t.getMem 7696=s.getMem 8339456 ∧ t.getMem 6000=s.getMem 8347648 ∧ t.getMem 5152=s.getMem 8351744 ∧
      ∀ X,X∉OuterNoncePostMachine.destinations → t.getMem X=s.getMem X := by
  obtain ⟨u,hjump,hpc,hg,hm⟩:=jump 84218 88260 (by decide) (by decide) OuterImageControlTransfers.post_jump s hp
  obtain ⟨t,hrun,htpc,hregs,h0,h1,h2,h3,h4,hframe⟩:=OuterNoncePostMachine.run OuterImageHelpers.expand_post u hpc
  refine ⟨t,hjump.trans hrun,htpc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact OuterImageControlTransfers.post_halt.fetch t htpc
  · intro r hn
    rw [hregs r hn,hg]
  · rw [h0,hm]
  · rw [h1,hm]
  · rw [h2,hm]
  · rw [h3,hm]
  · rw [h4,hm]
  · intro X hn
    rw [hframe X hn,hm]

#print axioms jump
#print axioms post
end OuterControlRun
