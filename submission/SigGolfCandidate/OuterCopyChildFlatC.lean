import SigGolfCandidate.OuterCopyChildC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCopyChildFlatC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedCProof
open SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

def Writes (coord j X : Nat) : Prop :=
  OuterCopyLayer2C.Changes (coordRegion coord) j X ∨
    OuterCopyGroundC.Changes (coordRegion coord) j X ∨ OuterCopyFlatC.TailWrites coord j X

theorem base_max (coord : Fin 9) : coordRegion coord.val≤9768 := by
  rw [OuterNodeControllerGeometry.actual_frame coord]
  exact (OuterNodeBufferGeometry.frame_bounds coord.val coord.isLt).2.1

theorem outside16 (coord : Fin 9) (j : Fin 128) (X : Nat)
    (hx : (slot16 (coordRegion coord.val)≤X ∧ X<slot16 (coordRegion coord.val)+16) ∨ (SCR16≤X ∧ X<SCR16+32)) :
    ¬(OuterCopyGroundC.Changes (coordRegion coord.val) j.val X ∨ OuterCopyFlatC.TailWrites coord.val j.val X) := by
  have hb:=base_max coord
  have hlo:=OuterCopyFlatC.base_bounds coord
  have hbl:=blk_bounds j.val j.isLt 3 (by decide)
  have htail:=OuterCopyFlatC.outside coord j X (by unfold slot16 SCR16 at hx;omega)
    (Or.inr (by unfold slot16 SCR16 at hx;omega)) (by unfold slot16 SCR16 at hx;omega) (by unfold slot16 SCR16 at hx;omega)
  rintro (hg|ht)
  · unfold OuterCopyGroundC.Changes at hg
    simp only [slotA,slot16,SCR,SCR16] at hg hx
    unfold padO at hg
    omega
  · exact htail ht

structure Post (coord j : Nat) (u : MachineState) (res : Nat×Nat×Nat×Digest) (t : MachineState) : Prop where
  pc : t.pc=(u.getReg .x1+316#64) &&& ~~~1#64
  a1 : t.getReg .x11=64
  a2 : t.getReg .x12=BitVec.ofNat 64 (coordRegion coord-handO j)
  top : DigAt t (coordRegion coord-handO j+OuterGroundCore.offset coord (heapOf 5 j)/8) res.2.2.2
  outer : t.getMem (BitVec.ofNat 64 (8323072+(coord-1)*4096))=BitVec.ofNat 64 res.2.2.1
  keep : ∀ r : Reg, r ≠ .x3  →  r ≠ .x10  →  r ≠ .x11  →  r ≠ .x12  →  t.getReg r=u.getReg r
  slot0 : t.getMem (BitVec.ofNat 64 (slotA (coordRegion coord)))=BitVec.ofNat 64 (coordRegion coord+blkO j 3+WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slotA (coordRegion coord)+8))=BitVec.ofNat 64 res.1
  nle : res.1≤FUEL (widthOf (coordRegion coord))
  rec0 : decide (SEL16≤coordRegion coord)=true → t.getMem (BitVec.ofNat 64 (slot16 (coordRegion coord)))=BitVec.ofNat 64 (coordRegion coord+blkO j 2+WADJ)
  rec1 : decide (SEL16≤coordRegion coord)=true → t.getMem (BitVec.ofNat 64 (slot16 (coordRegion coord)+8))=BitVec.ofNat 64 res.2.1
  nle16 : res.2.1≤255
  n0 : decide (SEL16≤coordRegion coord)=false → res.2.1=0
  saves : ∀ i,i<5 → t.getMem (BitVec.ofNat 64 (1104+8*i))=0
  scr : ∀ i,i<4 → t.getMem (BitVec.ofNat 64 (SCR+8*i))=0
  scr16 : decide (SEL16≤coordRegion coord)=true → ∀ i,i<4 → t.getMem (BitVec.ofNat 64 (SCR16+8*i))=0
  frame : Frame u t (Writes coord j)

theorem flatten (coord : Fin 9) (j : Fin 128) (index : Nat) (u t : MachineState) (res : Nat×Nat×Nat×Digest)
    (h : OuterCopyChildC.Post coord.val index j.val u res t) : Post coord.val j.val u res t := by
  obtain ⟨s6,raw2,h6,hp⟩:=h
  have hb:=OuterCopyFlatC.base_bounds coord
  have hbl:=blk_bounds j.val j.isLt 2 (by decide)
  have vu : ∀ r,(virt2 j.val (coordRegion coord.val) u s6).getReg r=u.getReg r := by intro r;cases r <;> rfl
  have rd : ∀ X,X<2^64 → ((slot16 (coordRegion coord.val)≤X ∧ X<slot16 (coordRegion coord.val)+16) ∨
      (SCR16≤X ∧ X<SCR16+32)) → t.getMem (BitVec.ofNat 64 X)=s6.getMem (BitVec.ofNat 64 X) := by
    intro X hX hx
    rw [hp.frame.get hX (outside16 coord j X hx),virt2_getMem j.val (coordRegion coord.val) u s6 X hX (by unfold padO;omega),if_pos]
    apply Or.inr ∘ Or.inr
    rcases hx with hx|hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  refine ⟨?_,hp.a1,hp.a2,hp.top,hp.outer,?_,hp.slot0,hp.slot1,hp.nle,?_,?_,h6.nle,h6.n0,hp.saves,hp.scr,?_,?_⟩
  · rw [hp.pc,vu]
  · intro r h3 h10 h11 h12
    rw [hp.keep r h3 h10 h11 h12,vu]
  · intro hsel
    rw [rd _ (by unfold slot16 SCR16;omega) (Or.inl ⟨by omega,by omega⟩)]
    exact h6.rec0 hsel
  · intro hsel
    rw [rd _ (by unfold slot16 SCR16;omega) (Or.inl ⟨by omega,by omega⟩)]
    exact h6.rec1 hsel
  · intro hsel i hi
    rw [rd _ (by unfold SCR16;omega) (Or.inr ⟨by omega,by omega⟩)]
    exact h6.scr hsel i hi
  · have hv : Frame u (virt2 j.val (coordRegion coord.val) u s6) (OuterCopyLayer2C.Changes (coordRegion coord.val) j.val) := by
      intro X hX hn
      change ¬(X=coordRegion coord.val+padO j.val 2 ∨ X=coordRegion coord.val+padO j.val 2+8 ∨ far16 (coordRegion coord.val) X) at hn
      rw [virt2_getMem j.val (coordRegion coord.val) u s6 X hX (by unfold padO;omega),if_neg hn]
    exact hv.trans hp.frame

#print axioms outside16
#print axioms flatten
end OuterCopyChildFlatC
