import SigGolfCandidate.OuterCopyTailC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCopyFlatC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedCProof OuterNodeSearchInvariant
open SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

def TailWrites (coord j X : Nat) : Prop :=
  (∃ off∈stagesW j 6,X=coordRegion coord+off) ∨
    Work (coordRegion coord+blkO j 5) (coordRegion coord-handO j) X ∨ X=8323072+(coord-1)*4096

theorem base_bounds (coord : Fin 9) : 1848≤coordRegion coord.val ∧ coordRegion coord.val<2^14 := by
  rw [OuterNodeControllerGeometry.actual_frame coord]
  unfold OuterNodeBufferGeometry.frameBase W9Machine.V3.regionOffset
  have := coord.isLt
  omega

theorem outside (coord : Fin 9) (j : Fin 128) (X : Nat) (hx : X<8323072)
    (hb : X<1848 ∨ 2^20≤X) (h6 : X≠1152) (h7 : X≠1160) : ¬TailWrites coord.val j.val X := by
  have hB:=base_bounds coord
  have hg:=OuterNodeControllerGeometry.c_geometry coord j.val
  have hbl:=blk_bounds j.val j.isLt 5 (by decide)
  rintro (⟨off,hoff,he⟩|hw|he)
  · have ho:=stagesW_bound j.isLt (by decide) hoff
    omega
  · unfold Work at hw
    rcases hw with he|he|⟨hle,hlt⟩|he|he <;> omega
  · omega

structure Post (coord j : Nat) (u : MachineState) (res : Nat×Nat×Digest) (t : MachineState) : Prop where
  pc : t.pc=(u.getReg .x1+316#64) &&& ~~~1#64
  a1 : t.getReg .x11=64
  a2 : t.getReg .x12=BitVec.ofNat 64 (coordRegion coord-handO j)
  top : DigAt t (coordRegion coord-handO j+OuterGroundCore.offset coord (heapOf 5 j)/8) res.2.2
  outer : t.getMem (BitVec.ofNat 64 (8323072+(coord-1)*4096))=BitVec.ofNat 64 res.2.1
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r=u.getReg r
  slot0 : t.getMem (BitVec.ofNat 64 (slotA (coordRegion coord)))=BitVec.ofNat 64 (coordRegion coord+blkO j 3+WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slotA (coordRegion coord)+8))=BitVec.ofNat 64 res.1
  nle : res.1≤FUEL (widthOf (coordRegion coord))
  saves : ∀ i,i<5→t.getMem (BitVec.ofNat 64 (1104+8*i))=0
  scr : ∀ i,i<4→t.getMem (BitVec.ofNat 64 (SCR+8*i))=0
  frame : Frame u t (fun X=>OuterCopyGroundC.Changes (coordRegion coord) j X ∨ TailWrites coord j X)

theorem flatten (coord : Fin 9) (j : Fin 128) (index : Nat) (pads sibs : Nat→Digest)
    (u t : MachineState) (res : Nat×Nat×Digest) (h : OuterCopyTailC.Post coord.val index j.val pads sibs u res t) :
    Post coord.val j.val u res t := by
  obtain ⟨mid,v4,u',hground,hvirt,hregs,hframe,htail⟩:=h
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hslot0,hslot1,hnle,hsaves,hscr⟩:=hground
  obtain ⟨hp,h11,h12,hd,hn,hkeep,htframe⟩:=htail
  have hB:=base_bounds coord
  have rd : ∀ X,X<8323072→(X<1848 ∨ 2^20≤X)→X≠1152→X≠1160→
      t.getMem (BitVec.ofNat 64 X)=mid.getMem (BitVec.ofNat 64 X) := by
    intro X hX hlow h6 h7
    rw [htframe X (by omega) (outside coord j X hX hlow h6 h7),hvirt,
      virt_getMem j.val (coordRegion coord.val) u mid (by omega) j.isLt X (by omega),if_neg]
    rintro ⟨off,hoff,he⟩
    have ho:=stagesW_bound j.isLt (by decide) hoff
    omega
  refine ⟨?_,h11,h12,hd,hn,?_,?_,?_,hnle,?_,?_,?_⟩
  · rw [hp,hregs]
  · intro r h3 h10 h11 h12
    rw [hkeep r h3 h10 h11 h12,hregs]
  · rw [rd _ (by unfold slotA SCR;omega) (Or.inr (by unfold slotA SCR;omega))
      (by unfold slotA SCR;omega) (by unfold slotA SCR;omega)]
    exact hslot0
  · rw [rd _ (by unfold slotA SCR;omega) (Or.inr (by unfold slotA SCR;omega))
      (by unfold slotA SCR;omega) (by unfold slotA SCR;omega)]
    exact hslot1
  · intro i hi
    rw [rd _ (by omega) (Or.inl (by omega)) (by omega) (by omega)]
    exact hsaves i hi
  · intro i hi
    rw [rd _ (by unfold SCR;omega) (Or.inr (by unfold SCR;omega)) (by unfold SCR;omega) (by unfold SCR;omega)]
    exact hscr i hi
  · exact hframe.trans htframe

#print axioms outside
#print axioms flatten
end OuterCopyFlatC
