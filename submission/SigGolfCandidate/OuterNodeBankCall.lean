import SigGolfCandidate.OuterNodeBankLayout
import SigGolfCandidate.OuterNodeSourceFacts
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeBankCall
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterNodeSourceSim

def jumpCode : List (BitVec 32) := [0x80006f]
sym_block jump := symRun {noAlias:=true} jumpCode 0 4

theorem jump_at (pc : Word) : symRun {noAlias:=true} jumpCode pc 4=
    some {jump.res with pc:=.c (pc+8#64)} := by rfl

theorem jump_run {im : Image} {s : MachineState} {pc : Word}
    (hc : CodeAt im pc jumpCode) (hp : s.pc=pc) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pc+8#64 ∧ (∀ r,t.getReg r=s.getReg r) ∧ (∀ a,t.getMem a=s.getMem a) := by
  let res : Result := {jump.res with pc:=.c (pc+8#64)}
  have h : symRun {noAlias:=true} jumpCode pc 4=some res := jump_at pc
  refine ⟨res.toState s,symRun_sound h hc s hp ?_,rfl,?_,?_⟩
  · simp [res,jump.res,Result.obligs,Oblig.all]
  · intro r
    rw [Result.toState_getReg]
    cases r <;> rfl
  · intro a
    rw [Result.toState_getMem]
    rfl

theorem input_of_equal {A D : Nat} {pre right : List UInt8} {s t : MachineState}
    (F : Input A D pre right s) (hg : ∀ r,t.getReg r=s.getReg r) (hm : ∀ a,t.getMem a=s.getMem a) :
    Input A D pre right t := by
  refine ⟨?_,?_,?_,?_,F.pre_len,F.right_len,?_,?_,F.alo,F.ahi,F.aa,F.dlo,F.dhi,F.da,F.disjoint⟩
  · rw [hg];exact F.x5
  · rw [hg];exact F.x10
  · rw [hg];exact F.x11
  · rw [hg];exact F.x12
  · simpa only [MachineState.readWords,hm] using F.pre_words
  · simpa only [MachineState.readWords,hm] using F.right_words

theorem out_of_equal {coord heap A D : Nat} {s u t : MachineState} {ret : Word} {res : Nat×Digest}
    (h : SourceOut coord heap u A D ret res t)
    (hg : ∀ r,u.getReg r=s.getReg r) (hm : ∀ a,u.getMem a=s.getMem a) :
    SourceOut coord heap s A D ret res t := by
  obtain ⟨raw,hk,ho⟩:=h
  have hr : OuterNodeMachinePost.recordAddr u=OuterNodeMachinePost.recordAddr s := by simp only [OuterNodeMachinePost.recordAddr,hg,hm]
  refine ⟨raw,hk,ho.at_pc,?_,ho.answer,?_,?_⟩
  · intro r hn
    rw [ho.regs.get hn,hg]
  · rw [←hr];exact ho.record
  · intro X hX hn
    rw [←hm]
    apply ho.frame X hX
    simpa only [hr] using hn

theorem jump_slicesB : ∀ j : Fin 128,
    ((OuterNodeBankLayout.bWords j.val).drop (OuterNodeBankLayout.bSite j.val)).take 1=jumpCode := by decide +kernel
theorem jump_slicesC : ∀ j : Fin 128,
    ((OuterNodeBankLayout.cWords j.val).drop (OuterNodeBankLayout.cSite j.val)).take 1=jumpCode := by decide +kernel

theorem runB {im : Image} {sk : BitVec 256} {A D coord index heap : Nat} {left right : Digest}
    {s : MachineState} (j : Fin 128) (hc8 : coord≠8)
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j.val)) (OuterNodeBankLayout.bWords j.val))
    (hp : s.pc=pcOf (W9Drv.SharedBProof.childBase j.val+OuterNodeBankLayout.bSite j.val)) :
    TBSim im sk s 30735 (OuterGroundCore.nodeAt coord index heap left right)
      (SourceOut coord heap s A D (pcOf (W9Drv.SharedBProof.childBase j.val+OuterNodeBankLayout.bSite j.val+2)-4#64)) := by
  have hlen:=(OuterNodeBankLayout.b_slices j).1
  have hspace:=OuterNodeBankLayout.b_space j
  have hj:=codeAt_sub (seg:=jumpCode) (OuterNodeBankLayout.bSite j.val) hc (by rw [hlen];change _+1≤64;omega) (jump_slicesB j)
  obtain ⟨u,hs,hpu,hg,hm⟩:=jump_run hj hp
  have F':=input_of_equal F hg hm
  have hpu' : u.pc=pcOf (W9Drv.SharedBProof.childBase j.val+OuterNodeBankLayout.bSite j.val+2) := by
    rw [hpu]
    simp only [pcOf,Nat.mul_add,ofNat_add_ofNat]
    rfl
  have he:=OuterNodeSourceSim.runB (sk:=sk) hc8 F' (OuterNodeBankLayout.b_helper_code j hc) hpu'
  exact (TBSim.steps hs he).mono (by omega) (fun a t ht=>out_of_equal ht hg hm)

theorem runC {im : Image} {sk : BitVec 256} {A D index heap : Nat} {left right : Digest}
    {s : MachineState} (j : Fin 128) (hh : heap=2 ∨ heap=3)
    (F : Input A D (OuterNodeRawModel.pre 8 index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : CodeAt im (pcOf (W9Drv.SharedCProof.childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    (hp : s.pc=pcOf (W9Drv.SharedCProof.childBase j.val+OuterNodeBankLayout.cSite j.val)) :
    TBSim im sk s 77839 (OuterGroundCore.nodeAt 8 index heap left right)
      (SourceOut 8 heap s A D (pcOf (W9Drv.SharedCProof.childBase j.val+OuterNodeBankLayout.cSite j.val+2)-4#64)) := by
  have hlen:=(OuterNodeBankLayout.c_slices j).1
  have hspace:=OuterNodeBankLayout.c_space j
  have hj:=codeAt_sub (seg:=jumpCode) (OuterNodeBankLayout.cSite j.val) hc (by rw [hlen];change _+1≤64;omega) (jump_slicesC j)
  obtain ⟨u,hs,hpu,hg,hm⟩:=jump_run hj hp
  have F':=input_of_equal F hg hm
  have hpu' : u.pc=pcOf (W9Drv.SharedCProof.childBase j.val+OuterNodeBankLayout.cSite j.val+2) := by
    rw [hpu]
    simp only [pcOf,Nat.mul_add,ofNat_add_ofNat]
    rfl
  have he:=OuterNodeSourceFacts.runC (sk:=sk) hh F' (OuterNodeBankLayout.c_helper_code j hc) hpu'
  exact (TBSim.steps hs he).mono (by omega) (fun a t ht=>out_of_equal ht hg hm)

#print axioms runB
#print axioms runC

#print axioms jump_run
#print axioms input_of_equal
end OuterNodeBankCall
