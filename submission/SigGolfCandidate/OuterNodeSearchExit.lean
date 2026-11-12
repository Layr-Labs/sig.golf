import SigGolfCandidate.OuterNodeSearchInvariant
import SigGolfCandidate.OuterNodePostRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeSearchExit
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterNodeMachinePost

structure Out (s : MachineState) (A D : Nat) (ret : Word) (res : Nat × HashOutput) (t : MachineState) : Prop where
  at_pc : t.pc=ret
  regs : RegsExcept s t []
  answer : Answer A D res.1 res.2 t
  record : t.getMem (recordAddr s)=BitVec.ofNat 64 res.1
  frame : Frame s t (fun X=>Work A D X ∨ X=(recordAddr s).toNat)

theorem record_preserved {A D n : Nat} {pre right : List UInt8} {s u : MachineState} {pc : Word}
    (F : Input A D pre right s) (hu : Stage s A D pc n u) : recordAddr u=recordAddr s := by
  have gx : u.getReg .x10=s.getReg .x10 := hu.regs.get (by decide)
  have ha:=F.ahi;have hlo:=F.alo;have hsep:=F.disjoint
  unfold recordAddr
  rw [gx,F.x10,ofNat_add_ofNat,hu.frame.get (by omega) (by unfold Work;omega)]

theorem runB {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im pc OuterNodeMachineBlocks.b_postCode)
    (hu : Stage s A D pc n u) (hh : Answer A D n a u) :
    TBSim im sk u 9 (pure (n,a)) (Out s A D (pc-56#64)) := by
  have ha:=F.ahi;have hd:=F.dhi
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  obtain ⟨t,hs,hp,hr,hrec,h6,h7,hm⟩:=OuterNodePostRun.runB pc hc u hu.at_pc A gx F.ahi F.alo F.aa
  have hR:=record_preserved F hu
  rw [hR,hu.nonce] at hrec
  have keep : ∀ X,X<2^22 → t.getMem (BitVec.ofNat 64 X)=u.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    exact hm _ (OuterNodePostRun.record_ne_low u _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];exact hX))
  refine tb_pure_steps hs ⟨hp,?_,⟨?_,?_,?_⟩,hrec,?_⟩
  · intro reg _
    by_cases hreg : reg∈[Reg.x6,Reg.x7]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hreg
      rcases hreg with rfl|rfl
      · rw [h6];exact hu.saved6
      · rw [h7];exact hu.saved7
    · rw [hr.get hreg,hu.regs.get hreg]
  · intro k hk;rw [keep _ (by omega)];exact hh.output k hk
  · rw [keep _ (by omega)];exact hh.pad32
  · rw [keep _ (by omega)];exact hh.pad40
  · intro X hX hne
    rw [hm _ (by
      rw [hR]
      intro he
      exact hne (Or.inr (by rw [←he,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hX])))]
    exact hu.frame X hX (fun h=>hne (Or.inl h))

theorem runC {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im pc OuterNodeMachineBlocks.c_postCode)
    (hu : Stage s A D pc n u) (hh : Answer A D n a u) :
    TBSim im sk u 9 (pure (n,a)) (Out s A D (pc-72#64)) := by
  have ha:=F.ahi;have hd:=F.dhi
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  obtain ⟨t,hs,hp,hr,hrec,h6,h7,hm⟩:=OuterNodePostRun.runC pc hc u hu.at_pc A gx F.ahi F.alo F.aa
  have hR:=record_preserved F hu
  rw [hR,hu.nonce] at hrec
  have keep : ∀ X,X<2^22 → t.getMem (BitVec.ofNat 64 X)=u.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    exact hm _ (OuterNodePostRun.record_ne_low u _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];exact hX))
  refine tb_pure_steps hs ⟨hp,?_,⟨?_,?_,?_⟩,hrec,?_⟩
  · intro reg _
    by_cases hreg : reg∈[Reg.x6,Reg.x7]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hreg
      rcases hreg with rfl|rfl
      · rw [h6];exact hu.saved6
      · rw [h7];exact hu.saved7
    · rw [hr.get hreg,hu.regs.get hreg]
  · intro k hk;rw [keep _ (by omega)];exact hh.output k hk
  · rw [keep _ (by omega)];exact hh.pad32
  · rw [keep _ (by omega)];exact hh.pad40
  · intro X hX hne
    rw [hm _ (by
      rw [hR]
      intro he
      exact hne (Or.inr (by rw [←he,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hX])))]
    exact hu.frame X hX (fun h=>hne (Or.inl h))

#print axioms runB
#print axioms runC
#print axioms record_preserved
end OuterNodeSearchExit
