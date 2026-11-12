import SigGolfCandidate.OuterNodeSearchExit
import SigGolfCandidate.OuterNodeCheckRun
import SigGolfCandidate.OuterNodeCounterRun
import SigGolfCandidate.OuterNodeLastRun
import SigGolfCandidate.OuterNodeHashZero
import SigGolfCandidate.OuterNodeLoopControl
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeSearchC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterNodeMachineBlocks

def high (heap : Nat) : Bool := if heap=3 then false else true

theorem ok (heap : Nat) (a : HashOutput) : zeroOkH (high heap) 4 a=true ↔
    (a.extractLsb' (if heap=3 then 64 else 192) 64 >>> 60)=0 := by
  by_cases hh : heap=3
  · have h:=OuterNodeHashZero.upper_word_iff (a.extractLsb' 0 128) 4 (by decide)
    rw [OuterNodeHashZero.low_word] at h
    simpa [zeroOkH,halfOf,high,hh,Nat.div_eq_zero_iff] using h.symm
  · have h:=OuterNodeHashZero.upper_word_iff (a.extractLsb' 128 128) 4 (by decide)
    rw [OuterNodeHashZero.high_word] at h
    simpa [zeroOkH,halfOf,high,hh,Nat.div_eq_zero_iff] using h.symm

theorem check {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pc+8#64) c_checkCode) (hu : Stage s A D (pc+8#64) n u)
    (hh : Answer A D n a u) :
    ∃ t,Steps im u 7 7 t ∧
      Stage s A D (if zeroOkH (high heap) 4 a then pc+52#64 else pc+36#64) n t ∧ Answer A D n a t := by
  have ga : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have gx : u.getReg .x12=BitVec.ofNat 64 D := by rw [hu.regs.get (by decide)];exact F.x12
  have heap_word : u.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap := by
    rw [heap_preserved F hu.frame];exact hmem
  obtain ⟨t,hs,hr,hp,hm⟩:=OuterNodeCheckRun.runC (pc+8#64) hc u hu.at_pc A D heap ga gx
    F.ahi F.alo F.aa F.dhi F.dlo F.da hheap heap_word
  have ho : u.getMem (u.getReg .x12+(if heap=3 then 8#64 else 24#64))=
      a.extractLsb' (if heap=3 then 64 else 192) 64 := by
    by_cases hh3 : heap=3
    · simp only [if_pos hh3,gx,ofNat_add_ofNat]
      exact hh.output 1 (by decide)
    · simp only [if_neg hh3,gx,ofNat_add_ofNat]
      exact hh.output 3 (by decide)
  simp only [show (8:Word)=8#64 from rfl,show (24:Word)=24#64 from rfl] at hp
  rw [ho] at hp
  simp only [←ok] at hp
  have hp' : t.pc=(if zeroOkH (high heap) 4 a then pc+52#64 else pc+36#64) := by
    simpa only [BitVec.add_assoc,BitVec.reduceAdd] using hp
  refine ⟨t,hs,hu.readOnly hp' (hr.mono (by simp)) ?_ hm,hh.readOnly hm⟩
  rw [hr.get (by decide)];exact hu.nonce

theorem retry {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pc+8#64) c_checkCode) (hf : CodeAt im (pc+36#64) c_failureCode)
    (hu : Stage s A D (pc+8#64) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH (high heap) 4 a=true) (hn : n+1<4096) :
    ∃ t,Steps im u 10 10 t ∧ Stage s A D pc (n+1) t := by
  obtain ⟨v,hs,hv,hav⟩:=check F heap hheap hmem hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hp,hm⟩:=OuterNodeCounterRun.runC (pc+36#64) hf v hv.at_pc n (by omega) hv.nonce
  rw [if_pos hn] at hp
  have hp' : t.pc=pc := by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using hp
  exact ⟨t,hs.trans ht,hv.readOnly hp' hr h6 hm⟩

theorem finish {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pc+8#64) c_checkCode) (hp : CodeAt im (pc+52#64) c_postCode)
    (hu : Stage s A D (pc+8#64) n u) (hh : Answer A D n a u)
    (hz : zeroOkH (high heap) 4 a=true) :
    TBSim im sk u 16 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
  obtain ⟨v,hs,hv,hav⟩:=check F heap hheap hmem hc hu hh
  simp only [if_pos hz] at hv
  have he:=OuterNodeSearchExit.runC (sk:=sk) F hp hv hav
  have he' : TBSim im sk v 9 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using he
  exact TBSim.steps hs he'

theorem exhaust {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pc+8#64) c_checkCode) (hf : CodeAt im (pc+36#64) c_failureCode)
    (hl : CodeAt im (pc+48#64) c_lastCode) (hp : CodeAt im (pc+52#64) c_postCode)
    (hu : Stage s A D (pc+8#64) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH (high heap) 4 a=true) (hn : n+1=4096) :
    TBSim im sk u 20 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
  obtain ⟨v,hs,hv,hav⟩:=check F heap hheap hmem hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hpt,hm⟩:=OuterNodeCounterRun.runC (pc+36#64) hf v hv.at_pc n (by omega) hv.nonce
  have hpt' : t.pc=pc+48#64 := by
    simpa only [show ¬n+1<4096 by omega,if_false,BitVec.add_assoc,BitVec.reduceAdd] using hpt
  have htv:=hv.readOnly hpt' hr h6 hm
  have hat:=hav.readOnly hm
  obtain ⟨w,hw,hwpc,hwr,hw6,hwm⟩:=OuterNodeLastRun.run (pc+48#64) hl t hpt' n (by omega) h6
  have hwpc' : w.pc=pc+52#64 := by simpa only [BitVec.add_assoc,BitVec.reduceAdd] using hwpc
  have hwv:=htv.readOnly hwpc' (hwr.mono (by simp)) hw6 hwm
  have haw:=hat.readOnly hwm
  have he:=OuterNodeSearchExit.runC (sk:=sk) F hp hwv haw
  have he' : TBSim im sk w 9 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using he
  exact TBSim.steps (hs.trans (ht.trans hw)) he'

theorem loop {im : Image} {sk : BitVec 256} {A D : Nat} {pre right : List UInt8}
    {s : MachineState} {pc : Word} (F : Input A D pre right s)
    (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hq : CodeAt im pc c_preHashCode) (hc : CodeAt im (pc+8#64) c_checkCode)
    (hf : CodeAt im (pc+36#64) c_failureCode) (hl : CodeAt im (pc+48#64) c_lastCode)
    (hp : CodeAt im (pc+52#64) c_postCode) :
    ∀ fuel n u,Stage s A D pc n u → n+fuel+1=4096 →
      TBSim im sk u (19*fuel+29) (searchH (high heap) 4 pre right fuel n)
        (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
  refine OuterNodeLoopControl.loop_sim (high heap) 4 4096 7 pre right (Stage s A D pc)
    (fun n a u=>Stage s A D (pc+8#64) n u ∧ Answer A D n a u)
    (OuterNodeSearchExit.Out s A D (pc-20#64)) ?_ ?_ ?_ ?_
  · intro β n u hu hn W f Q hk
    exact trial F hq hu (by omega) (fun a t ht ha=>hk a t ⟨ht,ha⟩)
  · intro n a u hu hn hz
    exact finish F heap hheap hmem hc hp hu.1 hu.2 hz
  · intro n a u hu hz hn
    exact retry F heap hheap hmem hc hf hu.1 hu.2 hz hn
  · intro n a u hu hz hn
    exact exhaust F heap hheap hmem hc hf hl hp hu.1 hu.2 hz hn

#print axioms finish
#print axioms exhaust
#print axioms loop

#print axioms ok
#print axioms check
#print axioms retry
end OuterNodeSearchC
