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
namespace OuterNodeSearchB
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterNodeMachineBlocks

theorem ok (a : HashOutput) : zeroOkH true 3 a=true ↔ (a.extractLsb' 192 64 >>> 61)=0 := by
  have h:=OuterNodeHashZero.upper_word_iff (a.extractLsb' 128 128) 3 (by decide)
  rw [OuterNodeHashZero.high_word] at h
  simpa [zeroOkH,halfOf,Nat.div_eq_zero_iff] using h.symm

theorem check {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pc+8#64) b_checkCode) (hu : Stage s A D (pc+8#64) n u)
    (hh : Answer A D n a u) :
    ∃ t,Steps im u 3 3 t ∧
      Stage s A D (if zeroOkH true 3 a then pc+36#64 else pc+20#64) n t ∧ Answer A D n a t := by
  have gx : u.getReg .x12=BitVec.ofNat 64 D := by rw [hu.regs.get (by decide)];exact F.x12
  obtain ⟨t,hs,hr,hp,hm⟩:=OuterNodeCheckRun.runB (pc+8#64) hc u hu.at_pc D gx F.dhi F.dlo F.da
  have ho : u.getMem (u.getReg .x12+24#64)=a.extractLsb' 192 64 := by
    rw [gx,ofNat_add_ofNat];exact hh.output 3 (by decide)
  rw [ho] at hp
  simp only [←ok] at hp
  have hp' : t.pc=(if zeroOkH true 3 a then pc+36#64 else pc+20#64) := by
    simpa only [BitVec.add_assoc,BitVec.reduceAdd] using hp
  refine ⟨t,hs,hu.readOnly hp' (hr.mono (by simp)) ?_ hm,hh.readOnly hm⟩
  rw [hr.get (by decide)];exact hu.nonce

theorem retry {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pc+8#64) b_checkCode) (hf : CodeAt im (pc+20#64) b_failureCode)
    (hu : Stage s A D (pc+8#64) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH true 3 a=true) (hn : n+1<2048) :
    ∃ t,Steps im u 6 6 t ∧ Stage s A D pc (n+1) t := by
  obtain ⟨v,hs,hv,hav⟩:=check F hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hp,hm⟩:=OuterNodeCounterRun.runB (pc+20#64) hf v hv.at_pc n (by omega) hv.nonce
  rw [if_pos hn] at hp
  have hp' : t.pc=pc := by simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using hp
  exact ⟨t,hs.trans ht,hv.readOnly hp' hr h6 hm⟩

theorem finish {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pc+8#64) b_checkCode) (hp : CodeAt im (pc+36#64) b_postCode)
    (hu : Stage s A D (pc+8#64) n u) (hh : Answer A D n a u)
    (hz : zeroOkH true 3 a=true) :
    TBSim im sk u 12 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
  obtain ⟨v,hs,hv,hav⟩:=check F hc hu hh
  simp only [if_pos hz] at hv
  have he:=OuterNodeSearchExit.runB (sk:=sk) F hp hv hav
  have he' : TBSim im sk v 9 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using he
  exact TBSim.steps hs he'

theorem exhaust {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pc+8#64) b_checkCode) (hf : CodeAt im (pc+20#64) b_failureCode)
    (hl : CodeAt im (pc+32#64) b_lastCode) (hp : CodeAt im (pc+36#64) b_postCode)
    (hu : Stage s A D (pc+8#64) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH true 3 a=true) (hn : n+1=2048) :
    TBSim im sk u 16 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
  obtain ⟨v,hs,hv,hav⟩:=check F hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hpt,hm⟩:=OuterNodeCounterRun.runB (pc+20#64) hf v hv.at_pc n (by omega) hv.nonce
  have hpt' : t.pc=pc+32#64 := by
    simpa only [show ¬n+1<2048 by omega,if_false,BitVec.add_assoc,BitVec.reduceAdd] using hpt
  have htv:=hv.readOnly hpt' hr h6 hm
  have hat:=hav.readOnly hm
  obtain ⟨w,hw,hwpc,hwr,hw6,hwm⟩:=OuterNodeLastRun.run (pc+32#64) hl t hpt' n (by omega) h6
  have hwpc' : w.pc=pc+36#64 := by simpa only [BitVec.add_assoc,BitVec.reduceAdd] using hwpc
  have hwv:=htv.readOnly hwpc' (hwr.mono (by simp)) hw6 hwm
  have haw:=hat.readOnly hwm
  have he:=OuterNodeSearchExit.runB (sk:=sk) F hp hwv haw
  have he' : TBSim im sk w 9 (pure (n,a)) (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using he
  exact TBSim.steps (hs.trans (ht.trans hw)) he'

theorem loop {im : Image} {sk : BitVec 256} {A D : Nat} {pre right : List UInt8}
    {s : MachineState} {pc : Word} (F : Input A D pre right s)
    (hq : CodeAt im pc b_preHashCode) (hc : CodeAt im (pc+8#64) b_checkCode)
    (hf : CodeAt im (pc+20#64) b_failureCode) (hl : CodeAt im (pc+32#64) b_lastCode)
    (hp : CodeAt im (pc+36#64) b_postCode) :
    ∀ fuel n u,Stage s A D pc n u → n+fuel+1=2048 →
      TBSim im sk u (15*fuel+25) (searchH true 3 pre right fuel n)
        (OuterNodeSearchExit.Out s A D (pc-20#64)) := by
  refine OuterNodeLoopControl.loop_sim true 3 2048 3 pre right (Stage s A D pc)
    (fun n a u=>Stage s A D (pc+8#64) n u ∧ Answer A D n a u)
    (OuterNodeSearchExit.Out s A D (pc-20#64)) ?_ ?_ ?_ ?_
  · intro β n u hu hn W f Q hk
    exact trial F hq hu (by omega) (fun a t ht ha=>hk a t ⟨ht,ha⟩)
  · intro n a u hu hn hz
    exact finish F hc hp hu.1 hu.2 hz
  · intro n a u hu hz hn
    exact retry F hc hf hu.1 hu.2 hz hn
  · intro n a u hu hz hn
    exact exhaust F hc hf hl hp hu.1 hu.2 hz hn

#print axioms finish
#print axioms exhaust
#print axioms loop

#print axioms ok
#print axioms check
#print axioms retry
end OuterNodeSearchB
