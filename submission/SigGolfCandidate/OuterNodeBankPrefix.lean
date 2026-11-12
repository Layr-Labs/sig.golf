import SigGolfCandidate.OuterNodeBankCall
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterNodeBankPrefix
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.FtsGrind

def resultBeq (a b : Result) : Bool :=
  SymState.beq a.st b.st && E.beq a.pc b.pc && decide (a.stop=b.stop) && a.steps==b.steps && a.cycles==b.cycles

theorem resultBeq_eq {a b : Result} (h : resultBeq a b=true) : a=b := by
  cases a with | mk ast apc astop astep acyc=>
    cases b with | mk bst bpc bstop bstep bcyc=>
      simp only [resultBeq,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
      obtain ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩:=h
      rw [SymState.beq_eq h1,E.beq_eq h2,h3,h4,h5]

def optResultBeq (o : Option Result) (r : Result) : Bool :=
  match o with | some a=>resultBeq a r | none=>false

theorem optResultBeq_eq {o : Option Result} {r : Result} (h : optResultBeq o r=true) : o=some r := by
  cases o with
  | none=>simp [optResultBeq] at h
  | some a=>simp only [optResultBeq] at h;rw [resultBeq_eq h]

def bSetup (j l : Nat) : List (BitVec 32) :=
  (W9Drv.SharedBProof.childWords j).drop (W9Drv.SharedBProof.ecIdx j l+1) |>.take (W9Drv.SharedBProof.lvlSt j l)
def bResult (j l : Nat) : Result :=
  let r:=W9Drv.SharedBProof.lvlRes j l
  ⟨r.st,.c r.pc,.endOfCode,r.steps,r.cycles⟩

theorem b_setup_computed : ∀ j : Fin 128,∀ l : Fin 6,
    optResultBeq (symRun cfg0 (bSetup j.val l.val)
      (pcOf (W9Drv.SharedBProof.childBase j.val+W9Drv.SharedBProof.ecIdx j.val l.val+1)) 40)
      (bResult j.val l.val)=true := by decide +kernel

theorem b_setup_runs (j : Fin 128) (l : Fin 6) :
    symRun cfg0 (bSetup j.val l.val) (pcOf (W9Drv.SharedBProof.childBase j.val+W9Drv.SharedBProof.ecIdx j.val l.val+1)) 40=
      some (bResult j.val l.val) := optResultBeq_eq (b_setup_computed j l)

theorem b_setup_slices : ∀ j : Fin 128,∀ l : Fin 6,
    ((OuterNodeBankLayout.bWords j.val).drop (W9Drv.SharedBProof.ecIdx j.val l.val+1)).take (bSetup j.val l.val).length=
      bSetup j.val l.val ∧ W9Drv.SharedBProof.ecIdx j.val l.val+1+(bSetup j.val l.val).length≤64 := by decide +kernel

theorem runB {im : Image} (j : Fin 128) (l : Fin 6)
    (hc : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j.val)) (OuterNodeBankLayout.bWords j.val))
    (s : MachineState) (hp : s.pc=pcOf (W9Drv.SharedBProof.childBase j.val+W9Drv.SharedBProof.ecIdx j.val l.val+1))
    (ho : ∀ o∈(W9Drv.SharedBProof.lvlRes j.val l.val).st.obl,o.holds s) :
    Steps im s (W9Drv.SharedBProof.lvlSt j.val l.val) (W9Drv.SharedBProof.lvlSt j.val l.val)
      ((W9Drv.SharedBProof.lvlRes j.val l.val).toState s) := by
  have hsl:=b_setup_slices j l
  have hlen:=(OuterNodeBankLayout.b_slices j).1
  have hcode:=codeAt_sub (seg:=bSetup j.val l.val) (W9Drv.SharedBProof.ecIdx j.val l.val+1) hc
    (by rw [hlen];exact hsl.2) hsl.1
  have h:=symRun_sound (b_setup_runs j l) hcode s (by simpa only [Nat.add_assoc] using hp)
    ((Oblig.all_iff s _).mpr ho)
  exact h

def cSetup (j l : Nat) : List (BitVec 32) :=
  (W9Drv.SharedCProof.childWords j).drop (W9Drv.SharedCProof.ecIdx j l+1) |>.take (W9Drv.SharedCProof.lvlSt j l)
def cResult (j l : Nat) : Result :=
  let r:=W9Drv.SharedCProof.lvlRes j l
  ⟨r.st,.c r.pc,.endOfCode,r.steps,r.cycles⟩

theorem c_setup_computed : ∀ j : Fin 128,∀ l : Fin 6,
    optResultBeq (symRun cfg0 (cSetup j.val l.val)
      (pcOf (W9Drv.SharedCProof.childBase j.val+W9Drv.SharedCProof.ecIdx j.val l.val+1)) 40)
      (cResult j.val l.val)=true := by decide +kernel

theorem c_setup_runs (j : Fin 128) (l : Fin 6) :
    symRun cfg0 (cSetup j.val l.val) (pcOf (W9Drv.SharedCProof.childBase j.val+W9Drv.SharedCProof.ecIdx j.val l.val+1)) 40=
      some (cResult j.val l.val) := optResultBeq_eq (c_setup_computed j l)

theorem c_setup_slices : ∀ j : Fin 128,∀ l : Fin 6,
    ((OuterNodeBankLayout.cWords j.val).drop (W9Drv.SharedCProof.ecIdx j.val l.val+1)).take (cSetup j.val l.val).length=
      cSetup j.val l.val ∧ W9Drv.SharedCProof.ecIdx j.val l.val+1+(cSetup j.val l.val).length≤64 := by decide +kernel

theorem runC {im : Image} (j : Fin 128) (l : Fin 6)
    (hc : CodeAt im (pcOf (W9Drv.SharedCProof.childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    (s : MachineState) (hp : s.pc=pcOf (W9Drv.SharedCProof.childBase j.val+W9Drv.SharedCProof.ecIdx j.val l.val+1))
    (ho : ∀ o∈(W9Drv.SharedCProof.lvlRes j.val l.val).st.obl,o.holds s) :
    Steps im s (W9Drv.SharedCProof.lvlSt j.val l.val) (W9Drv.SharedCProof.lvlSt j.val l.val)
      ((W9Drv.SharedCProof.lvlRes j.val l.val).toState s) := by
  have hsl:=c_setup_slices j l
  have hlen:=(OuterNodeBankLayout.c_slices j).1
  have hcode:=codeAt_sub (seg:=cSetup j.val l.val) (W9Drv.SharedCProof.ecIdx j.val l.val+1) hc
    (by rw [hlen];exact hsl.2) hsl.1
  have h:=symRun_sound (c_setup_runs j l) hcode s (by simpa only [Nat.add_assoc] using hp)
    ((Oblig.all_iff s _).mpr ho)
  exact h

#print axioms runC
#print axioms c_setup_runs
#print axioms b_setup_runs
#print axioms b_setup_slices
#print axioms runB
end OuterNodeBankPrefix
