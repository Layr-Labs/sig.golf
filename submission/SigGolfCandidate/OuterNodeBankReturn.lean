import SigGolfCandidate.OuterNodeBankPrefix
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeBankReturn
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind

def bCode : List (BitVec 32) := [0x13008067]
def cCode : List (BitVec 32) := [0x13c08067]
sym_block b_ret := symRun {noAlias:=true} bCode 0 40
sym_block c_ret := symRun {noAlias:=true} cCode 0 40

theorem b_at (pc : Word) : symRun {noAlias:=true} bCode pc 40=some b_ret.res := by rfl
theorem c_at (pc : Word) : symRun {noAlias:=true} cCode pc 40=some c_ret.res := by rfl

theorem b_slices : ∀ j : Fin 128,
    ((OuterNodeBankLayout.bWords j.val).drop (OuterNodeBankLayout.bSite j.val+1)).take 1=bCode ∧
      OuterNodeBankLayout.bSite j.val+2≤64 := by decide +kernel

theorem c_slices : ∀ j : Fin 128,
    ((OuterNodeBankLayout.cWords j.val).drop (OuterNodeBankLayout.cSite j.val+1)).take 1=cCode ∧
      OuterNodeBankLayout.cSite j.val+2≤64 := by decide +kernel

theorem runB {im : Image} (j : Fin 128)
    (hc : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j.val)) (OuterNodeBankLayout.bWords j.val))
    (s : MachineState) (hp : s.pc=pcOf (W9Drv.SharedBProof.childBase j.val+OuterNodeBankLayout.bSite j.val+1)) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=(s.getReg .x1+304#64) &&& ~~~1#64 ∧
      (∀ r,t.getReg r=s.getReg r) ∧ (∀ a,t.getMem a=s.getMem a) := by
  have hs:=b_slices j
  have hlen:=(OuterNodeBankLayout.b_slices j).1
  have hcode:=codeAt_sub (seg:=bCode) (OuterNodeBankLayout.bSite j.val+1) hc
    (by rw [hlen];exact hs.2) hs.1
  refine ⟨b_ret.res.toState s,symRun_sound (b_at _) hcode s (by simpa only [Nat.add_assoc] using hp) ?_,rfl,?_,?_⟩
  · simp [Result.obligs,b_ret.res,Oblig.all]
  · intro r
    rw [Result.toState_getReg]
    cases r <;> rfl
  · intro a
    rw [Result.toState_getMem]
    rfl

theorem runC {im : Image} (j : Fin 128)
    (hc : CodeAt im (pcOf (W9Drv.SharedCProof.childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    (s : MachineState) (hp : s.pc=pcOf (W9Drv.SharedCProof.childBase j.val+OuterNodeBankLayout.cSite j.val+1)) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=(s.getReg .x1+316#64) &&& ~~~1#64 ∧
      (∀ r,t.getReg r=s.getReg r) ∧ (∀ a,t.getMem a=s.getMem a) := by
  have hs:=c_slices j
  have hlen:=(OuterNodeBankLayout.c_slices j).1
  have hcode:=codeAt_sub (seg:=cCode) (OuterNodeBankLayout.cSite j.val+1) hc
    (by rw [hlen];exact hs.2) hs.1
  refine ⟨c_ret.res.toState s,symRun_sound (c_at _) hcode s (by simpa only [Nat.add_assoc] using hp) ?_,rfl,?_,?_⟩
  · simp [Result.obligs,c_ret.res,Oblig.all]
  · intro r
    rw [Result.toState_getReg]
    cases r <;> rfl
  · intro a
    rw [Result.toState_getMem]
    rfl

#print axioms runB
#print axioms runC
end OuterNodeBankReturn
