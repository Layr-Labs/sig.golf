import SigGolfCandidate.SimCore
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNoncePostMachine
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def postCode : List (BitVec 32) := [0x7f03b7,0x3b303,0x33b7,0xb463b823,0x7f23b7,0x3b303,0x23b7,0x4a63b823,0x7f43b7,0x3b303,0x23b7,0xe063b823,0x7f63b7,0x3b303,0x13b7,0x7663b823,0x7f73b7,0x3b303,0x13b7,0x4263b023]
sym_block postBlock := symRun {noAlias:=true} postCode (pcOf 88260) 30
theorem counts : postBlock.res.steps=20 ∧ postBlock.res.cycles=20 := by decide +kernel
theorem obligs (s : MachineState) : postBlock.res.obligs s := by
  simp [postBlock.res,Result.obligs,Oblig.all]
def destinations : List Word := [11088,9392,7696,6000,5152]
theorem frame (s : MachineState) (a : Word) (ha : a∉destinations) :
    (postBlock.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [postBlock.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  all_goals
    intro he
    apply ha
    simp only [Addr.eval,E.eval] at he
    subst a
    decide
theorem nonce0 (s : MachineState) : (postBlock.res.toState s).getMem 11088=s.getMem 8323072 := by
  simp [Result.toState_getMem,postBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval]
theorem nonce1 (s : MachineState) : (postBlock.res.toState s).getMem 9392=s.getMem 8331264 := by
  simp [Result.toState_getMem,postBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval]
theorem nonce2 (s : MachineState) : (postBlock.res.toState s).getMem 7696=s.getMem 8339456 := by
  simp [Result.toState_getMem,postBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval]
theorem nonce3 (s : MachineState) : (postBlock.res.toState s).getMem 6000=s.getMem 8347648 := by
  simp [Result.toState_getMem,postBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval]
theorem nonce4 (s : MachineState) : (postBlock.res.toState s).getMem 5152=s.getMem 8351744 := by
  simp [Result.toState_getMem,postBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval]
theorem run {im : Image} (hc : CodeAt im (pcOf 88260) postCode) (s : MachineState) (hp : s.pc=pcOf 88260) :
    ∃ t,Steps im s 20 20 t ∧ t.pc=pcOf 88280 ∧ RegsExcept s t [.x6,.x7] ∧
      t.getMem 11088=s.getMem 8323072 ∧ t.getMem 9392=s.getMem 8331264 ∧
      t.getMem 7696=s.getMem 8339456 ∧ t.getMem 6000=s.getMem 8347648 ∧ t.getMem 5152=s.getMem 8351744 ∧
      ∀ a,a∉destinations→t.getMem a=s.getMem a := by
  refine ⟨postBlock.res.toState s,symRun_sound postBlock hc s hp (obligs s),rfl,?_,
    nonce0 s,nonce1 s,nonce2 s,nonce3 s,nonce4 s,frame s⟩
  intro r hr
  cases r <;> simp at hr <;> rfl
#print axioms counts
#print axioms run
end OuterNoncePostMachine
