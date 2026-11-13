import SigGolfCandidate.MachineCounterCaps
import SigGolfCandidate.Route16Guard
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace SigGolfCandidate.Route16Machine
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M

def guardCode : List (BitVec 32) := Route16Guard.words ++ [0x66f37,0x18f3f03,0x815e806f]
sym_block guardBlock := symRun {noAlias:=true} guardCode (pcOf 26008) 20

theorem guard_steps {im : Image} (hc : CodeAt im (pcOf 26008) guardCode)
    (s : MachineState) (hp : s.pc=pcOf 26008) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66018=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 1959 ∧
      t.getReg .x29=BitVec.ofNat 64 (Route16Guard.floor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let t := guardBlock.res.toState s
  refine ⟨t,symRun_sound guardBlock hc s hp (by simp [guardBlock.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · simpa [t,guardBlock.res,rv_simp,Route16Guard.guardWord,h18,BitVec.xor_comm,
      BitVec.add_comm] using Route16Guard.guard_checked ⟨leaf,hl⟩
  · simpa [t,guardBlock.res,rv_simp] using hm
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl

def expandCode : List (BitVec 32) := Route16Guard.words ++ [0x66f37,0x40f3f03,0x810df06f]
sym_block expandBlock := symRun {noAlias:=true} expandCode (pcOf 88095) 20

theorem expand_steps {im : Image} (hc : CodeAt im (pcOf 88095) expandCode)
    (s : MachineState) (hp : s.pc=pcOf 88095) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66040=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 54317 ∧
      t.getReg .x29=BitVec.ofNat 64 (Route16Guard.floor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let t := expandBlock.res.toState s
  refine ⟨t,symRun_sound expandBlock hc s hp (by simp [expandBlock.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · simpa [t,expandBlock.res,rv_simp,Route16Guard.guardWord,h18,BitVec.xor_comm,
      BitVec.add_comm] using Route16Guard.guard_checked ⟨leaf,hl⟩
  · simpa [t,expandBlock.res,rv_simp] using hm
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl


#print axioms expand_steps
#print axioms guard_steps
end SigGolfCandidate.Route16Machine
