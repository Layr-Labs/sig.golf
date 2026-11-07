import SigGolfCandidate.RvCore
import SigGolfCandidate.SimCore
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.DigestLabel
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def start (expand : Bool) : Nat := if expand then 83939 else 25688
def pcAddr (n : Nat) : Word := BitVec.ofNat 64 (4096 + 4*n)
def prefixWords : List (BitVec 32) := [0x18593,0x61b7,0x58018193,0x353823,0x58193,0x4000593]
def address : Addr := ⟨some (.reg .x10), 16⟩
def result (expand : Bool) : Result :=
  ⟨⟨RegFile.init.set .x11 (.c 64), [(address, .c 25984)], [.valid address 8]⟩,
    .c (pcAddr (start expand + 6)), .fuel, 6, 6⟩
theorem run_eq (expand : Bool) : symRun {} prefixWords (pcAddr (start expand)) 6 = some (result expand) := by
  cases expand <;> rfl

theorem registers (expand : Bool) (s : MachineState) (h11 : s.getReg .x11 = 64) (x : Reg) :
    ((result expand).toState s).getReg x = s.getReg x := by
  rw [Result.toState_getReg]
  cases x <;> first | rfl | exact h11.symm

theorem pc (expand : Bool) (s : MachineState) :
    ((result expand).toState s).pc = pcAddr (start expand + 6) := rfl

theorem memory (expand : Bool) (s : MachineState) (a : Word) :
    ((result expand).toState s).getMem a =
      if a = s.getReg .x10 + 16 then 25984 else s.getMem a := by
  rfl

theorem stored (expand : Bool) (s : MachineState) :
    ((result expand).toState s).getMem (s.getReg .x10 + 16) = 25984 := by
  rw [memory, if_pos rfl]

theorem post_regs (expand : Bool) (s : MachineState) (h11 : s.getReg .x11 = 64) :
    RegsExcept s ((result expand).toState s) [] := by
  intro r _
  exact registers expand s h11 r

theorem post_frame (expand : Bool) (s : MachineState) :
    Frame s ((result expand).toState s) (fun a => BitVec.ofNat 64 a = s.getReg .x10 + 16) := by
  intro a _ hn
  rw [memory, if_neg hn]

theorem post_frame_at (expand : Bool) (s : MachineState) (a : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 a) (ha : a + 16 < 2^64) :
    Frame s ((result expand).toState s) (fun b => b = a + 16) := by
  apply (post_frame expand s).mono
  intro b hb he
  rw [h10] at he
  have he' : BitVec.ofNat 64 b = BitVec.ofNat 64 (a + 16) := by
    simpa [BitVec.ofNat_add] using he
  have hn := congrArg BitVec.toNat he'
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha] using hn

theorem prefix_steps {im : Image} (expand : Bool) (s : MachineState)
    (hc : CodeAt im (pcAddr (start expand)) prefixWords) (hp : s.pc = pcAddr (start expand))
    (hv : accessValid (s.getReg .x10 + 16) 8 = true) :
    Steps im s 6 6 ((result expand).toState s) := by
  apply symRun_sound (run_eq expand) hc s hp
  apply (Oblig.all_iff s _).mpr
  intro o ho
  simp only [result, List.mem_singleton] at ho
  subst o
  exact hv
def hookPc (expand : Bool) : Nat := if expand then 45070 else 22614
def hookWord (expand : Bool) : BitVec 32 := if expand then 0x7552506f else 0x80306f
def backWord (expand : Bool) : BitVec 32 := if expand then 0x894da06f else 0xfe1fc06f
def jumpResult (pc : Nat) : Result := ⟨SymState.init, .c (pcAddr pc), .jump, 1, 1⟩
theorem hook_run (expand : Bool) :
    symRun {} [hookWord expand] (pcAddr (hookPc expand)) 1 = some (jumpResult (start expand)) := by
  cases expand <;> rfl
theorem back_run (expand : Bool) :
    symRun {} [backWord expand] (pcAddr (start expand + 7)) 1 = some (jumpResult (hookPc expand + 1)) := by
  cases expand <;> rfl

class Code (im : Image) (expand : Bool) : Prop where
  hook_at : CodeAt im (pcAddr (hookPc expand)) [hookWord expand]
  prefix_at : CodeAt im (pcAddr (start expand)) prefixWords
  hash_at : CodeAt im (pcAddr (start expand + 6)) [0x73]
  back_at : CodeAt im (pcAddr (start expand + 7)) [backWord expand]

theorem hook_steps {im : Image} (expand : Bool) [Code im expand] (s : MachineState)
    (hp : s.pc = pcAddr (hookPc expand)) : Steps im s 1 1 ((jumpResult (start expand)).toState s) := by
  apply symRun_sound (hook_run expand) (Code.hook_at (im := im) (expand := expand)) s hp
  apply (Oblig.all_iff s _).mpr
  intro o ho
  cases ho

theorem back_steps {im : Image} (expand : Bool) [Code im expand] (s : MachineState)
    (hp : s.pc = pcAddr (start expand + 7)) : Steps im s 1 1 ((jumpResult (hookPc expand + 1)).toState s) := by
  apply symRun_sound (back_run expand) (Code.back_at (im := im) (expand := expand)) s hp
  apply (Oblig.all_iff s _).mpr
  intro o ho
  cases ho

theorem jump_regs (pc : Nat) (s : MachineState) : RegsExcept s ((jumpResult pc).toState s) [] := by
  intro r _
  cases r <;> rfl

theorem jump_frame (pc : Nat) (s : MachineState) : Frame s ((jumpResult pc).toState s) (fun _ => False) := by
  intro a _ _
  rfl

theorem jump_pc (pc : Nat) (s : MachineState) : ((jumpResult pc).toState s).pc = pcAddr pc := rfl

def prepared (expand : Bool) (s : MachineState) : MachineState :=
  (result expand).toState ((jumpResult (start expand)).toState s)

theorem prepare_steps {im : Image} (expand : Bool) [Code im expand] (s : MachineState)
    (hp : s.pc = pcAddr (hookPc expand))
    (hv : accessValid (s.getReg .x10 + 16) 8 = true) :
    Steps im s 7 7 (prepared expand s) := by
  have hj := hook_steps (im := im) expand s hp
  have hs := prefix_steps expand ((jumpResult (start expand)).toState s)
    (Code.prefix_at (im := im) (expand := expand)) rfl hv
  exact hj.trans hs

theorem prepared_regs (expand : Bool) (s : MachineState) (h11 : s.getReg .x11 = 64) :
    RegsExcept s (prepared expand s) [] := by
  exact (jump_regs _ s).trans (post_regs expand _ h11)

theorem prepared_pc (expand : Bool) (s : MachineState) :
    (prepared expand s).pc = pcAddr (start expand + 6) := rfl

theorem prepared_stored (expand : Bool) (s : MachineState) :
    (prepared expand s).getMem (s.getReg .x10 + 16) = 25984 := by
  exact stored expand ((jumpResult (start expand)).toState s)

theorem prepared_frame_at (expand : Bool) (s : MachineState) (a : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 a) (ha : a + 16 < 2^64) :
    Frame s (prepared expand s) (fun b => b = a + 16) := by
  exact ((jump_frame _ s).trans (post_frame_at expand _ a h10 ha)).mono
    (fun _ _ h => h.elim False.elim id)

def returned (expand : Bool) (s : MachineState) (a : BitVec 256) : MachineState :=
  (jumpResult (hookPc expand + 1)).toState (writeHash s a)

@[simp] theorem returned_getReg (expand : Bool) (s : MachineState) (a : BitVec 256) (r : Reg) :
    (returned expand s a).getReg r = s.getReg r := by
  exact ((jump_regs _ (writeHash s a)).get (by simp)).trans (getReg_writeHash s a r)

@[simp] theorem returned_getMem (expand : Bool) (s : MachineState) (a : BitVec 256) (b : Word) :
    (returned expand s a).getMem b = (writeHash s a).getMem b := rfl

theorem returned_pc (expand : Bool) (s : MachineState) (a : BitVec 256) :
    (returned expand s a).pc = pcAddr (hookPc expand + 1) := rfl

theorem publicHash_return_bind {im : Image} (expand : Bool) [Code im expand]
    {sk : BitVec 256} {s : MachineState} {input : List UInt8} {W : Nat} {β : Type}
    {f : SigGolfCandidate.T3.HashOutput → SigGolfCandidate.T3.M β} {Q : β → MachineState → Prop}
    (hp : s.pc = pcAddr (start expand + 6))
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (SigGolfCandidate.T3.pad64 input))
    (h : ∀ a, TBSim im sk (returned expand s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (SigGolfCandidate.T3.pad64 input)).blocks + (1 + W))
      (SigGolfCandidate.T3.publicHash input >>= f) Q := by
  unfold TBSim
  rw [mrealize_bind, mrealize_publicHash]
  apply Sim.query_bind hf ht0 hv hq
  intro a
  have hpc : (writeHash s a).pc = pcAddr (start expand + 7) := by
    rw [pc_writeHash, hp]
    cases expand <;> rfl
  exact TBSim.steps (back_steps (im := im) expand (writeHash s a) hpc) (h a)

#print axioms publicHash_return_bind
#print axioms returned_getReg

#print axioms prepare_steps
#print axioms prepared_regs
#print axioms prepared_stored
#print axioms prepared_frame_at

#print axioms hook_run
#print axioms back_run
#print axioms hook_steps
#print axioms back_steps
#print axioms jump_regs
#print axioms jump_frame
#print axioms run_eq
#print axioms registers
#print axioms memory
#print axioms stored
#print axioms post_regs
#print axioms post_frame
#print axioms post_frame_at
#print axioms prefix_steps
end SigGolfCandidate.T3M.DigestLabel
