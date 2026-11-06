import SigGolfCandidate.SimCore
set_option linter.all false

namespace SigGolfCandidate.T3M.CacheMaskMachine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def hook (signing : Bool) : Nat := if signing then 1456 else 309
def stub (signing : Bool) : Nat := if signing then 21934 else 1024
def jumpWord (signing : Bool) : BitVec 32 := if signing then 0x7fd1306f else 0x3310006f
def returnZeroWord (signing : Bool) : BitVec 32 := if signing then 0xff9eb06f else 0xcc4ff06f
def zeroWords (signing : Bool) : List (BitVec 32) :=
  [0x63023, 0x63423, 0x63823, 0x63c23, returnZeroWord signing]

structure Code (image : Image) (signing : Bool) : Prop where
  jump : CodeAt image (pcOf (hook signing)) [jumpWord signing]
  zero : CodeAt image (pcOf (stub signing + 1)) (zeroWords signing)

def jumpResult (signing : Bool) : Result :=
  ⟨SymState.init, .c (pcOf (stub signing + 1)), .jump, 1, 1⟩

theorem jump_run (signing : Bool) :
    symRun {} [jumpWord signing] (pcOf (hook signing)) 1 = some (jumpResult signing) := by
  cases signing <;> kernel_rfl

sym_block kgZero := symRun {} (zeroWords false) (pcOf 1025) 8
sym_block sgZero := symRun {} (zeroWords true) (pcOf 21935) 8

variable {image : Image} {signing : Bool} (code : Code image signing)
include code

theorem jump_steps (s : MachineState) (hp : s.pc = pcOf (hook signing)) :
    Steps image s 1 1 { s with pc := pcOf (stub signing + 1) } := by
  have h := symRun_sound (jump_run signing) code.jump s hp
    (by simp [Result.obligs, jumpResult, SymState.init, Oblig.all])
  convert h using 1 <;> try rfl
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl

theorem zero_steps (s : MachineState) (hp : s.pc = pcOf (stub signing + 1))
    (h12 : s.getReg .x12 = 131168) :
    Steps image s 5 5 { writeHash s 0 with pc := pcOf (hook signing + 1) } := by
  cases signing
  · have hs := symRun_sound kgZero code.zero s hp (by
      simp [kgZero.res, Result.obligs, Oblig.all, Oblig.holds, E.eval, Addr.eval, h12]
      decide +kernel)
    convert hs using 1 <;> try rfl
    apply MachineState.ext' <;> try rfl
    · funext r; cases r <;> simp [kgZero.res, Result.toState, SymState.toState, SymState.init,
        RegFile.init, RegFile.get, writeHash] <;> rfl
    · funext a
      simp [kgZero.res, Result.toState, SymState.toState, memEval, Addr.eval, E.eval,
        writeHash, MachineState.writeWords, MachineState.setMem, MachineState.getMem,
        MachineState.setPC, h12]
  · have hs := symRun_sound sgZero code.zero s hp (by
      simp [sgZero.res, Result.obligs, Oblig.all, Oblig.holds, E.eval, Addr.eval, h12]
      decide +kernel)
    convert hs using 1 <;> try rfl
    apply MachineState.ext' <;> try rfl
    · funext r; cases r <;> simp [sgZero.res, Result.toState, SymState.toState, SymState.init,
        RegFile.init, RegFile.get, writeHash] <;> rfl
    · funext a
      simp [sgZero.res, Result.toState, SymState.toState, memEval, Addr.eval, E.eval,
        writeHash, MachineState.writeWords, MachineState.setMem, MachineState.getMem,
        MachineState.setPC, h12]

theorem runner : MaskSelectRunner image (hook signing) where
  zero s hp h12 := by
    have hj := jump_steps code s hp
    have hs := zero_steps code { s with pc := pcOf (stub signing + 1) } rfl h12
    have he : { writeHash { s with pc := pcOf (stub signing + 1) } 0 with
        pc := pcOf (hook signing + 1) } = writeHash s 0 := by
      apply MachineState.ext' <;> try rfl
      simp only [pc_writeHash, hp]
      exact (pcOf_add4 (hook signing)).symm
    rw [he] at hs
    exact hj.trans hs

end SigGolfCandidate.T3M.CacheMaskMachine
