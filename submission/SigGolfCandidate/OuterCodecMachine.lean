import SigGolfCandidate.SimCore
import SigGolfCandidate.OuterTailPacket
set_option debug.skipKernelTC false
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCodecMachine
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def packCode : List (BitVec 32) := [0x7e37,0x83b7,0x4403d303,0x19fe4383,0x737e93,0x5e9e93,0x1d3e3b3,0x187e0fa3,0x335313,0x32fe4383,0x737e93,0x5e9e93,0x1d3e3b3,0x327e07a3,0x335313,0x4bfe4383,0x737e93,0x5e9e93,0x1d3e3b3,0x4a7e0fa3,0x335313,0x64fe4383,0x737e93,0x5e9e93,0x1d3e3b3,0x647e07a3,0x335313,0x71fe4383,0xf37e93,0x4e9e93,0x1d3e3b3,0x707e0fa3,0x435313]
sym_block packBlock := symRun {noAlias:=true} packCode (pcOf 26207) 50
theorem pack_counts : packBlock.res.steps=33 ∧ packBlock.res.cycles=33 := by decide +kernel
#print axioms pack_counts
def unpackCode : List (BitVec 32) := [0x7e37,0x313,0x19fe4383,0x53de93,0xe9e93,0x1d36333,0x1f3f393,0x187e0fa3,0x32fe4383,0x53de93,0x3e9e93,0x1d36333,0x1f3f393,0x327e07a3,0x4bfe4383,0x53de93,0x6e9e93,0x1d36333,0x1f3f393,0x4a7e0fa3,0x64fe4383,0x53de93,0x9e9e93,0x1d36333,0x1f3f393,0x647e07a3,0x71fe4383,0x43de93,0xce9e93,0x1d36333,0xf3f393,0x707e0fa3,0x83b7,0x44639023,0x313,0x393,0xe13,0xe93]
sym_block unpackBlock := symRun {noAlias:=true} unpackCode (pcOf 88300) 50
theorem unpack_counts : unpackBlock.res.steps=38 ∧ unpackBlock.res.cycles=38 := by decide +kernel
#print axioms unpack_counts
theorem pack_obligs (s : MachineState) : packBlock.res.obligs s := by
  simp [packBlock.res,Result.obligs,Oblig.all]

theorem unpack_obligs (s : MachineState) : unpackBlock.res.obligs s := by
  simp [unpackBlock.res,Result.obligs,Oblig.all]

theorem pack_run {im : Image} (hc : CodeAt im (pcOf 26207) packCode) (s : MachineState)
    (hp : s.pc=pcOf 26207) :
    ∃ t,Steps im s 33 33 t ∧ t.pc=pcOf 26240 ∧ RegsExcept s t [.x6,.x7,.x28,.x29] := by
  refine ⟨packBlock.res.toState s,symRun_sound packBlock hc s hp (pack_obligs s),rfl,?_⟩
  intro r hr
  cases r <;> simp at hr <;> rfl

#print axioms pack_obligs
#print axioms unpack_obligs
#print axioms pack_run
end OuterCodecMachine
