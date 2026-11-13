import SigGolfCandidate.SimCore
import SigGolfCandidate.OuterTailPacket
set_option debug.skipKernelTC false
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCodecMachine
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def packCode : List (BitVec 32) := [0x7e37,0x83b7,0x19fe4303,0x32fe4e83,0x3e9e93,0x1d36333,0x4bfe4e83,0x6e9e93,0x1d36333,0x64fe4e83,0x9e9e93,0x1d36333,0x71fe4e83,0xce9e93,0x1d36333,0x4403de83,0x10e9e93,0x1d36333,0x186e0fa3,0x835313,0x326e07a3,0x835313,0x4a6e0fa3,0x835313,0x646e07a3,0x43f3ce83,0x71de0fa3,0x42038fa3,0x13,0x13,0x13,0x13,0x13]
sym_block packBlock := symRun {noAlias:=true} packCode (pcOf 26207) 50
theorem pack_counts : packBlock.res.steps=33 ∧ packBlock.res.cycles=33 := by decide +kernel
#print axioms pack_counts
def unpackCode : List (BitVec 32) := [0x7e37,0x19fe4303,0x32fe4e83,0x8e9e93,0x1d36333,0x4bfe4e83,0x10e9e93,0x1d36333,0x64fe4e83,0x18e9e93,0x1d36333,0x83b7,0x71fe4e83,0x43d38fa3,0x737e93,0x19de0fa3,0x335313,0x737e93,0x33de07a3,0x335313,0x737e93,0x4bde0fa3,0x335313,0x737e93,0x65de07a3,0x335313,0xf37e93,0x71de0fa3,0x435313,0x44639023,0x313,0x393,0xe13,0xe93,0x13,0x13,0x13,0x13]
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
