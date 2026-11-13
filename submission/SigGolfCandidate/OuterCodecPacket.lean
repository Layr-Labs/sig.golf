import SigGolfCandidate.OuterCodecValues
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterCodecPacket
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterCodecValues OuterTailPacket

def readCarriers (s : MachineState) : Four := ⟨extractByte (s.getMem 29080) 7,extractByte (s.getMem 29480) 7,
  extractByte (s.getMem 29880) 7,extractByte (s.getMem 30280) 7⟩
end OuterCodecPacket
