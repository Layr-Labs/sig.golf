import SigGolfCandidate.T3M.Verify.Mem

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
abbrev idxOf (a : HashOutput) : Nat := ClaudeWCT.WCT9.digestIndex a
def DigestAt (a : HashOutput) (u : MachineState) : Prop :=
  ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (8 * k)) = a.extractLsb' (64 * k) 64
def dataBase7 : Nat := 0xffbde0
structure HeaderBank (u : MachineState) : Prop where
  top : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
    BitVec.ofNat 64 (topWords.getD k 0)
  top8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21200
structure SetupMask (u : MachineState) : Prop where
  child : u.getMem (BitVec.ofNat 64 (dataBase7 + 368)) = BitVec.ofNat 64 0xce800
  jt : u.getMem (BitVec.ofNat 64 (dataBase7 + 376)) = BitVec.ofNat 64 0xd6800
  coord : u.getMem (BitVec.ofNat 64 (dataBase7 + 464)) = BitVec.ofNat 64 8640
  gate : u.getMem (BitVec.ofNat 64 (dataBase7 + 352)) = BitVec.ofNat 64 0x1524000000000000
  d0 : u.getMem (BitVec.ofNat 64 dataBase7) = BitVec.ofNat 64 0xfff
structure ForestData (u : MachineState) : Prop where
  zero0 : u.getMem (BitVec.ofNat 64 (dataBase7 + 16)) = 0
  zero1 : u.getMem (BitVec.ofNat 64 (dataBase7 + 24)) = 0
  header : u.getMem (BitVec.ofNat 64 (dataBase7 + 32)) = BitVec.ofNat 64 0xf01
structure GatePre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 4
  glob : Glob [(.x5, 0)] w pk u
  len64 : u.getReg .x11 = 64
  forest : ForestData u
  digest : DigestAt a u
  bank : HeaderBank u
  wit : Orig w (fun o => o ≠ 20896) u
  setupMask : SetupMask u
  sp : u.getReg .x2 = BitVec.ofNat 64 dataBase7
end W9Drv
