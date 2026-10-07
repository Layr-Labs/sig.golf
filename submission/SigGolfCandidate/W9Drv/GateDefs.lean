import SigGolfCandidate.T3M.Verify.Mem

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
abbrev idxOf (a : HashOutput) : Nat := ClaudeWCT.WCT9.digestIndex a
def DigestAt (a : HashOutput) (u : MachineState) : Prop :=
  ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (8 * k)) = a.extractLsb' (64 * k) 64
structure HeaderBank (u : MachineState) : Prop where
  node : u.getMem (BitVec.ofNat 64 (0xffbf40 + 8)) =
    BitVec.ofNat 64 (1 + 3 * 256 + 4 * 65536)
  top : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
    BitVec.ofNat 64 (topWords.getD k 0)
  top8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 22152
  forest : ∀ j, j < 3 → u.getMem (BitVec.ofNat 64 (0xffbdf0 + 8 * j)) =
    BitVec.ofNat 64 (if j = 2 then 3841 else 0)
def setupMaskAddr : Nat := 0xffbf40
structure SetupMask (u : MachineState) : Prop where
  child : u.getMem (BitVec.ofNat 64 (setupMaskAddr + 16)) = BitVec.ofNat 64 0xce800
  jt : u.getMem (BitVec.ofNat 64 (setupMaskAddr + 24)) = BitVec.ofNat 64 0xd6800
structure GatePre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 32781
  glob : Glob baseK w pk u
  cached0 : u.getReg .x16 = a.extractLsb' 0 64
  len64 : u.getReg .x11 = 64
  zero : u.getMem (BitVec.ofNat 64 1024) = 0 ∧ u.getMem (BitVec.ofNat 64 1032) = 0
  digest : DigestAt a u
  bank : HeaderBank u
  wit : WitAll w u
  setupMask : SetupMask u
  sp : u.getReg .x2 = BitVec.ofNat 64 0xffbde0
end W9Drv
