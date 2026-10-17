import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Fetch
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.WitV5
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodecC
import SigGolfCandidate.T3M.Expand.LayersBlocks
import SigGolfCandidate.T3M.Search.DigestSearch

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
def PLAN : Nat := 0xff9a00
def PlanAt (t : MachineState) : Prop :=
  ∀ k < 128, t.getMem (BitVec.ofNat 64 (PLAN + 8 * k)) = bytesToWordLE ((planBytes.drop (8 * k)).take 8)
def zeroBlk : List (BitVec 32) := [28343,0x9a0eb823,0x9a0ebc23,0x9c0eb023,0x9c0eb423,2451,0xce4d606f]
def ExpandDataOK (im : Image) : Prop :=
  im.data = lplanBytes ++ planBytes ++ expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData
end ClaudeWCT.W9.Machine.Expand
