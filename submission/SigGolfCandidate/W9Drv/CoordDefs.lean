import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.W9Machine.WctChildContract

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchPc (n : Nat) : Nat := [246,370,498,626,753,881,1009,1136,1263,1391].getD n 1391
def cachedWord (n : Nat) : Nat := [0,0,1,1,1,2,2,2,2,2].getD n 2
def pairBase : Nat := 0xffbe10
structure CoordPre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (n : Nat)
    (pairs : List (Digest × Digest)) (u : MachineState) : Prop where
  le : n ≤ 9
  length : pairs.length = n
  pc : u.pc = pcOf (dispatchPc n)
  glob : Glob baseK w pk u
  digest : DigestAt a u
  bank : HeaderBank u
  forest : ForestData u
  index : u.getReg .x22 = BitVec.ofNat 64 (idxOf a)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  stepOne : u.getReg .x7 = 1
  stepTwo : u.getReg .x13 = 2
  hashLen : u.getReg .x11 = 64
  coordStep : u.getReg .x6 = 65536
  nodeReg : u.getReg .x15 = BitVec.ofNat 64 (idxOf a * 2^27 + 1537 + 65536 * (n-1))
  cached3 : u.getReg .x17 = a.extractLsb' 192 64
  cached : u.getReg .x16 = a.extractLsb' (64 * cachedWord n) 64
  mask : u.getReg .x2 = BitVec.ofNat 64 0xfffc
  jt : u.getReg .x24 = BitVec.ofNat 64 0xd6800
  childBlock : u.getReg .x29 = BitVec.ofNat 64 0xce800
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (9152 - 880 * (n-1))
  pairPtr : u.getReg .x9 = BitVec.ofNat 64 (pairBase + 32 * (n-1))
  pairs : ∀ i, i < n → DigAt u (pairBase + 32*i) (pairs.getD i (0,0)).1 ∧
    DigAt u (pairBase + 32*i + 16) (pairs.getD i (0,0)).2
  coords : ∀ k : Fin 9, n ≤ k.val → ∀ off, off < 880 → off % 8 = 0 →
    W9Machine.OrigW w u (coordinateBase k + off)
  layer : Orig w (fun o => o < 64 ∨ (8000 ≤ o ∧ o < 21472)) u
end W9Drv
