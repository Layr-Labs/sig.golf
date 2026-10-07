import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.W9Machine.WctChildContract

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchPc (n : Nat) : Nat := [32836,32848,32863,32878,32892,32907,32922,32936,32950,32965].getD n 32965
def cachedWord (n : Nat) : Nat := [0,0,1,1,1,2,2,2,2,2].getD n 2
structure CoordPre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (n : Nat)
    (pairs : List (Digest × Digest)) (u : MachineState) : Prop where
  le : n ≤ 9
  length : pairs.length = n
  pc : u.pc = pcOf (dispatchPc n)
  glob : Glob baseK w pk u
  digest : DigestAt a u
  bank : HeaderBank u
  index : u.getReg .x22 = BitVec.ofNat 64 (idxOf a)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  stepOne : u.getReg .x7 = 1
  stepTwo : u.getReg .x13 = 2
  hashLen : u.getReg .x11 = 64
  coordStep : u.getReg .x6 = 65536
  prefixReg : u.getReg .x15 = BitVec.ofNat 64 (idxOf a * 2^27 + 65536 * (n-1) + 644)
  cached3 : u.getReg .x17 = a.extractLsb' 192 64
  cached : u.getReg .x16 = a.extractLsb' (64 * cachedWord n) 64
  nodeReg : n ≠ 0 → u.getReg .x27 = BitVec.ofNat 64 (V3.nodeLow (n-1) (idxOf a))
  nodeZero : n = 0 → u.getReg .x27 = BitVec.ofNat 64 (1 + 3 * 256 + 4 * 65536)
  zero : u.getMem (BitVec.ofNat 64 1024) = 0 ∧ u.getMem (BitVec.ofNat 64 1032) = 0
  mask : u.getReg .x2 = BitVec.ofNat 64 (if n = 0 then 0xffbde0 else 0xfffc)
  forestPointer : u.getReg .x9 = BitVec.ofNat 64 (0xffbdf0 + 32 + 32 * (n-1))
  jt : u.getReg .x24 = BitVec.ofNat 64 0xd6800
  childBlock : u.getReg .x29 = BitVec.ofNat 64 0xce800
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (2112 + 896 * (n-1))
  headerZero : n = 0 → u.getReg .x28 = BitVec.ofNat 64 (idxOf a * 2^32)
  headerReg : n ≠ 0 → u.getReg .x28 = BitVec.ofNat 64 (1537 + 65536 * (n-1))
  pairs : ∀ i, i < n → DigAt u (0xffbe10 + 32*i) (pairs.getD i (0,0)).1 ∧
    DigAt u (0xffbe10 + 32*i + 16) (pairs.getD i (0,0)).2
  coords : ∀ k : Fin 9, n ≤ k.val → ∀ off, off < 896 → off % 8 = 0 →
    W9Machine.OrigW w u (coordinateBase k + off)
  layer : Orig w (fun o => o < 64 ∨ 8136 ≤ o) u
end W9Drv
