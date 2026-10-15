import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.W9Machine.WctChildContract
import SigGolfCandidate.W9Machine.WctNestView

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchPc (n : Nat) : Nat := [89, 171, 257, 342, 426, 512, 596, 680, 765, 849].getD n 849
def cachedWord (n : Nat) : Nat := [0,0,1,1,1,2,2,2,2,2].getD n 2
def pairBase : Nat := 0xffbe10
/-- Nested FTS: coordinate 0's pads are the witness slots of region 0 (honest 0). -/
def ftsStartW (w : ClaudeWCT.W9.T3M.WBytes) : Digest × Digest := (V3.leafPad w 0, V3.nodePad w 0 0 5)
/-- The previous coordinate's top pair (coordinate 0: the witness pads). -/
def prevOf (w : ClaudeWCT.W9.T3M.WBytes) (pairs : List (Digest × Digest)) : Digest × Digest :=
  pairs.getLastD (ftsStartW w)
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
  cached3 : u.getReg .x17 = if n < 8 then a.extractLsb' 192 64 else a.extractLsb' 192 64 ||| rankPad
  cached : u.getReg .x16 = a.extractLsb' (64 * cachedWord n) 64 ||| rankPad
  mask : u.getReg .x2 = BitVec.ofNat 64 0xfff00
  childMask : n ≥ 3 → u.getReg .x27 = BitVec.ofNat 64 0x7f00000
  jt : u.getReg .x24 = rankPad
  childBlock : u.getReg .x29 = BitVec.ofNat 64 0xf1b00
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (8560 - 896 * (n-1))
  pairPtr : u.getReg .x9 = BitVec.ofNat 64 TOPB9
  prevL : DigAt u (regionAddr n + 720) (prevOf w pairs).1
  prevR : DigAt u (regionAddr n + 864) (prevOf w pairs).2
  a2 : 0 < n → u.getReg .x12 = BitVec.ofNat 64 (regionAddr n + 704) ∨
    u.getReg .x12 = BitVec.ofNat 64 (regionAddr n + 848)
  coords : ∀ m, n ≤ m → m ≤ 9 → ∀ off, off < 896 → off % 8 = 0 → (m = 9 → 720 ≤ off) →
    (m = n → ¬ V3.isHand off) → W9Machine.OrigW w u (regionAddr m + off)
  layer : Orig w (fun o => (32 ≤ o ∧ o < 48) ∨ (8256 ≤ o ∧ o < 24832)) u
end W9Drv

namespace W9Drv.SharedCoord
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)

def rankPad : Word := 0x1801801800000
def dispatchPc (n : Nat) : Nat := [89,171,257,341,425,511,595,679,765,853].getD n 853

def prevOf (w : ClaudeWCT.W9.T3M.WBytes) (pairs : List (Digest × Digest)) : Digest × Digest :=
  pairs.getLastD (SharedV3.initialPair w)

def isHand (n off : Nat) : Prop :=
  if n = 9 then (720 ≤ off ∧ off < 752) ∨ (768 ≤ off ∧ off < 800)
  else SharedV3.isHand off
instance (n off : Nat) : Decidable (isHand n off) := by unfold isHand; infer_instance

structure Pre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (n : Nat)
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
  cached3 : u.getReg .x17 = if n < 8 then a.extractLsb' 192 64 else a.extractLsb' 192 64 ||| rankPad
  cached : u.getReg .x16 = a.extractLsb' (64 * cachedWord n) 64 ||| rankPad
  mask : u.getReg .x2 = BitVec.ofNat 64 0xfff00
  childMask : u.getReg .x27 = BitVec.ofNat 64 0x7f00000
  aTable : u.getReg .x28 = BitVec.ofNat 64 0xe3300
  jt : u.getReg .x24 = rankPad
  childBlock : u.getReg .x29 = BitVec.ofNat 64 0xf1b00
  singletonTable : u.getMem (BitVec.ofNat 64 (TOPB9 - 240)) = BitVec.ofNat 64 0xe7400
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (8560 - 896 * (n-1))
  pairPtr : u.getReg .x9 = BitVec.ofNat 64 TOPB9
  prevL : DigAt u (regionAddr n + 720) (prevOf w pairs).1
  prevR : DigAt u (regionAddr n + SharedV3.handR n) (prevOf w pairs).2
  a2 : 0 < n → u.getReg .x12 = BitVec.ofNat 64 (regionAddr n + (if n = 9 then 720 else 704)) ∨
    u.getReg .x12 = BitVec.ofNat 64 (regionAddr n + (if n = 9 then 768 else 144))
  coords : ∀ m, n ≤ m → m ≤ 9 → ∀ off, off < 896 → off % 8 = 0 → (m = 9 → 720 ≤ off) →
    (m = n → ¬ isHand n off) → W9Machine.OrigW w u (regionAddr m + off)
  layer : Orig w (fun o => (32 ≤ o ∧ o < 48) ∨ (8256 ≤ o ∧ o < 24832)) u
  /-- Coordinate-8 dispatch hoist: coordinate 7's dispatcher ends with `srli tp,a7,17` (word 689, after its
  `or a7,a7,s8`), and no chain or B′ child routine of coordinate 7 writes `tp` or `a7`, so coordinate 8's dispatcher
  finds its shared shift `a7 >>> 17` already in `tp`. -/
  hoist : n = 8 → u.getReg .x4 = u.getReg .x17 >>> 17
end W9Drv.SharedCoord
