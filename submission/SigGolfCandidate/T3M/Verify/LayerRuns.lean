import SigGolfCandidate.T3M.Verify.Spec

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def xtrTab : List (List Nat) :=[[1061,2085,3109,4133,5157,6181,7205,8229,9253,10277,11301,12325,13349,14373,15397,16421,17445,18469,19493,20517,21541,22565,23589,24613,25637,26661,27685,28709,29733,30757,31781,32805,33829,34853,35877,36901,37925,38949,39973,40997,42021,43045,44069,45093,46117,47141,48165,49189,50213,51237,52261,53285,54309,55333,56357,57381,58405,59429,60453,61477,62501,63525,64549,65573,66597,67621,68645,69669,70693,71717,72741,73765,74789,75813,76837,77861,78885,79909,80933,81957,82981,84005,85029,86053,87077,88101,89125,90149,91173,92197,93221,94245,95269,96293,97317,98341,99365,100389,101413,102437,103461,104485,105509,106533,107557,108581,109605,110629,111653,112677,113701,114725,115749,116773,117797,118821,119845,120869,121893,122917,123941,124965,125989,127013,128037,129061,130085,131109],[141983,142111,142239,142367,142495,142623,142751,142879,143007,143135,143263,143391,143519,143647,143775,143903,144031,144159,144287,144415,144543,144671,144799,144927,145055,145183,145311,145439,145567,145695,145823,145951,146079,146207,146335,146463,146591,146719,146847,146975,147103,147231,147359,147487,147615,147743,147871,147999,148127,148255,148383,148511,148639,148767,148895,149023,149151,149279,149407,149535,149663,149791,149919,150047],[133791,133919,134047,134175,134303,134431,134559,134687,134815,134943,135071,135199,135327,135455,135583,135711,135839,135967,136095,136223,136351,136479,136607,136735,136863,136991,137119,137247,137375,137503,137631,137759,137887,138015,138143,138271,138399,138527,138655,138783,138911,139039,139167,139295,139423,139551,139679,139807,139935,140063,140191,140319,140447,140575,140703,140831,140959,141087,141215,141343,141471,141599,141727,141855],[851]]
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def hL (lay : Nat) : Nat := [12,7,6,6].getD lay 0
def stepsA (lay : Nat) : Nat := if lay = 0 then 8 else if lay = 3 then 10 else 7
def retOff (lay : Nat) : Nat := if lay = 0 then 11 else if lay = 3 then 42 else 41
def s6v (lay : Nat) : Nat := [11920,15104,18176,21248].getD lay 0
def s3v : Nat := 11920
def tgtL (lay : Nat) : Nat := [144,201,202,202].getD lay 0
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
def rejEcall : Nat := 3431
def stabIdx (lay : Nat) : Nat := [209768,209640,209576,209512].getD lay 0
def stabMask (lay : Nat) : Nat := if lay = 1 then 508 else 252
def s7Bias (lay : Nat) : Nat := [4096,2,1117,1053].getD lay 0
def stabW (lay sh : Nat) : Nat :=
  if lay = 0 then 142032 + 128 * sh else if lay = 1 then 1024 + 1024 * sh else if lay = 2 then 141952 + 128 * sh else 133760 + 128 * sh
def M1c : Nat := 8198552921648689607
def M2c : Nat := 17311559823019733055
def M4c : Nat := 3689348814741910323
def M8c : Nat := 1085102592571150095
def mkBase (lay : Nat) : Nat := [8256,12496,15616,18688].getD lay 0
def planL1 : List (List Nat) :=[[1,4,7,10,13,16,19],[0,4,7,10,13,16,19],[4,0,7,10,13,16,19],[3,0,7,10,13,16,19],[4,7,0,10,13,16,19],[3,7,0,10,13,16,19],[7,3,0,10,13,16,19],[6,3,0,10,13,16,19],[4,7,10,0,13,16,19],[3,7,10,0,13,16,19],[7,3,10,0,13,16,19],[6,3,10,0,13,16,19],[7,10,3,0,13,16,19],[6,10,3,0,13,16,19],[10,6,3,0,13,16,19],[9,6,3,0,13,16,19],[4,7,10,13,0,16,19],[3,7,10,13,0,16,19],[7,3,10,13,0,16,19],[6,3,10,13,0,16,19],[7,10,3,13,0,16,19],[6,10,3,13,0,16,19],[10,6,3,13,0,16,19],[9,6,3,13,0,16,19],[7,10,13,3,0,16,19],[6,10,13,3,0,16,19],[10,6,13,3,0,16,19],[9,6,13,3,0,16,19],[10,13,6,3,0,16,19],[9,13,6,3,0,16,19],[13,9,6,3,0,16,19],[12,9,6,3,0,16,19],[4,7,10,13,16,0,19],[3,7,10,13,16,0,19],[7,3,10,13,16,0,19],[6,3,10,13,16,0,19],[7,10,3,13,16,0,19],[6,10,3,13,16,0,19],[10,6,3,13,16,0,19],[9,6,3,13,16,0,19],[7,10,13,3,16,0,19],[6,10,13,3,16,0,19],[10,6,13,3,16,0,19],[9,6,13,3,16,0,19],[10,13,6,3,16,0,19],[9,13,6,3,16,0,19],[13,9,6,3,16,0,19],[12,9,6,3,16,0,19],[7,10,13,16,3,0,19],[6,10,13,16,3,0,19],[10,6,13,16,3,0,19],[9,6,13,16,3,0,19],[10,13,6,16,3,0,19],[9,13,6,16,3,0,19],[13,9,6,16,3,0,19],[12,9,6,16,3,0,19],[10,13,16,6,3,0,19],[9,13,16,6,3,0,19],[13,9,16,6,3,0,19],[12,9,16,6,3,0,19],[13,16,9,6,3,0,19],[12,16,9,6,3,0,19],[16,12,9,6,3,0,19],[15,12,9,6,3,0,19],[4,7,10,13,16,19,0],[3,7,10,13,16,19,0],[7,3,10,13,16,19,0],[6,3,10,13,16,19,0],[7,10,3,13,16,19,0],[6,10,3,13,16,19,0],[10,6,3,13,16,19,0],[9,6,3,13,16,19,0],[7,10,13,3,16,19,0],[6,10,13,3,16,19,0],[10,6,13,3,16,19,0],[9,6,13,3,16,19,0],[10,13,6,3,16,19,0],[9,13,6,3,16,19,0],[13,9,6,3,16,19,0],[12,9,6,3,16,19,0],[7,10,13,16,3,19,0],[6,10,13,16,3,19,0],[10,6,13,16,3,19,0],[9,6,13,16,3,19,0],[10,13,6,16,3,19,0],[9,13,6,16,3,19,0],[13,9,6,16,3,19,0],[12,9,6,16,3,19,0],[10,13,16,6,3,19,0],[9,13,16,6,3,19,0],[13,9,16,6,3,19,0],[12,9,16,6,3,19,0],[13,16,9,6,3,19,0],[12,16,9,6,3,19,0],[16,12,9,6,3,19,0],[15,12,9,6,3,19,0],[7,10,13,16,19,3,0],[6,10,13,16,19,3,0],[10,6,13,16,19,3,0],[9,6,13,16,19,3,0],[10,13,6,16,19,3,0],[9,13,6,16,19,3,0],[13,9,6,16,19,3,0],[12,9,6,16,19,3,0],[10,13,16,6,19,3,0],[9,13,16,6,19,3,0],[13,9,16,6,19,3,0],[12,9,16,6,19,3,0],[13,16,9,6,19,3,0],[12,16,9,6,19,3,0],[16,12,9,6,19,3,0],[15,12,9,6,19,3,0],[10,13,16,19,6,3,0],[9,13,16,19,6,3,0],[13,9,16,19,6,3,0],[12,9,16,19,6,3,0],[13,16,9,19,6,3,0],[12,16,9,19,6,3,0],[16,12,9,19,6,3,0],[15,12,9,19,6,3,0],[13,16,19,9,6,3,0],[12,16,19,9,6,3,0],[16,12,19,9,6,3,0],[15,12,19,9,6,3,0],[16,19,12,9,6,3,0],[15,19,12,9,6,3,0],[19,15,12,9,6,3,0],[18,15,12,9,6,3,0]]
def planL32 : List (List Nat) :=[[1,4,7,10,13,16],[0,4,7,10,13,16],[4,0,7,10,13,16],[3,0,7,10,13,16],[4,7,0,10,13,16],[3,7,0,10,13,16],[7,3,0,10,13,16],[6,3,0,10,13,16],[4,7,10,0,13,16],[3,7,10,0,13,16],[7,3,10,0,13,16],[6,3,10,0,13,16],[7,10,3,0,13,16],[6,10,3,0,13,16],[10,6,3,0,13,16],[9,6,3,0,13,16],[4,7,10,13,0,16],[3,7,10,13,0,16],[7,3,10,13,0,16],[6,3,10,13,0,16],[7,10,3,13,0,16],[6,10,3,13,0,16],[10,6,3,13,0,16],[9,6,3,13,0,16],[7,10,13,3,0,16],[6,10,13,3,0,16],[10,6,13,3,0,16],[9,6,13,3,0,16],[10,13,6,3,0,16],[9,13,6,3,0,16],[13,9,6,3,0,16],[12,9,6,3,0,16],[4,7,10,13,16,0],[3,7,10,13,16,0],[7,3,10,13,16,0],[6,3,10,13,16,0],[7,10,3,13,16,0],[6,10,3,13,16,0],[10,6,3,13,16,0],[9,6,3,13,16,0],[7,10,13,3,16,0],[6,10,13,3,16,0],[10,6,13,3,16,0],[9,6,13,3,16,0],[10,13,6,3,16,0],[9,13,6,3,16,0],[13,9,6,3,16,0],[12,9,6,3,16,0],[7,10,13,16,3,0],[6,10,13,16,3,0],[10,6,13,16,3,0],[9,6,13,16,3,0],[10,13,6,16,3,0],[9,13,6,16,3,0],[13,9,6,16,3,0],[12,9,6,16,3,0],[10,13,16,6,3,0],[9,13,16,6,3,0],[13,9,16,6,3,0],[12,9,16,6,3,0],[13,16,9,6,3,0],[12,16,9,6,3,0],[16,12,9,6,3,0],[15,12,9,6,3,0]]
def plan (lay r j : Nat) : Nat := ((if lay = 1 then planL1 else planL32).getD r []).getD j 0
def rowA (lay c : Nat) : Nat := 0x4c0 + mkBase (lay + 1) + 16 * plan (lay + 1) c (hL (lay + 1) - 1)
/-- Campaign S1: write address of the encoding answer of layer `lay` (= the root-window input node of layer `lay + 1`,
16 below its slot when it is a left node). -/
def rowWa (lay c : Nat) : Nat := rowA lay c + 64 * (c / 2 ^ (hL (lay + 1) - 1) % 2) - 16
/-- Destination of the encoding answer of layer `lay`: for the L3 block (campaign S2) the `a2` left by coordinate 8's
child routine (`WIT - 16` when tree 8's top node is heap 2, `WIT + 128` for heap 3); else `rowWa`. -/
def EncDst (lay c d : Nat) : Prop := if lay = 3 then d = 1200 ∨ d = 1344 else d = rowWa lay c
def bufferBias (lay : Nat) : Nat := [24672,23680,22944,22208].getD lay 0
def bufferBase (lay : Nat) : Nat := [25184,24448,23712,22976].getD lay 0
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then [(.x5, 0)] ++ [(.x8, BitVec.ofNat 64 1392), (.x11, 64), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7),
    (.x9, BitVec.ofNat 64 TOPB9), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)]
  else baseK ++ [(.x6, 0x10000), (.x2, 0x7fc00),
    (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x5, 0), (.x9, BitVec.ofNat 64 TOPB9), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias (lay+1)))] ++
    (if lay = 0 then [(.x8, BitVec.ofNat 64 s3v)] else [])
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x9, BitVec.ofNat 64 TOPB9)] ++
    (if lay = 3 then [] else [(.x2, if lay=0 then 0x7fc80 else 0x7fc00), (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x5, 0), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias lay))]) ++
    (if lay = 0 then [(.x8, BitVec.ofNat 64 s3v)] else [])
def chainK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x2, 0x7fc00),
    (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x5, 0), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias lay))]
def bK (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, 1216)] ++
  (if lay = 1 ∨ lay = 2 then [(.x22, BitVec.ofNat 64 (s6v lay))] else [])
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x31
def leafE (lay : Nat) : E := if lay = 0 then .reg .x31 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := if lay = 0 then .bin .sll (leafE lay) (kw 32) else .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def dispatchHeap (lay leaf : Nat) : Nat := if lay = 0 then 16 * (s7Bias lay + leaf) else s7Bias lay + leaf
def s7E (lay : Nat) : E := if lay = 0 then .bin .or (.bin .sll (leafE lay) (kw 4)) (kw (16 * 2 ^ hL lay)) else .bin .add (leafE lay) (kw (s7Bias lay))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x4d0 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay, kw 0x400000, d⟩
def setupPc (_lay p : Nat) : Nat := p
def setupAcceptDir (lay : Nat) : Bool := decide (lay = 3)
def hdrA (lay : Nat) : Nat := if lay = 3 then TOPLOAD + 32 else HDATA + 8 * lay
def t3E3 : E := .bin .or (.ld (kw (hdrA 3))) (.bin .sll (.reg .x22) (kw 16))
/-- L3 encoding block at 851 (campaign S2, nested FTS): `ld gp,-32(s0); ld a4,-24(s0); sd gp,-128(s0); sd a4,-120(s0)`
(R copy from the virtual Z slot `WIT + 144` to the block's right slot `WIT + 48`), `slli gp,s6,16; ld t3,120(s1);
or t3,t3,gp; sd t3,-160(s0); addi a0,s0,-176; ld s2,-304(s1); ecall`: only the low tweak word (1232) is written, 1240
(`wbcHigh`) stays witness; `a2` is the coordinate-8 child's (kept); `s2` is loaded from data word 0 (`0xFFF`). -/
def x18E3 : E := .ld (kw (TOPB9 - 304))
def l3Writes : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 1232⟩, t3E3), (⟨none, BitVec.ofNat 64 1272⟩, .ld (kw 1368)),
   (⟨none, BitVec.ofNat 64 1264⟩, .ld (kw 1360))]
def specA (lay p : Nat) : Spec :=
  ⟨if lay = 3 then [(.x28, t3E3), (.x18, x18E3)] else [(.x23, s7E lay), (.x31, treeE lay), (.x28, t3E3)],
   l3Writes,
   p + stepsA lay, true, stepsA lay, [], none, stepsA lay⟩
def rejA (lay _p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   l3Writes,
   28822, true, 33, [ctrBr lay (!setupAcceptDir lay)], none, 33⟩
def a6E : E := .ld (.reg .x12)
def a7E : E := .ld (.bin .add (.reg .x12) (kw 8))
def b1E : E := .bin .sll a7E (kw 1)
def M1E (lay : Nat) : E := if lay = 3 then .ld (kw (TOPLOAD + 8)) else kw M1c
def M2E (lay : Nat) : E := if lay = 3 then .ld (kw TOPLOAD) else kw M2c
def maskE (lay : Nat) : E := if lay = 3 then .ld (kw (TOPLOAD + 24)) else kw 0x7fc00
def sw1RefE : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl a7E (kw 3)) (kw M1c))) (.bin .and a7E (kw M1c))
def swLowE (lay : Nat) : E := .bin .add (.bin .and a6E (M1E lay)) (.bin .and a7E (M1E lay))
def sw1E (lay : Nat) : E := .bin .add (swLowE lay) (.bin .srl (.bin .sub (.bin .add a6E a7E) (swLowE lay)) (kw 3))
def sumE (lay : Nat) : E := .bin .remu (.bin .and (.bin .add (sw1E lay) (.bin .srl (sw1E lay) (kw 6))) (M2E lay)) (kw 4095)
def t4E (lay : Nat) : E := .bin .add (sumE lay) (kw (2 ^ 64 - (tgtL lay - 7)))
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.ltu, kw 7, t4E lay, d⟩
def spareBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .lt else .ge, .bin .and a6E a7E, kw 0, if lay = 3 then !d else d⟩
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
def x14l (lay : Nat) : E := .bin .and (.bin .sll a6E (kw 10)) (maskE lay)
def tgtl (lay : Nat) : E := .bin .and (.bin .add (x14l lay) (kw 1992)) (.c (~~~1#64))
def a6HiE : E := .ld (.bin .add (.reg .x12) (kw 16))
def a7HiE : E := .ld (.bin .add (.reg .x12) (kw 24))
def b1HiE : E := .bin .sll a7HiE (kw 1)
def swLowHiE (lay : Nat) : E := .bin .add (.bin .and a6HiE (M1E lay)) (.bin .and a7HiE (M1E lay))
def sw1HiE (lay : Nat) : E := .bin .add (swLowHiE lay) (.bin .srl (.bin .sub (.bin .add a6HiE a7HiE) (swLowHiE lay)) (kw 3))
def sumHiE (lay : Nat) : E := .bin .remu (.bin .and (.bin .add (sw1HiE lay) (.bin .srl (sw1HiE lay) (kw 6))) (M2E lay)) (kw 4095)
def t4HiE (lay : Nat) : E := .bin .add (sumHiE lay) (kw (2 ^ 64 - (tgtL lay - 7)))
def rngHiBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7HiE (kw k), kw 0, d⟩
def ckHiBr (lay : Nat) (d : Bool) : Br := ⟨.ltu, kw 7, t4HiE lay, d⟩
def spareHiBr (_lay : Nat) (d : Bool) : Br := ⟨.lt, .bin .and a6HiE a7HiE, kw 0, !d⟩
def a7HiL : E := .bin .or b1HiE (.bin .srl a6HiE (kw 63))
def x14Hi (lay : Nat) : E := .bin .and (.bin .sll a6HiE (kw 10)) (maskE lay)
def tgtHi (lay : Nat) : E := .bin .and (.bin .add (x14Hi lay) (kw 1992)) (.c (~~~1#64))
def bSt (lay : Nat) : Nat := if lay = 3 then 30 else if lay = 1 ∨ lay = 2 then 21 else 33
def bCy (lay : Nat) : Nat := if lay = 3 then 33 else if lay = 1 ∨ lay = 2 then 24 else 36
def prefixReturn (lay p : Nat) : Nat := p + (if lay = 3 then 37 else 38)
def s7Sh (lay : Nat) : Nat := if lay = 1 then 12 else 9
def s23E (lay : Nat) : E := if lay = 3 then .bin .sll (s7E 3) (kw 9) else .bin .sll (.reg .x23) (kw (s7Sh lay))
def specBl (lay _p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7E), (.x23, s23E lay), (.x25, sumE lay), (.x29, t4E lay),
    (.x14, x14l lay)] ++ (if lay = 3 then [(.x22, .ld (kw (TOPLOAD - 8))),
      (.x24, .ld (kw TOPLOAD)), (.x1, .ld (kw (TOPLOAD + 8))), (.x2, .ld (kw (TOPLOAD + 24))),
      (.x31, treeE 3), (.x27, .bin .srl (maskE 3) (kw 1)), (.x4, .ld (kw (TOPB9+56)))] else []),
   [], 0, false, bSt lay, [ckBr lay false, spareBr lay false], some (tgtl lay), bCy lay⟩
def specBlHi (lay _p : Nat) : Spec :=
  ⟨[(.x16, a6HiE), (.x17, a7HiE), (.x23, s23E lay), (.x25, sumHiE lay), (.x29, t4HiE lay),
    (.x14, x14Hi lay)] ++ (if lay = 3 then [(.x22, .ld (kw (TOPLOAD - 8))),
      (.x24, .ld (kw TOPLOAD)), (.x1, .ld (kw (TOPLOAD + 8))), (.x2, .ld (kw (TOPLOAD + 24))),
      (.x31, treeE 3), (.x27, .bin .srl (maskE 3) (kw 1)), (.x4, .ld (kw (TOPB9+56)))] else []),
   [], 0, false, bSt lay + 4, [ckHiBr lay false, spareHiBr lay false, spareBr lay true], some (tgtHi lay), bCy lay + 4⟩
def postBl (lay _p : Nat) : List (Reg × Word) :=
  chainK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x7, 1), (.x9, BitVec.ofNat 64 TOPB9)]
def postBlC (lay p : Nat) : List (Reg × Word) :=
  if lay = 3 then ((chainK lay).filter (fun q => q.1 != .x24 && q.1 != .x1 && q.1 != .x2 && q.1 != .x27 && q.1 != .x4)) ++ [(.x7, 1), (.x9, BitVec.ofNat 64 TOPB9)] else postBl lay p
def rejSpare (lay : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [spareBr lay true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, if lay = 3 then 23 else 20, [ckBr lay true, spareBr lay false], none, if lay = 3 then 26 else 23⟩
def rejCkHi (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, (if lay = 3 then 23 else 20)+4,
    [ckHiBr lay true, spareHiBr lay false, spareBr lay true], none, (if lay = 3 then 26 else 23)+4⟩
def spareTrap (lay c : Nat) : Nat := ([[],[142017,142145,142273,142401,142529,142657,142785,142913,143041,143169,143297,143425,143553,143681,143809,143937,144065,144193,144326,144449,144577,144705,144833,144961,145089,145217,145345,145473,145601,145729,145857,145985,146113,146241,146369,146497,146625,146753,146881,147009,147140,147265,147393,147521,147649,147777,147905,148033,148161,148289,148417,148545,148673,148801,148929,149057,149185,149313,149441,149569,149697,149825,149954,150081],[133825,133953,134081,134209,134337,134465,134593,134721,134849,134977,135105,135233,135361,135489,135617,135745,135873,136001,136129,136257,136385,136518,136641,136769,136897,137025,137153,137281,137409,137537,137665,137793,137921,138049,138177,138305,138433,138564,138689,138817,138945,139073,139201,139329,139457,139585,139713,139841,139969,140097,140225,140353,140481,140609,140737,140865,140993,141121,141249,141378,141505,141633,141761,141889],[870],[]].getD lay []).getD c 0
def rejBothSpare (lay c : Nat) : Spec :=
  ⟨[], [], spareTrap lay c, false, 8, [spareHiBr lay true, spareBr lay true], none, 8⟩
def lfAllowed (lay : Nat) : List Nat := [bufferBase lay+16]
def leafK (lay : Nat) : List (Reg × Word) :=
  baseK ++ (if lay = 0 then [(.x5, 0), (.x6, 520192)] else [(.x7, 1), (.x5, 0)]) ++ [(.x4,BitVec.ofNat 64 (bufferBias lay))]
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .sll (.bin .add (.bin .and (.reg .x31) (kw 63)) (kw 1117)) (kw 9)
  else if lay = 1 then .bin .sll (.reg .x23) (kw 12)
  else .bin .sll (.reg .x23) (kw 9)
def tgtLf (lay : Nat) : E := if lay = 0 then .bin .and (addC (x14lf lay) 320) (.c (~~~1#64)) else .bin .and (.reg .x23) (.c (~~~1#64))
def lfDirs (_lay : Nat) : List Dir := [.jmp]
def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)], [(⟨none, BitVec.ofNat 64 (bufferBase lay+16)⟩, .reg .x28)], 0, false, 7, [], some (tgtLf lay), 7⟩
  else
    ⟨[], [(⟨none, BitVec.ofNat 64 (bufferBase lay+16)⟩, .reg .x28)], 0, false, 4, [],
      some (tgtLf lay), 4⟩
def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ [(.x10, BitVec.ofNat 64 (bufferBase lay)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704))]
def keepA : List Reg := []
def keepB (lay : Nat) : List Reg := if lay = 3 then [.x28] else [.x28, .x31]
def keepLf : List Reg := [.x23, .x31, .x22]
end SigGolfCandidate.T3M
