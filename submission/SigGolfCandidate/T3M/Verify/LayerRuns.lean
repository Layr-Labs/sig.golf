import SigGolfCandidate.T3M.Verify.Spec

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def xtrTab : List (List Nat) :=[[1064,2088,3112,4136,5160,6184,7208,8232,9256,10280,11304,12328,13352,14376,15400,16424,17448,18472,19496,20520,21544,22568,23592,24616,25640,26664,27688,28712,29736,30760,31784,32808,33832,34856,35880,36904,37928,38952,39976,41000,42024,43048,44072,45096,46120,47144,48168,49192,50216,51240,52264,53288,54312,55336,56360,57384,58408,59432,60456,61480,62504,63528,64552,65576,66600,67624,68648,69672,70696,71720,72744,73768,74792,75816,76840,77864,78888,79912,80936,81960,82984,84008,85032,86056,87080,88104,89128,90152,91176,92200,93224,94248,95272,96296,97320,98344,99368,100392,101416,102440,103464,104488,105512,106536,107560,108584,109608,110632,111656,112680,113704,114728,115752,116776,117800,118824,119848,120872,121896,122920,123944,124968,125992,127016,128040,129064,130088,131112],[141986,142114,142242,142370,142498,142626,142754,142882,143010,143138,143266,143394,143522,143650,143778,143906,144034,144162,144290,144418,144546,144674,144802,144930,145058,145186,145314,145442,145570,145698,145826,145954,146082,146210,146338,146466,146594,146722,146850,146978,147106,147234,147362,147490,147618,147746,147874,148002,148130,148258,148386,148514,148642,148770,148898,149026,149154,149282,149410,149538,149666,149794,149922,150050],[133794,133922,134050,134178,134306,134434,134562,134690,134818,134946,135074,135202,135330,135458,135586,135714,135842,135970,136098,136226,136354,136482,136610,136738,136866,136994,137122,137250,137378,137506,137634,137762,137890,138018,138146,138274,138402,138530,138658,138786,138914,139042,139170,139298,139426,139554,139682,139810,139938,140066,140194,140322,140450,140578,140706,140834,140962,141090,141218,141346,141474,141602,141730,141858],[855]]
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def hL (lay : Nat) : Nat := [12,7,6,6].getD lay 0
def stepsA (lay : Nat) : Nat := if lay = 3 then 7 else 8
def retOff (lay : Nat) : Nat := if lay = 0 then 10 else if lay = 3 then 42 else 41
def s6v (lay : Nat) : Nat := [11904,15088,18144,21200].getD lay 0
def s3v : Nat := 11904
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
def mkBase (lay : Nat) : Nat := [7424,11648,14768,17824].getD lay 0
def planL1 : List (List Nat) :=[[0,2,4,6,8,10,12],[19,0,2,4,6,8,10],[0,19,2,4,6,8,10],[19,16,0,2,4,6,8],[0,2,19,4,6,8,10],[19,0,16,2,4,6,8],[0,19,16,2,4,6,8],[19,16,13,0,2,4,6],[0,2,4,19,6,8,10],[19,0,2,16,4,6,8],[0,19,2,16,4,6,8],[19,16,0,13,2,4,6],[0,2,19,16,4,6,8],[19,0,16,13,2,4,6],[0,19,16,13,2,4,6],[19,16,13,10,0,2,4],[0,2,4,6,19,8,10],[19,0,2,4,16,6,8],[0,19,2,4,16,6,8],[19,16,0,2,13,4,6],[0,2,19,4,16,6,8],[19,0,16,2,13,4,6],[0,19,16,2,13,4,6],[19,16,13,0,10,2,4],[0,2,4,19,16,6,8],[19,0,2,16,13,4,6],[0,19,2,16,13,4,6],[19,16,0,13,10,2,4],[0,2,19,16,13,4,6],[19,0,16,13,10,2,4],[0,19,16,13,10,2,4],[19,16,13,10,7,0,2],[0,2,4,6,8,19,10],[19,0,2,4,6,16,8],[0,19,2,4,6,16,8],[19,16,0,2,4,13,6],[0,2,19,4,6,16,8],[19,0,16,2,4,13,6],[0,19,16,2,4,13,6],[19,16,13,0,2,10,4],[0,2,4,19,6,16,8],[19,0,2,16,4,13,6],[0,19,2,16,4,13,6],[19,16,0,13,2,10,4],[0,2,19,16,4,13,6],[19,0,16,13,2,10,4],[0,19,16,13,2,10,4],[19,16,13,10,0,7,2],[0,2,4,6,19,16,8],[19,0,2,4,16,13,6],[0,19,2,4,16,13,6],[19,16,0,2,13,10,4],[0,2,19,4,16,13,6],[19,0,16,2,13,10,4],[0,19,16,2,13,10,4],[19,16,13,0,10,7,2],[0,2,4,19,16,13,6],[19,0,2,16,13,10,4],[0,19,2,16,13,10,4],[19,16,0,13,10,7,2],[0,2,19,16,13,10,4],[19,0,16,13,10,7,2],[0,19,16,13,10,7,2],[19,16,13,10,7,4,0],[0,2,4,6,8,10,14],[19,0,2,4,6,8,16],[0,19,2,4,6,8,16],[19,16,0,2,4,6,13],[0,2,19,4,6,8,16],[19,0,16,2,4,6,13],[0,19,16,2,4,6,13],[19,16,13,0,2,4,10],[0,2,4,19,6,8,16],[19,0,2,16,4,6,13],[0,19,2,16,4,6,13],[19,16,0,13,2,4,10],[0,2,19,16,4,6,13],[19,0,16,13,2,4,10],[0,19,16,13,2,4,10],[19,16,13,10,0,2,7],[0,2,4,6,19,8,16],[19,0,2,4,16,6,13],[0,19,2,4,16,6,13],[19,16,0,2,13,4,10],[0,2,19,4,16,6,13],[19,0,16,2,13,4,10],[0,19,16,2,13,4,10],[19,16,13,0,10,2,7],[0,2,4,19,16,6,13],[19,0,2,16,13,4,10],[0,19,2,16,13,4,10],[19,16,0,13,10,2,7],[0,2,19,16,13,4,10],[19,0,16,13,10,2,7],[0,19,16,13,10,2,7],[19,16,13,10,7,0,4],[0,2,4,6,8,19,16],[19,0,2,4,6,16,13],[0,19,2,4,6,16,13],[19,16,0,2,4,13,10],[0,2,19,4,6,16,13],[19,0,16,2,4,13,10],[0,19,16,2,4,13,10],[19,16,13,0,2,10,7],[0,2,4,19,6,16,13],[19,0,2,16,4,13,10],[0,19,2,16,4,13,10],[19,16,0,13,2,10,7],[0,2,19,16,4,13,10],[19,0,16,13,2,10,7],[0,19,16,13,2,10,7],[19,16,13,10,0,7,4],[0,2,4,6,19,16,13],[19,0,2,4,16,13,10],[0,19,2,4,16,13,10],[19,16,0,2,13,10,7],[0,2,19,4,16,13,10],[19,0,16,2,13,10,7],[0,19,16,2,13,10,7],[19,16,13,0,10,7,4],[0,2,4,19,16,13,10],[19,0,2,16,13,10,7],[0,19,2,16,13,10,7],[19,16,0,13,10,7,4],[0,2,19,16,13,10,7],[19,0,16,13,10,7,4],[0,19,16,13,10,7,4],[19,16,13,10,7,4,1]]
def planL32 : List (List Nat) :=[[0,2,4,6,8,10],[15,0,2,4,6,8],[0,15,2,4,6,8],[15,12,0,2,4,6],[0,2,15,4,6,8],[15,0,12,2,4,6],[0,15,12,2,4,6],[15,12,9,0,2,4],[0,2,4,15,6,8],[15,0,2,12,4,6],[0,15,2,12,4,6],[15,12,0,9,2,4],[0,2,15,12,4,6],[15,0,12,9,2,4],[0,15,12,9,2,4],[15,12,9,6,0,2],[0,2,4,6,15,8],[15,0,2,4,12,6],[0,15,2,4,12,6],[15,12,0,2,9,4],[0,2,15,4,12,6],[15,0,12,2,9,4],[0,15,12,2,9,4],[15,12,9,0,6,2],[0,2,4,15,12,6],[15,0,2,12,9,4],[0,15,2,12,9,4],[15,12,0,9,6,2],[0,2,15,12,9,4],[15,0,12,9,6,2],[0,15,12,9,6,2],[12,9,6,3,0,15],[0,2,4,6,8,15],[15,0,2,4,6,12],[0,15,2,4,6,12],[15,12,0,2,4,9],[0,2,15,4,6,12],[15,0,12,2,4,9],[0,15,12,2,4,9],[15,12,9,0,2,6],[0,2,4,15,6,12],[15,0,2,12,4,9],[0,15,2,12,4,9],[15,12,0,9,2,6],[0,2,15,12,4,9],[15,0,12,9,2,6],[0,15,12,9,2,6],[12,9,6,3,15,0],[0,2,4,6,15,12],[15,0,2,4,12,9],[0,15,2,4,12,9],[15,12,0,2,9,6],[0,2,15,4,12,9],[15,0,12,2,9,6],[0,15,12,2,9,6],[12,9,6,15,3,0],[0,2,4,15,12,9],[15,0,2,12,9,6],[0,15,2,12,9,6],[12,9,15,6,3,0],[0,2,15,12,9,6],[12,15,9,6,3,0],[15,12,9,6,3,0],[15,12,9,6,3,0]]
def plan (lay r j : Nat) : Nat := ((if lay = 1 then planL1 else planL32).getD r []).getD j 0
def rowA (lay c : Nat) : Nat := 0x800 + mkBase (lay + 1) + 16 * plan (lay + 1) c (hL (lay + 1) - 1)
def bufferBias (lay : Nat) : Nat := [24624,23632,22896,22160].getD lay 0
def bufferBase (lay : Nat) : Nat := [25136,24400,23664,22928].getD lay 0
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then baseK ++ [(.x12, BitVec.ofNat 64 2048), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7),
    (.x9, BitVec.ofNat 64 TOPB9), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)]
  else baseK ++ [(.x6, 0x10000), (.x2, 0x7fc00),
    (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x5, 0), (.x9, BitVec.ofNat 64 TOPB9), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias (lay+1)))]
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x9, BitVec.ofNat 64 TOPB9)] ++
    (if lay = 3 then [] else [(.x2, 0x7fc00), (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x5, 0), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias lay))])
def chainK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x2, 0x7fc00),
    (.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x5, 0), (.x27, 0x3fe00), (.x4, BitVec.ofNat 64 (bufferBias lay))]
def bK (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, 2048)] ++ (if lay = 3 then [(.x12, 2048)] else []) ++
  (if lay = 1 ∨ lay = 2 then [(.x22, BitVec.ofNat 64 (s6v lay))] else [])
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x31
def leafE (lay : Nat) : E := if lay = 0 then .reg .x31 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := if lay = 0 then .bin .sll (leafE lay) (kw 32) else .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def dispatchHeap (lay leaf : Nat) : Nat := if lay = 0 then 16 * (s7Bias lay + leaf) else s7Bias lay + leaf
def s7E (lay : Nat) : E := if lay = 0 then .bin .or (.bin .sll (leafE lay) (kw 4)) (kw (16 * 2 ^ hL lay)) else .bin .add (leafE lay) (kw (s7Bias lay))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x810 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay, kw 0x400000, d⟩
def setupPc (_lay p : Nat) : Nat := p
def setupAcceptDir (lay : Nat) : Bool := decide (lay = 3)
def hdrA (lay : Nat) : Nat := if lay = 3 then TOPLOAD + 32 else HDATA + 8 * lay
def t3E3 : E := .bin .or (.ld (kw (hdrA 3))) (.bin .sll (.reg .x22) (kw 16))
def specA (lay p : Nat) : Spec :=
  ⟨if lay = 3 then [(.x28, t3E3)] else [(.x23, s7E lay), (.x31, treeE lay), (.x28, t3E3)],
   [(⟨none, BitVec.ofNat 64 2072⟩, kw 1), (⟨none, BitVec.ofNat 64 2064⟩, t3E3)],
   p + stepsA lay, true, stepsA lay, [], none, stepsA lay⟩
def rejA (lay _p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 2072⟩, kw 1), (⟨none, BitVec.ofNat 64 2064⟩, t3E3)],
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
def spareTrap (lay c : Nat) : Nat := ([[],[142021,142149,142277,142405,142533,142661,142789,142917,143045,143173,143301,143429,143557,143685,143813,143941,144069,144197,144330,144453,144581,144709,144837,144965,145093,145221,145349,145477,145605,145733,145861,145989,146117,146245,146373,146501,146629,146757,146885,147013,147144,147269,147397,147525,147653,147781,147909,148037,148165,148293,148421,148549,148677,148805,148933,149061,149189,149317,149445,149573,149701,149829,149958,150085],[133829,133957,134085,134213,134341,134469,134597,134725,134853,134981,135109,135237,135365,135493,135621,135749,135877,136005,136133,136261,136389,136522,136645,136773,136901,137029,137157,137285,137413,137541,137669,137797,137925,138053,138181,138309,138437,138568,138693,138821,138949,139077,139205,139333,139461,139589,139717,139845,139973,140101,140229,140357,140485,140613,140741,140869,140997,141125,141253,141382,141509,141637,141765,141893],[871]].getD lay []).getD c 0
def rejBothSpare (lay c : Nat) : Spec :=
  ⟨[], [], spareTrap lay c, false, 8, [spareHiBr lay true, spareBr lay true], none, 8⟩
def lfAllowed (lay : Nat) : List Nat := [bufferBase lay+16,bufferBase lay+24]
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
    ⟨[], [(⟨none, BitVec.ofNat 64 (bufferBase lay+24)⟩, kw 0), (⟨none, BitVec.ofNat 64 (bufferBase lay+16)⟩, .reg .x28)], 0, false, 5, [],
      some (tgtLf lay), 5⟩
def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ [(.x10, BitVec.ofNat 64 (bufferBase lay)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704))]
def keepA : List Reg := []
def keepB (lay : Nat) : List Reg := if lay = 3 then [.x28] else [.x28, .x31]
def keepLf : List Reg := [.x23, .x31, .x22]
end SigGolfCandidate.T3M
