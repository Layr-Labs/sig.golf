import SigGolfCandidate.T3M.Verify.Spec

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def xtrTab : List (List Nat) :=[[48168,48232,48296,48360,48424,48488,48552,48616,48680,48744,48808,48872,48936,49000,49064,49128,49192,49256,49320,49384,49448,49512,49576,49640,49704,49768,49832,49896,49960,50024,50088,50152,50216,50280,50344,50408,50472,50536,50600,50664,50728,50792,50856,50920,50984,51048,51112,51176,51240,51304,51368,51432,51496,51560,51624,51688,51752,51816,51880,51944,52008,52072,52136,52200,52264,52328,52392,52456,52520,52584,52648,52712,52776,52840,52904,52968,53032,53096,53160,53224,53288,53352,53416,53480,53544,53608,53672,53736,53800,53864,53928,53992,54056,54120,54184,54248,54312,54376,54440,54504,54568,54632,54696,54760,54824,54888,54952,55016,55080,55144,55208,55272,55336,55400,55464,55528,55592,55656,55720,55784,55848,55912,55976,56040,56104,56168,56232,56296],[141986,142114,142242,142370,142498,142626,142754,142882,143010,143138,143266,143394,143522,143650,143778,143906,144034,144162,144290,144418,144546,144674,144802,144930,145058,145186,145314,145442,145570,145698,145826,145954,146082,146210,146338,146466,146594,146722,146850,146978,147106,147234,147362,147490,147618,147746,147874,148002,148130,148258,148386,148514,148642,148770,148898,149026,149154,149282,149410,149538,149666,149794,149922,150050],[133794,133922,134050,134178,134306,134434,134562,134690,134818,134946,135074,135202,135330,135458,135586,135714,135842,135970,136098,136226,136354,136482,136610,136738,136866,136994,137122,137250,137378,137506,137634,137762,137890,138018,138146,138274,138402,138530,138658,138786,138914,139042,139170,139298,139426,139554,139682,139810,139938,140066,140194,140322,140450,140578,140706,140834,140962,141090,141218,141346,141474,141602,141730,141858],[33373]]
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def hL (lay : Nat) : Nat := [12,7,6,6].getD lay 0
def stepsA (lay : Nat) : Nat := if lay = 3 then 11 else if lay = 0 then 5 else 7
def retOff (lay : Nat) : Nat := if lay = 0 then 11 else if lay = 3 then 42 else 41
def s6v (lay : Nat) : Nat := [12480,15664,18720,21776].getD lay 0
def s3v : Nat := 12480
def tgtL (lay : Nat) : Nat := [129,198,198,198].getD lay 0
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
def rejEcall : Nat := 33511
def stabIdx (lay : Nat) : Nat := [209768,209640,209576,209512].getD lay 0
def stabMask (lay : Nat) : Nat := if lay = 1 then 508 else 252
def s7Bias (lay : Nat) : Nat := [4096,768,1117,1053].getD lay 0
def stabW (lay sh : Nat) : Nat :=
  if lay = 0 then 129664 + 64 * sh else if lay = 1 then 48128 + 64 * sh else if lay = 2 then 141952 + 128 * sh else 133760 + 128 * sh
def M1c : Nat := 8198552921648689607
def M2c : Nat := 17311559823019733055
def M4c : Nat := 3689348814741910323
def M8c : Nat := 1085102592571150095
def mkBase (lay : Nat) : Nat := [8000,12224,15344,18400].getD lay 0
def planL1 : List (List Nat) :=[[0,2,4,6,8,10,12],[19,0,2,4,6,8,10],[0,19,2,4,6,8,10],[19,16,0,2,4,6,8],[0,2,19,4,6,8,10],[19,0,16,2,4,6,8],[0,19,16,2,4,6,8],[19,16,13,0,2,4,6],[0,2,4,19,6,8,10],[19,0,2,16,4,6,8],[0,19,2,16,4,6,8],[19,16,0,13,2,4,6],[0,2,19,16,4,6,8],[19,0,16,13,2,4,6],[0,19,16,13,2,4,6],[19,16,13,10,0,2,4],[0,2,4,6,19,8,10],[19,0,2,4,16,6,8],[0,19,2,4,16,6,8],[19,16,0,2,13,4,6],[0,2,19,4,16,6,8],[19,0,16,2,13,4,6],[0,19,16,2,13,4,6],[19,16,13,0,10,2,4],[0,2,4,19,16,6,8],[19,0,2,16,13,4,6],[0,19,2,16,13,4,6],[19,16,0,13,10,2,4],[0,2,19,16,13,4,6],[19,0,16,13,10,2,4],[0,19,16,13,10,2,4],[19,16,13,10,7,0,2],[0,2,4,6,8,19,10],[19,0,2,4,6,16,8],[0,19,2,4,6,16,8],[19,16,0,2,4,13,6],[0,2,19,4,6,16,8],[19,0,16,2,4,13,6],[0,19,16,2,4,13,6],[19,16,13,0,2,10,4],[0,2,4,19,6,16,8],[19,0,2,16,4,13,6],[0,19,2,16,4,13,6],[19,16,0,13,2,10,4],[0,2,19,16,4,13,6],[19,0,16,13,2,10,4],[0,19,16,13,2,10,4],[19,16,13,10,0,7,2],[0,2,4,6,19,16,8],[19,0,2,4,16,13,6],[0,19,2,4,16,13,6],[19,16,0,2,13,10,4],[0,2,19,4,16,13,6],[19,0,16,2,13,10,4],[0,19,16,2,13,10,4],[19,16,13,0,10,7,2],[0,2,4,19,16,13,6],[19,0,2,16,13,10,4],[0,19,2,16,13,10,4],[19,16,0,13,10,7,2],[0,2,19,16,13,10,4],[19,0,16,13,10,7,2],[0,19,16,13,10,7,2],[19,16,13,10,7,4,0],[0,2,4,6,8,10,14],[19,0,2,4,6,8,16],[0,19,2,4,6,8,16],[19,16,0,2,4,6,13],[0,2,19,4,6,8,16],[19,0,16,2,4,6,13],[0,19,16,2,4,6,13],[19,16,13,0,2,4,10],[0,2,4,19,6,8,16],[19,0,2,16,4,6,13],[0,19,2,16,4,6,13],[19,16,0,13,2,4,10],[0,2,19,16,4,6,13],[19,0,16,13,2,4,10],[0,19,16,13,2,4,10],[19,16,13,10,0,2,7],[0,2,4,6,19,8,16],[19,0,2,4,16,6,13],[0,19,2,4,16,6,13],[19,16,0,2,13,4,10],[0,2,19,4,16,6,13],[19,0,16,2,13,4,10],[0,19,16,2,13,4,10],[19,16,13,0,10,2,7],[0,2,4,19,16,6,13],[19,0,2,16,13,4,10],[0,19,2,16,13,4,10],[19,16,0,13,10,2,7],[0,2,19,16,13,4,10],[19,0,16,13,10,2,7],[0,19,16,13,10,2,7],[19,16,13,10,7,0,4],[0,2,4,6,8,19,16],[19,0,2,4,6,16,13],[0,19,2,4,6,16,13],[19,16,0,2,4,13,10],[0,2,19,4,6,16,13],[19,0,16,2,4,13,10],[0,19,16,2,4,13,10],[19,16,13,0,2,10,7],[0,2,4,19,6,16,13],[19,0,2,16,4,13,10],[0,19,2,16,4,13,10],[19,16,0,13,2,10,7],[0,2,19,16,4,13,10],[19,0,16,13,2,10,7],[0,19,16,13,2,10,7],[19,16,13,10,0,7,4],[0,2,4,6,19,16,13],[19,0,2,4,16,13,10],[0,19,2,4,16,13,10],[19,16,0,2,13,10,7],[0,2,19,4,16,13,10],[19,0,16,2,13,10,7],[0,19,16,2,13,10,7],[19,16,13,0,10,7,4],[0,2,4,19,16,13,10],[19,0,2,16,13,10,7],[0,19,2,16,13,10,7],[19,16,0,13,10,7,4],[0,2,19,16,13,10,7],[19,0,16,13,10,7,4],[0,19,16,13,10,7,4],[19,16,13,10,7,4,1]]
def planL32 : List (List Nat) :=[[0,2,4,6,8,10],[15,0,2,4,6,8],[0,15,2,4,6,8],[15,12,0,2,4,6],[0,2,15,4,6,8],[15,0,12,2,4,6],[0,15,12,2,4,6],[15,12,9,0,2,4],[0,2,4,15,6,8],[15,0,2,12,4,6],[0,15,2,12,4,6],[15,12,0,9,2,4],[0,2,15,12,4,6],[15,0,12,9,2,4],[0,15,12,9,2,4],[15,12,9,6,0,2],[0,2,4,6,15,8],[15,0,2,4,12,6],[0,15,2,4,12,6],[15,12,0,2,9,4],[0,2,15,4,12,6],[15,0,12,2,9,4],[0,15,12,2,9,4],[15,12,9,0,6,2],[0,2,4,15,12,6],[15,0,2,12,9,4],[0,15,2,12,9,4],[15,12,0,9,6,2],[0,2,15,12,9,4],[15,0,12,9,6,2],[0,15,12,9,6,2],[12,9,6,3,0,15],[0,2,4,6,8,15],[15,0,2,4,6,12],[0,15,2,4,6,12],[15,12,0,2,4,9],[0,2,15,4,6,12],[15,0,12,2,4,9],[0,15,12,2,4,9],[15,12,9,0,2,6],[0,2,4,15,6,12],[15,0,2,12,4,9],[0,15,2,12,4,9],[15,12,0,9,2,6],[0,2,15,12,4,9],[15,0,12,9,2,6],[0,15,12,9,2,6],[12,9,6,3,15,0],[0,2,4,6,15,12],[15,0,2,4,12,9],[0,15,2,4,12,9],[15,12,0,2,9,6],[0,2,15,4,12,9],[15,0,12,2,9,6],[0,15,12,2,9,6],[12,9,6,15,3,0],[0,2,4,15,12,9],[15,0,2,12,9,6],[0,15,2,12,9,6],[12,9,15,6,3,0],[0,2,15,12,9,6],[12,15,9,6,3,0],[15,12,9,6,3,0],[15,12,9,6,3,0]]
def plan (lay r j : Nat) : Nat := ((if lay = 1 then planL1 else planL32).getD r []).getD j 0
def rowA (lay c : Nat) : Nat := 0x800 + mkBase (lay + 1) + 16 * plan (lay + 1) c (hL (lay + 1) - 1)
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then baseK ++ [(.x24, BitVec.ofNat 64 M2c), (.x9, BitVec.ofNat 64 M1c),
    (.x2, BitVec.ofNat 64 0x3fe00), (.x12, BitVec.ofNat 64 2048), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7),
    (.x1, BitVec.ofNat 64 TOPBASE), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)]
  else baseK ++ [(.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x2, BitVec.ofNat 64 0x3fe00), (.x1, BitVec.ofNat 64 TOPBASE)]
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x1, BitVec.ofNat 64 TOPBASE)] ++
    (if lay = 3 then [] else [(.x2, BitVec.ofNat 64 0x3fe00)])
def chainK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7),
    (.x2, BitVec.ofNat 64 0x3fe00)]
def ld3In : List (Reg × Word) := baseK ++ [(.x1, BitVec.ofNat 64 TOPBASE)]
def ld3Spec : Spec :=
  ⟨[(.x24, .ld (kw TOPLOAD)), (.x9, .ld (kw (TOPLOAD + 8))), (.x2, .ld (kw (TOPLOAD + 24)))],
    [], 32955, false, 3, [], none, 3⟩
def ld3Check : Bool := specB [] [] baseK (runAt ld3In [32955] 32952 []) ld3Spec [] ld3In [.x22, .x12, .x26, .x7, .x13, .x30, .x19, .x20, .x21, .x6]
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
def setupPc (lay p : Nat) : Nat := if lay = 3 then 32955 else p
def setupAcceptDir (lay : Nat) : Bool := decide (lay = 3)
def hdrA (lay : Nat) : Nat := if lay = 3 then TOPLOAD + 32 else HDATA + 8 * lay
def t3E3 : E := .bin .or (.ld (kw (hdrA 3))) (.bin .sll (.reg .x22) (kw 16))
def specA (lay p : Nat) : Spec :=
  ⟨[(.x23, s7E lay), (.x31, treeE lay), (.x28, t3E3)],
   [(⟨none, BitVec.ofNat 64 2072⟩, kw 1), (⟨none, BitVec.ofNat 64 2064⟩, t3E3)],
   p + stepsA lay, true, stepsA lay, [], none, stepsA lay⟩
def rejA (lay p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 2072⟩, kw 1), (⟨none, BitVec.ofNat 64 2064⟩, t3E3)],
   32989, true, 33, [ctrBr lay (!setupAcceptDir lay)], none, 33⟩
def a6E : E := .ld (.reg .x12)
def a7E : E := .ld (.bin .add (.reg .x12) (kw 8))
def b1E : E := .bin .sll a7E (kw 1)
def sw1RefE : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl a7E (kw 3)) (kw M1c))) (.bin .and a7E (kw M1c))
def swLowE : E := .bin .add (.bin .and a6E (kw M1c)) (.bin .and a7E (kw M1c))
def sw1E : E := .bin .add swLowE (.bin .srl (.bin .sub (.bin .add a6E a7E) swLowE) (kw 3))
def sumE : E := .bin .remu (.bin .and (.bin .add sw1E (.bin .srl sw1E (kw 6))) (kw M2c)) (kw 4095)
def t4E (lay : Nat) : E := .bin .add sumE (kw (2 ^ 64 - (tgtL lay - 7)))
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.ltu, kw 7, t4E lay, d⟩
def spareBr (d : Bool) : Br := ⟨.ge, .bin .and a6E a7E, kw 0, d⟩
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x3fe00)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 260384)) (.c (~~~1#64))
def bSt (lay : Nat) : Nat := if lay = 3 then 23 else if lay = 1 ∨ lay = 2 then 22 else 33
def bCy (lay : Nat) : Nat := if lay = 3 then 26 else if lay = 1 ∨ lay = 2 then 25 else 36
def prefixReturn (lay p : Nat) : Nat := p + (if lay = 3 then 37 else 38)
def s7Sh (lay : Nat) : Nat := if lay = 1 then 8 else 9
def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7E), (.x23, .bin .sll (.reg .x23) (kw (s7Sh lay))), (.x25, sumE), (.x29, t4E lay),
    (.x14, x14l)] ++ (if lay = 3 then [(.x22, .ld (kw (TOPLOAD - 8)))] else []),
   [], 0, false, bSt lay, [ckBr lay false, spareBr false], some tgtl, bCy lay⟩
def postBl (lay p : Nat) : List (Reg × Word) :=
  chainK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x2, 0x3fe00), (.x1, BitVec.ofNat 64 TOPBASE)]
def postBlC (lay p : Nat) : List (Reg × Word) :=
  if lay = 3 then chainK lay ++ [(.x2, 0x3fe00), (.x1, BitVec.ofNat 64 TOPBASE)] else postBl lay p
def rejSpare : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [spareBr true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 20, [ckBr lay true, spareBr false], none, 23⟩
def leafK (lay : Nat) : List (Reg × Word) :=
  baseK ++ (if lay = 0 then [(.x6, 130048)] else [(.x7, 1)])
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .sll (.bin .add (.bin .and (.reg .x31) (kw 63)) (kw 2042)) (kw 8)
  else if lay = 1 then .bin .sll (.reg .x23) (kw 8)
  else .bin .sll (.reg .x23) (kw 9)
def tgtLf (lay : Nat) : E := if lay = 0 then .bin .and (x14lf lay) (.c (~~~1#64)) else .bin .and (.reg .x23) (.c (~~~1#64))
def lfDirs (_lay : Nat) : List Dir := [.jmp]
def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)], [(⟨none, BitVec.ofNat 64 528⟩, .reg .x28)], 0, false, 7, [], some (tgtLf lay), 7⟩
  else
    ⟨[], [(⟨none, BitVec.ofNat 64 792⟩, kw 0), (⟨none, BitVec.ofNat 64 784⟩, .reg .x28)], 0, false, 5, [],
      some (tgtLf lay), 5⟩
def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ [(.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704))]
def keepA : List Reg := []
def keepB : List Reg := [.x28, .x31]
def keepLf : List Reg := [.x23, .x31, .x22]
end SigGolfCandidate.T3M
