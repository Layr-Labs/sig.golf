import SigGolfCandidate.T3M.Verify.Spec

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def xtrTab : List (List Nat) :=[[31783,31847,31911,31975,32039,32103,32167,32231,32295,32359,32423,32487,32551,32615,32679,32743,32807,32871,32935,32999,33063,33127,33191,33255,33319,33383,33447,33511,33575,33639,33703,33767,33831,33895,33959,34023,34087,34151,34215,34279,34343,34407,34471,34535,34599,34663,34727,34791,34855,34919,34983,35047,35111,35175,35239,35303,35367,35431,35495,35559,35623,35687,35751,35815,35879,35943,36007,36071,36135,36199,36263,36327,36391,36455,36519,36583,36647,36711,36775,36839,36903,36967,37031,37095,37159,37223,37287,37351,37415,37479,37543,37607,37671,37735,37799,37863,37927,37991,38055,38119,38183,38247,38311,38375,38439,38503,38567,38631,38695,38759,38823,38887,38951,39015,39079,39143,39207,39271,39335,39399,39463,39527,39591,39655,39719,39783,39847,39911],[23585,23713,23841,23969,24097,24225,24353,24481,24609,24737,24865,24993,25121,25249,25377,25505,25633,25761,25889,26017,26145,26273,26401,26529,26657,26785,26913,27041,27169,27297,27425,27553,27681,27809,27937,28065,28193,28321,28449,28577,28705,28833,28961,29089,29217,29345,29473,29601,29729,29857,29985,30113,30241,30369,30497,30625,30753,30881,31009,31137,31265,31393,31521,31649],[15393,15521,15649,15777,15905,16033,16161,16289,16417,16545,16673,16801,16929,17057,17185,17313,17441,17569,17697,17825,17953,18081,18209,18337,18465,18593,18721,18849,18977,19105,19233,19361,19489,19617,19745,19873,20001,20129,20257,20385,20513,20641,20769,20897,21025,21153,21281,21409,21537,21665,21793,21921,22049,22177,22305,22433,22561,22689,22817,22945,23073,23201,23329,23457],[604]]
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def hL (lay : Nat) : Nat := [12,7,6,6].getD lay 0
def stepsA (lay : Nat) : Nat := if lay = 3 then 12 else if lay = 0 then 8 else 13
def retOff (lay : Nat) : Nat := if lay = 0 then 11 else if lay = 3 then 42 else 41
def s6v (lay : Nat) : Nat := [13064,17032,20168,23304].getD lay 0
def s3v : Nat := 13768
def tgtL (lay : Nat) : Nat := [129,197,197,198].getD lay 0
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
def rejEcall : Nat := 743
def stabIdx (lay : Nat) : Nat := [209768,209640,209576,209512].getD lay 0
def stabMask (lay : Nat) : Nat := if lay = 1 then 508 else 252
def s7Bias (lay : Nat) : Nat := [4096,512,192,128].getD lay 0
def stabW (lay sh : Nat) : Nat :=
  if lay = 0 then 96256 + 64 * sh else if lay = 1 then 31744 + 64 * sh else if lay = 2 then 23552 + 128 * sh else 15360 + 128 * sh
def M1c : Nat := 8198552921648689607
def M2c : Nat := 17311559823019733055
def M4c : Nat := 3689348814741910323
def M8c : Nat := 1085102592571150095
def t3In (lay : Nat) : Nat := if lay = 0 then headerBank 0 0 else headerBank (lay + 1) 0
def lfT3 (lay : Nat) : Nat := if lay ≤ 1 then headerBank 0 0 else headerBank lay 0
def x10In (lay : Nat) : Nat := [15560,18760,21896].getD lay 0
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then baseK ++ [(.x8, BitVec.ofNat 64 0x400000), (.x24, BitVec.ofNat 64 M2c), (.x9, BitVec.ofNat 64 M1c),
    (.x27, BitVec.ofNat 64 (hw 4 3)), (.x2, BitVec.ofNat 64 0x3fe00), (.x12, BitVec.ofNat 64 256), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7), (.x28, BitVec.ofNat 64 TOPBASE), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)]
  else baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 (lay + 1))), (.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x8, BitVec.ofNat 64 0x400000),
    (.x15, BitVec.ofNat 64 0x6e000), (.x10, BitVec.ofNat 64 (x10In lay)), (.x12, BitVec.ofNat 64 256)]
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 lay)), (.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x8, BitVec.ofNat 64 0x400000)] ++
    (if lay = 3 then [] else [(.x15, BitVec.ofNat 64 0x6e000)])
def chainK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 lay)), (.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x8, BitVec.ofNat 64 0x400000),
    (.x15, BitVec.ofNat 64 0x6e000)]
def ld3In : List (Reg × Word) := baseK ++ [(.x28, BitVec.ofNat 64 TOPBASE)]
def ld3Spec : Spec :=
  ⟨[(.x8, kw 0x400000), (.x24, .ld (kw TOPLOAD)), (.x9, .ld (kw (TOPLOAD + 8))),
      (.x27, .ld (kw (TOPLOAD + 16))), (.x2, .ld (kw (TOPLOAD + 24)))],
    [], 210, false, 5, [], none, 5⟩
def ld3Check : Bool := specB [] [] baseK (runAt ld3In [210] 205 []) ld3Spec [] ld3In [.x22, .x12, .x26, .x7, .x13, .x30, .x19, .x20, .x21, .x6]
def bK (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, 256)] ++ (if lay = 3 then [(.x12, 256)] else []) ++
  (if lay = 1 ∨ lay = 2 then [(.x22, BitVec.ofNat 64 (s6v lay))] else []) ++
  (if lay = 3 then [(.x28, BitVec.ofNat 64 TOPBASE)] else [])
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x31
def leafE (lay : Nat) : E := if lay = 0 then .reg .x31 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := if lay = 0 then .bin .sll (leafE lay) (kw 32) else .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def tp0E (lay : Nat) : E := if lay = 0 then .reg .x4 else tpE lay
def dispatchHeap (lay leaf : Nat) : Nat := s7Bias lay + leaf
def s7E (lay : Nat) : E := if lay = 0 then .bin .or (leafE lay) (kw (2 ^ hL lay)) else .bin .add (leafE lay) (kw (s7Bias lay))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x810 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay, kw 0x400000, d⟩
def setupPc (lay p : Nat) : Nat := if lay = 3 then 210 else p
def setupAcceptDir (lay : Nat) : Bool := decide (lay = 3)
def specA (lay p : Nat) : Spec :=
  ⟨if lay = 0 then [(.x4, tp0E lay), (.x23, s7E lay), (.x3, ctrE lay)]
   else [(.x4, tp0E lay), (.x23, s7E lay), (.x31, treeE lay), (.x3, ctrE lay)] ++
     (if lay = 3 then [(.x22, .reg .x22)] else
       [(.x28, .bin .sll (.reg (rReg lay)) (kw 16))]),
   [(⟨none, BitVec.ofNat 64 288⟩, .bin (.st .w 0) (.ld (kw 288)) (ctrE lay)), (⟨none, BitVec.ofNat 64 280⟩, tp0E lay),
    (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   p + stepsA lay, true, stepsA lay, [ctrBr lay (setupAcceptDir lay)], none, stepsA lay⟩
def rejA (lay p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 280⟩, tp0E lay), (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   (if lay = 3 then 223 else rejEcall), true, stepsA lay + 1, [ctrBr lay (!setupAcceptDir lay)], none, stepsA lay + 1⟩
def a6E : E := .ld (.reg .x12)
def a7E : E := .ld (.bin .add (.reg .x12) (kw 8))
def b1E : E := .bin .sll a7E (kw 1)
def sw1RefE : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl b1E (kw 3)) (kw M1c))) (.bin .and b1E (kw M1c))
def swLowE : E := .bin .add (.bin .and a6E (kw M1c)) (.bin .and b1E (kw M1c))
def sw1E : E := .bin .add swLowE (.bin .srl (.bin .sub (.bin .add a6E b1E) swLowE) (kw 3))
def sumE : E := .bin .remu (.bin .and (.bin .add sw1E (.bin .srl sw1E (kw 6))) (kw M2c)) (kw 4095)
def t4E (lay : Nat) : E := .bin .add sumE (kw (2 ^ 64 - (tgtL lay - 7)))
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.ltu, kw 7, t4E lay, d⟩
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x6e000)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 448800)) (.c (~~~1#64))
def bSt (lay : Nat) : Nat := if lay = 3 then 29 else if lay = 1 ∨ lay = 2 then 27 else 33
def bCy (lay : Nat) : Nat := if lay = 3 then 32 else if lay = 1 ∨ lay = 2 then 30 else 36
def hdrA (lay : Nat) : Nat := if lay = 3 then TOPLOAD + 32 else HDATA + 8 * lay
def packedRouteE (lay : Nat) : E :=
  if lay = 3 then .bin .or (.ld (kw (hdrA lay))) (.bin .sll (.reg .x22) (kw 16))
  else if lay = 1 ∨ lay = 2 then .bin .or (.reg .x28) (.ld (kw (hdrA lay)))
  else .bin .or (.bin .or (.ld (kw (hdrA lay)))
    (if lay = 1 then .bin .srl (.reg .x4) (kw 16)
      else .bin .sll (.bin .srl (.reg .x4) (kw 32)) (kw 16)))
    (.bin .sll (.reg .x31) (kw (hL lay + 16)))
def prefixReturn (lay p : Nat) : Nat := p + (if lay = 3 then 37 else 38)
def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7lE),
    (.x25, if lay ≠ 0 then sumE else kw (0x1000 + 4 * prefixReturn lay p)), (.x29, t4E lay),
    (.x3, if lay = 3 then .bin .sll (.reg .x22) (kw 16) else if lay = 1 ∨ lay = 2 then .ld (kw (hdrA lay))
      else .bin .sll (.reg .x31) (kw (hL lay + 16))), (.x14, x14l), (.x28, packedRouteE lay)] ++
     (if lay = 3 then [(.x22, .ld (kw (TOPLOAD - 8)))] else []),
   [], 0, false, bSt lay, [ckBr lay false, rngBr 62 false], some tgtl, bCy lay⟩
def postBl (lay p : Nat) : List (Reg × Word) :=
  chainK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x6e000), (.x1, pcOf (p + retOff lay))]
def postBlC (lay p : Nat) : List (Reg × Word) :=
  if lay = 3 then chainK lay ++ [(.x15, 0x6e000), (.x1, pcOf (p + retOff lay))] else postBl lay p
def rejRng (k : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [rngBr k true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 21, [ckBr lay true, rngBr 62 false], none, 24⟩
def gE : E := .bin .srl a7E (kw 34)
def p3E : E := .bin .add (.bin .and (.bin .srl gE (kw 3)) (kw M1c)) (.bin .and gE (kw M1c))
def s3E : E := .bin .remu (.bin .and (.bin .add p3E (.bin .srl p3E (kw 6))) (kw M2c)) (kw 4095)
def c34E : E := .bin .srl (.bin .sll a7E (kw 30)) (kw 30)
def l1E : E := .bin .add (.bin .and (.bin .srl a6E (kw 2)) (kw M4c)) (.bin .and a6E (kw M4c))
def l2E : E := .bin .add (.bin .and (.bin .srl c34E (kw 2)) (kw M4c)) (.bin .and c34E (kw M4c))
def lRefE : E := .bin .add l1E l2E
def lLowE : E := .bin .add (.bin .and a6E (kw M4c)) (.bin .and c34E (kw M4c))
def lE : E := .bin .add lLowE (.bin .srl (.bin .sub (.bin .add a6E c34E) lLowE) (kw 2))
def pE : E := .bin .add (.bin .and (.bin .srl lE (kw 4)) (kw M8c)) (.bin .and lE (kw M8c))
def totE : E := .bin .add (.bin .remu pE (kw 255)) s3E
def totBr (d : Bool) : Br := ⟨.ne, totE, kw 128, d⟩
def x14t : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 0xae000)
def tgtt : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 711072)) (.c (~~~1#64))
def specBt (p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, .bin .sll a7E (kw 2)), (.x3, totE), (.x14, x14t), (.x25, .bin .and c34E (kw M4c))],
   [], 0, false, 52, [totBr false, rngBr 61 false], some tgtt, 58⟩
def postBt (p : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 0)), (.x2, 0x3fe00), (.x9, BitVec.ofNat 64 M4c), (.x24, BitVec.ofNat 64 M8c),
    (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank 0 0)), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
    (.x30, 7), (.x22, BitVec.ofNat 64 (s6v 0)), (.x8, BitVec.ofNat 64 s3v), (.x6, 0x1fe00), (.x29, 8), (.x15, 0xae000),
    (.x1, pcOf (p + retOff 0))]
def rejTot : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 42, [totBr true, rngBr 61 false], none, 48⟩
def leafK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 lay))] ++ (if lay = 0 then [(.x15, 0xae000)] else [(.x7, 1), (.x15, 0x6e000)])
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .sll (.bin .add (.bin .and (.reg .x23) (kw 63)) (kw 1520)) (kw 8)
  else if lay = 1 then .bin .sll (.reg .x23) (kw 8)
  else .bin .sll (.reg .x23) (kw 9)
def tgtLf (lay : Nat) : E := .bin .and (x14lf lay) (.c (~~~1#64))
def lfDirs (_lay : Nat) : List Dir := [.jmp]
def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0), (⟨none, BitVec.ofNat 64 536⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))], 0, false, 12, [], some (tgtLf lay), 12⟩
  else
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4), (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay))], 0, false,
     8, [], some (tgtLf lay), 8⟩
def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++
   [(.x3, BitVec.ofNat 64 (hw 2 lay)), (if lay = 1 then .x25 else .x4, BitVec.ofNat 64 (hw 3 lay)),
    (.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704)),
    (.x15, BitVec.ofNat 64 (if lay = 0 then 0xae000 else 0x6e000))]
def keepA : List Reg := []
def keepB : List Reg := [.x4, .x23, .x31]
def keepLf : List Reg := [.x23, .x31, .x22]
def keepTopCall : List Reg := [.x2, .x3, .x4, .x5, .x7, .x13, .x19, .x20, .x10, .x11, .x12, .x21, .x14, .x15, .x16, .x17, .x18, .x8, .x9, .x24, .x22, .x23, .x6, .x25, .x26, .x27, .x28, .x29, .x31, .x30]
def specTopCall (p : Nat) : Spec :=
  ⟨[(.x1, kw (0x1000 + 4 * (p + 10)))], [], 96160, false, 1, [], none, 1⟩
def copyCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) keepA &&
  specB [] [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] &&
  (if lay = 0 then
    specB [] [] [] (runAt [] [96160] (p + stepsA lay + 1) []) (specTopCall p) [] [] keepTopCall
  else
    specB [] [] baseK (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) []
      (postBlC lay p) keepB &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) [] [] [] &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) [] [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) (lfDirs lay)) (specLf lay) [] (postLf lay) keepLf
def layerCheck (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => copyCheck lay (trPc lay c)
end SigGolfCandidate.T3M
