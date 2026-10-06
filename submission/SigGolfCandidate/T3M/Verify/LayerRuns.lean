import SigGolfCandidate.T3M.Verify.Spec

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def xtrTab : List (List Nat) :=[[48167,48231,48295,48359,48423,48487,48551,48615,48679,48743,48807,48871,48935,48999,49063,49127,49191,49255,49319,49383,49447,49511,49575,49639,49703,49767,49831,49895,49959,50023,50087,50151,50215,50279,50343,50407,50471,50535,50599,50663,50727,50791,50855,50919,50983,51047,51111,51175,51239,51303,51367,51431,51495,51559,51623,51687,51751,51815,51879,51943,52007,52071,52135,52199,52263,52327,52391,52455,52519,52583,52647,52711,52775,52839,52903,52967,53031,53095,53159,53223,53287,53351,53415,53479,53543,53607,53671,53735,53799,53863,53927,53991,54055,54119,54183,54247,54311,54375,54439,54503,54567,54631,54695,54759,54823,54887,54951,55015,55079,55143,55207,55271,55335,55399,55463,55527,55591,55655,55719,55783,55847,55911,55975,56039,56103,56167,56231,56295],[141985,142113,142241,142369,142497,142625,142753,142881,143009,143137,143265,143393,143521,143649,143777,143905,144033,144161,144289,144417,144545,144673,144801,144929,145057,145185,145313,145441,145569,145697,145825,145953,146081,146209,146337,146465,146593,146721,146849,146977,147105,147233,147361,147489,147617,147745,147873,148001,148129,148257,148385,148513,148641,148769,148897,149025,149153,149281,149409,149537,149665,149793,149921,150049],[133793,133921,134049,134177,134305,134433,134561,134689,134817,134945,135073,135201,135329,135457,135585,135713,135841,135969,136097,136225,136353,136481,136609,136737,136865,136993,137121,137249,137377,137505,137633,137761,137889,138017,138145,138273,138401,138529,138657,138785,138913,139041,139169,139297,139425,139553,139681,139809,139937,140065,140193,140321,140449,140577,140705,140833,140961,141089,141217,141345,141473,141601,141729,141857],[33372]]
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def hL (lay : Nat) : Nat := [12,7,6,6].getD lay 0
def stepsA (lay : Nat) : Nat := if lay = 3 then 12 else if lay = 0 then 9 else 13
def retOff (lay : Nat) : Nat := if lay = 0 then 11 else if lay = 3 then 42 else 41
def s6v (lay : Nat) : Nat := [11912,15880,19016,22152].getD lay 0
def s3v : Nat := 12616
def tgtL (lay : Nat) : Nat := [129,197,197,198].getD lay 0
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
def t3In (lay : Nat) : Nat := if lay = 0 then headerBank 0 0 else headerBank (lay + 1) 0
def lfT3 (lay : Nat) : Nat := if lay ≤ 1 then headerBank 0 0 else headerBank lay 0
def x10In (lay : Nat) : Nat := [14408,17608,20744].getD lay 0
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then baseK ++ [(.x8, BitVec.ofNat 64 0x400000), (.x24, BitVec.ofNat 64 M2c), (.x9, BitVec.ofNat 64 M1c),
    (.x27, BitVec.ofNat 64 (hw 4 3)), (.x2, BitVec.ofNat 64 0x3fe00), (.x12, BitVec.ofNat 64 256), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7), (.x1, BitVec.ofNat 64 TOPBASE), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)]
  else baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 (lay + 1))), (.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x8, BitVec.ofNat 64 0x400000),
    (.x15, BitVec.ofNat 64 0x40000), (.x10, BitVec.ofNat 64 (x10In lay)), (.x12, BitVec.ofNat 64 256),
    (.x1, BitVec.ofNat 64 TOPBASE)]
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 lay)), (.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x8, BitVec.ofNat 64 0x400000),
    (.x1, BitVec.ofNat 64 TOPBASE)] ++
    (if lay = 3 then [] else [(.x15, BitVec.ofNat 64 0x40000)])
def chainK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 lay)), (.x6, 0x10000), (.x2, 0x3fe00),
    (.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x8, BitVec.ofNat 64 0x400000),
    (.x15, BitVec.ofNat 64 0x40000)]
def ld3In : List (Reg × Word) := baseK ++ [(.x1, BitVec.ofNat 64 TOPBASE)]
def ld3Spec : Spec :=
  ⟨[(.x8, kw 0x400000), (.x24, .ld (kw TOPLOAD)), (.x9, .ld (kw (TOPLOAD + 8))),
      (.x27, .ld (kw (TOPLOAD + 16))), (.x2, .ld (kw (TOPLOAD + 24)))],
    [], 32978, false, 5, [], none, 5⟩
def ld3Check : Bool := specB [] [] baseK (runAt ld3In [32978] 32973 []) ld3Spec [] ld3In [.x22, .x12, .x26, .x7, .x13, .x30, .x19, .x20, .x21, .x6]
def bK (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, 256)] ++ (if lay = 3 then [(.x12, 256)] else []) ++
  (if lay = 1 ∨ lay = 2 then [(.x22, BitVec.ofNat 64 (s6v lay))] else []) ++
  (if lay = 3 then [(.x1, BitVec.ofNat 64 TOPBASE)] else [])
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x31
def leafE (lay : Nat) : E := if lay = 0 then .reg .x31 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := if lay = 0 then .bin .sll (leafE lay) (kw 32) else .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def dispatchHeap (lay leaf : Nat) : Nat := s7Bias lay + leaf
def s7E (lay : Nat) : E := if lay = 0 then .bin .or (leafE lay) (kw (2 ^ hL lay)) else .bin .add (leafE lay) (kw (s7Bias lay))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x810 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay, kw 0x400000, d⟩
def setupPc (lay p : Nat) : Nat := if lay = 3 then 32978 else p
def setupAcceptDir (lay : Nat) : Bool := decide (lay = 3)
def specA (lay p : Nat) : Spec :=
  ⟨if lay = 0 then [(.x4, tpE lay), (.x23, s7E lay), (.x3, ctrE lay)]
   else [(.x4, tpE lay), (.x23, s7E lay), (.x31, treeE lay), (.x3, ctrE lay)] ++
     (if lay = 3 then [(.x22, .reg .x22)] else
       [(.x28, .bin .sll (.reg (rReg lay)) (kw 16))]),
   [(⟨none, BitVec.ofNat 64 288⟩, .bin (.st .w 0) (.ld (kw 288)) (ctrE lay)), (⟨none, BitVec.ofNat 64 280⟩, tpE lay),
    (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   p + stepsA lay, true, stepsA lay, [ctrBr lay (setupAcceptDir lay)], none, stepsA lay⟩
def rejA (lay p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 280⟩, tpE lay), (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   (if lay = 3 then 32991 else rejEcall), true, stepsA lay + 1, [ctrBr lay (!setupAcceptDir lay)], none, stepsA lay + 1⟩
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
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x40000)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 260384)) (.c (~~~1#64))
def bSt (lay : Nat) : Nat := if lay = 3 then 27 else if lay = 1 ∨ lay = 2 then 24 else 33
def bCy (lay : Nat) : Nat := if lay = 3 then 30 else if lay = 1 ∨ lay = 2 then 27 else 36
def hdrA (lay : Nat) : Nat := if lay = 3 then TOPLOAD + 32 else HDATA + 8 * lay
def packedRouteE (lay : Nat) : E :=
  if lay = 3 then .bin .or (.ld (kw (hdrA lay))) (.bin .sll (.reg .x22) (kw 16))
  else if lay = 1 ∨ lay = 2 then .bin .or (.reg .x28) (.ld (kw (hdrA lay)))
  else .bin .or (.bin .or (.ld (kw (hdrA lay)))
    (if lay = 1 then .bin .srl (.reg .x4) (kw 16)
      else .bin .sll (.bin .srl (.reg .x4) (kw 32)) (kw 16)))
    (.bin .sll (.reg .x31) (kw (hL lay + 16)))
def prefixReturn (lay p : Nat) : Nat := p + (if lay = 3 then 37 else 38)
def s7Sh (lay : Nat) : Nat := if lay = 1 then 8 else 9
def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7E), (.x23, .bin .sll (.reg .x23) (kw (s7Sh lay))),
    (.x25, if lay ≠ 0 then sumE else kw (0x1000 + 4 * prefixReturn lay p)), (.x29, t4E lay),
    (.x3, if lay = 3 then .bin .sll (.reg .x22) (kw 16) else if lay = 1 ∨ lay = 2 then .ld (kw (hdrA lay))
      else .bin .sll (.reg .x31) (kw (hL lay + 16))), (.x14, x14l), (.x28, packedRouteE lay)] ++
     (if lay = 3 then [(.x22, .ld (kw (TOPLOAD - 8)))] else []),
   [], 0, false, bSt lay, [ckBr lay false, spareBr false], some tgtl, bCy lay⟩
def postBl (lay p : Nat) : List (Reg × Word) :=
  chainK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x40000), (.x1, BitVec.ofNat 64 TOPBASE)]
def postBlC (lay p : Nat) : List (Reg × Word) :=
  if lay = 3 then chainK lay ++ [(.x15, 0x40000), (.x1, BitVec.ofNat 64 TOPBASE)] else postBl lay p
def rejSpare : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [spareBr true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 20, [ckBr lay true, spareBr false], none, 23⟩
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
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 4 lay))] ++
    (if lay = 0 then [(.x15, 4096), (.x6, 130048)] else [(.x7, 1), (.x15, 0x40000)])
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .sll (.bin .add (.bin .and (.reg .x23) (kw 63)) (kw 2042)) (kw 8)
  else if lay = 1 then .bin .sll (.reg .x23) (kw 8)
  else .bin .sll (.reg .x23) (kw 9)
def tgtLf (lay : Nat) : E := if lay = 0 then .bin .and (x14lf lay) (.c (~~~1#64)) else .bin .and (.reg .x23) (.c (~~~1#64))
def lfDirs (_lay : Nat) : List Dir := [.jmp]
def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0), (⟨none, BitVec.ofNat 64 536⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))], 0, false, 12, [], some (tgtLf lay), 12⟩
  else
    ⟨[],
     [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4), (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay))], 0, false,
     7, [], some (tgtLf lay), 7⟩
def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++
   [(.x3, BitVec.ofNat 64 (hw 2 lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)),
    (.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704)),
    (.x15, BitVec.ofNat 64 (if lay = 0 then 4096 else 0x40000))]
def keepA : List Reg := []
def keepB : List Reg := [.x4, .x31]
def keepLf : List Reg := [.x23, .x31, .x22]
def keepTopCall : List Reg := [.x2, .x3, .x4, .x5, .x7, .x13, .x19, .x20, .x10, .x11, .x12, .x21, .x14, .x15, .x16, .x17, .x18, .x8, .x9, .x24, .x22, .x23, .x6, .x25, .x26, .x27, .x28, .x29, .x31, .x30]
def specTopCall (p : Nat) : Spec :=
  ⟨[(.x1, kw (0x1000 + 4 * (p + 11)))], [], 96160, false, 1, [], none, 1⟩
end SigGolfCandidate.T3M
