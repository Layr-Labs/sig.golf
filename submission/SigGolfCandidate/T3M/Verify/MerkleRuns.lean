import SigGolfCandidate.T3M.Verify.LayerRuns

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def mkKnownKeep (known : List (Reg × Word)) (keep : List Reg) : List (Reg × Word) :=
  known.filter fun p => keep.contains p.1
def mkUnknownKeep (known : List (Reg × Word)) (keep : List Reg) : List Reg :=
  keep.filter fun r => !(known.any fun p => p.1 == r)
def mkSpecB (allow : List Nat) (rel : List Reg) (gk known : List (Reg × Word))
    (stops : List Nat) (n : Nat) (dirs : List Dir) (sp : Spec)
    (obl : List Oblig) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  specB allow rel gk (runAt known stops n dirs) sp obl
    (post ++ mkKnownKeep known keep) (mkUnknownKeep known keep)
def mkNch (lay : Nat) : Nat := if lay = 0 then 2 else 1
def mkLo (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 6 else 0
def mkBits (lay ci : Nat) : Nat := if lay = 0 then 6 else hL lay
def mkTab (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 39936 else stabIdx lay
def mkTabW (lay ci sh : Nat) : Nat := if lay = 0 ∧ ci = 1 then 15612 + 256 * sh else stabW lay sh
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 133760 + 128 * sh else if lay = 2 then 141952 + 128 * sh
  else if lay = 1 then 48128 + 64 * sh else if ci = 0 then 129664 + 64 * sh else 39936 + 128 * sh
def mkReg (lay l : Nat) : Bool := decide (hL lay ≤ l + 3)
def mkWords (lay l : Nat) : Nat := (if l = 0 then (if lay = 0 then 6 else 8) else 5) + (if mkReg lay l then 0 else 1)
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
def mkBase (lay : Nat) : Nat := [8136,12360,15560,18696].getD lay 0
def mkBo (lay l : Nat) : Nat := mkBase lay + 64 * (hL lay - 1 - l)
def mkBlk (lay l : Nat) : Nat := 0x800 + mkBo lay l
def mkCur (lay l b : Nat) : Nat := mkBlk lay l + 48 * b
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then 10184 + 48 * (leaf / 2048 % 2) else 256
def mkMove (lay level : Nat) : Nat := if lay = 0 ∧ level = 11 then 0 else 1
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)
def mkHdrReg (lay : Nat) : Reg := if lay = 1 then .x25 else .x4
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (if lay = 0 then .x4 else .x25, BitVec.ofNat 64 (hw 3 lay)), (.x7, 1), (.x13, 2), (.x19, 3),
    (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x15, BitVec.ofNat 64 0x40000)]
def mkKc (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2), (.x19, 3),
    (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x15, BitVec.ofNat 64 0x40000)]
def mkX4 (lay : Nat) : E :=
  if lay = 1 then .bin .or (.bin .sll (.reg .x31) (kw 32)) (kw (hw 3 1))
  else .bin (.st .w 4) (kw (hw 3 lay)) (.reg .x31)
def mkKeep : List Reg := [.x1, .x2, .x16, .x17, .x8, .x9, .x24, .x23, .x6, .x27, .x28, .x29, .x31]
def mkEntSpec (lay ci sh : Nat) : Spec := let st := if lay = 0 ∧ ci = 1 then 2 else 1; ⟨[], [], mkShp lay ci sh + 1, true, st, [], none, st⟩
def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x12, BitVec.ofNat 64 (mkCur lay (mkLo lay ci) (sh % 2)))]
def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14, .x4, .x25]
def mkEntK (lay ci : Nat) : List (Reg × Word) :=
  mkKc lay ++ (if lay = 0 ∧ ci = 1 then [(.x10, BitVec.ofNat 64 (mkBlk 0 5))] else [])
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] baseK (mkEntK lay ci) [] (mkTabW lay ci sh) [] (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 5)) else kw (mkHeap lay ci sh l)
def mkHdrE (lay l : Nat) : E := if l = 0 then (if lay = 0 then kw (hw 3 lay) else mkX4 lay) else .reg (mkHdrReg lay)
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay l + 24)⟩, mkHeapE lay ci sh l),
   (⟨none, BitVec.ofNat 64 (mkBlk lay l + 16)⟩, mkHdrE lay l)]
def mkLvlRegs (lay l : Nat) : List (Reg × E) :=
  if l = 0 then (if lay = 0 then [(.x4, kw (hw 3 lay))] else if lay = 1 then [(.x25, mkX4 1), (.x4, tpE 0)] else [(.x4, mkX4 lay)]) else []
def mkLvlKeep (lay l : Nat) : List Reg := if l = 0 then [] else if lay = 1 then [.x25, .x4] else [.x4]
def mkLvlAllow (lay l : Nat) : List Nat := [mkBlk lay l + 16, mkBlk lay l + 24]
def mkDispTgt (sh : Nat) : E :=
  .bin .and (addC (.reg .x23) (BitVec.ofNat 64 (1008 - 16 * sh))) (.c (~~~1#64))
def mkBody (lay l : Nat) : Nat := (if l = 0 then (if lay = 0 then 3 else 5) else 2) + (if mkReg lay l then 1 else 2)
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2) else if lay = 0 then 10184 + 48 * (sh / 32 % 2) else 256
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk),
    mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk), true,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk), [], none,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk)⟩
def mkLvlSpecD (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk), 0, false,
    mkBody lay (mkLo lay ci + kk) + 1, [], some (mkDispTgt sh),
    mkBody lay (mkLo lay ci + kk) + 1⟩
def mkLvlK (lay l : Nat) : List (Reg × Word) := if l = 0 then mkK lay else mkKc lay ++ [(.x11, 64)]
def mkLvlPostN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))]
def mkLvlPostD (lay ci kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))), (.x15, 262144)]
def mkLvlKN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkLvlK lay (mkLo lay ci + kk) ++
    (if lay = 0 then
      [(.x12, BitVec.ofNat 64 (mkCur lay (mkLo lay ci + kk) (sh / 2 ^ kk % 2)))] else [])
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) []
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk) (mkKeep ++ (.x14 :: mkLvlKeep lay (mkLo lay ci + kk)))
def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [.jmp]
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci kk) (mkKeep ++ mkLvlKeep lay (mkLo lay ci + kk))
def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then mkLvlCheckD lay ci sh kk else mkLvlCheckN lay ci sh kk
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh && (List.range (mkBits lay ci)).all (mkLvlCheck lay ci sh)
def mkChunkCheck (lay ci lo n : Nat) : Bool := (List.range' lo n).all (mkBlockCheck lay ci)
def cmpPc (c : Nat) : Nat := 39970 + 128 * c
def cmpDst (c : Nat) : Nat := 10184 + 48 * (c / 32 % 2)
def cmpK (c : Nat) : List (Reg × Word) := baseK ++ [(.x12, BitVec.ofNat 64 (cmpDst c))]
def cmpBr1 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c)), .ld (kw 160), d⟩
def cmpBr2 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c + 8)), .ld (kw 168), d⟩
def cmpDelta (c : Nat) : E := .bin .sub (.ld (kw (cmpDst c + 8))) (.ld (kw 168))
def cmpAcc (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, cmpDelta c)], [], cmpPc c + 7, true, 7, [cmpBr1 c false], none, 7⟩
def cmpRej1 (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], cmpPc c + 11, true, 5, [cmpBr1 c true], none, 5⟩
def cmpCheck (c : Nat) : Bool :=
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br false]) (cmpAcc c) [] [] [] &&
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br true]) (cmpRej1 c) [] [] []
end SigGolfCandidate.T3M
