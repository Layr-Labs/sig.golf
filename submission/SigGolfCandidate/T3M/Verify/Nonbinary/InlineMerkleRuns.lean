/- Exact corrected662 Merkle constants and AE000 ABI. Only the concrete
   run lookup is replaced by the actual unchanged-image prefix lookup. -/
import SigGolfCandidate.T3M.Verify.LayerRuns
import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixSpec

namespace SigGolfCandidate.T3M.Nonbinary.InlineTail.Merkle
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Nonbinary.InlineTail
def mkKnownKeep (known : List (Reg × Word)) (keep : List Reg) : List (Reg × Word) :=
  known.filter fun p => keep.contains p.1
def mkUnknownKeep (known : List (Reg × Word)) (keep : List Reg) : List Reg :=
  keep.filter fun r => !(known.any fun p => p.1 == r)
def mkSpecB (allow : List Nat) (rel : List Reg) (gk known : List (Reg × Word))
    (stops : List Nat) (n : Nat) (dirs : List Dir) (sp : Spec)
    (obl : List Oblig) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  specB allow rel gk (prefixRunAt known stops n dirs) sp obl
    (post ++ mkKnownKeep known keep) (mkUnknownKeep known keep)
def mkNch (lay : Nat) : Nat := if lay = 0 then 2 else 1
def mkLo (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 6 else 0
def mkBits (lay ci : Nat) : Nat := if lay = 0 then 6 else hL lay
def mkTab (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 7168 else stabIdx lay
def mkTabW (lay ci sh : Nat) : Nat := if lay = 0 ∧ ci = 1 then 7168 + 128 * sh else stabW lay sh
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 15360 + 128 * sh else if lay = 2 then 23552 + 128 * sh
  else if lay = 1 then 31744 + 64 * sh else if ci = 0 then 96256 + 64 * sh else 7168 + 128 * sh
def mkReg (lay l : Nat) : Bool := decide (hL lay ≤ l + 3)
def mkWords (lay l : Nat) : Nat := (if l = 0 then (if lay = 0 then 6 else 8) else 5) + (if mkReg lay l then 0 else 1)
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
def mkBase (lay : Nat) : Nat := [9288,13512,16712,19848].getD lay 0
def mkBo (lay l : Nat) : Nat := mkBase lay + 64 * (hL lay - 1 - l)
def mkBlk (lay l : Nat) : Nat := 0x800 + mkBo lay l
def mkCur (lay l b : Nat) : Nat := mkBlk lay l + 48 * b
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then 11336 + 48 * (leaf / 2048 % 2) else 256
def mkMove (lay level : Nat) : Nat := if lay = 0 ∧ level = 11 then 0 else 1
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x4, BitVec.ofNat 64 (hw 3 lay)), (.x7, 1), (.x13, 2), (.x19, 3),
    (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x15, BitVec.ofNat 64 (if lay = 0 then 0xae000 else 0x6e000))]
def mkKc (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2), (.x19, 3),
    (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x15, BitVec.ofNat 64 (if lay = 0 then 0xae000 else 0x6e000))]
def mkX4 (lay : Nat) : E := .bin (.st .w 4) (kw (hw 3 lay)) (.reg .x31)
def mkKeep : List Reg := [.x1, .x2, .x16, .x17, .x8, .x9, .x24, .x23, .x6, .x25, .x27, .x28, .x29, .x31]
def mkEntSpec (lay ci sh : Nat) : Spec := ⟨[], [], mkShp lay ci sh + 1, true, 1, [], none, 1⟩
def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x12, BitVec.ofNat 64 (mkCur lay (mkLo lay ci) (sh % 2)))]
def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14, .x4]
def mkEntK (lay ci : Nat) : List (Reg × Word) :=
  mkKc lay ++ (if lay = 0 ∧ ci = 1 then [(.x10, BitVec.ofNat 64 (mkBlk 0 5))] else [])
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] baseK (mkEntK lay ci) [] (mkTabW lay ci sh) [] (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 1)) else kw (mkHeap lay ci sh l)
def mkHdrE (lay l : Nat) : E := if l = 0 then (if lay = 0 then kw (hw 3 lay) else mkX4 lay) else .reg .x4
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay l + 24)⟩, mkHeapE lay ci sh l),
   (⟨none, BitVec.ofNat 64 (mkBlk lay l + 16)⟩, mkHdrE lay l)]
def mkLvlRegs (lay l : Nat) : List (Reg × E) :=
  if l = 0 then (if lay = 0 then [(.x4, kw (hw 3 lay))] else [(.x4, mkX4 lay)]) else []
def mkLvlKeep (lay l : Nat) : List Reg := if l = 0 then [] else [.x4]
def mkLvlAllow (lay l : Nat) : List Nat := [mkBlk lay l + 16, mkBlk lay l + 24]
def mkDispTgt : E :=
  .bin .and (.bin .sll (.bin .srl (.reg .x23) (kw 6)) (kw 9)) (.c (~~~1#64))
def mkBody (lay l : Nat) : Nat := (if l = 0 then (if lay = 0 then 3 else 5) else 2) + (if mkReg lay l then 1 else 2)
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2) else if lay = 0 then 11336 + 48 * (sh / 32 % 2) else 256
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk),
    mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk), true,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk), [], none,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk)⟩
def mkLvlSpecD (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk), 0, false,
    mkBody lay (mkLo lay ci + kk) + 2, [], some mkDispTgt,
    mkBody lay (mkLo lay ci + kk) + 2⟩
def mkLvlK (lay l : Nat) : List (Reg × Word) := if l = 0 then mkK lay else mkKc lay ++ [(.x11, 64)]
def mkLvlPostN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))]
def mkLvlPostD (lay ci kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))), (.x15, 0xae000)]
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

end SigGolfCandidate.T3M.Nonbinary.InlineTail.Merkle
