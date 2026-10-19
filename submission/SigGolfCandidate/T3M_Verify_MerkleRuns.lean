import SigGolfCandidate.T3M_Verify_LayerRuns

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
def mkTab (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 133840 else stabIdx lay
def mkTabW (lay ci sh : Nat) : Nat := if lay = 0 ∧ ci = 1 then 15718 + 256 * sh else stabW lay sh
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 133764 + 128 * sh else if lay = 2 then 141956 + 128 * sh
  else if lay = 1 then 1028 + 1024 * sh else if ci = 0 then 142032 + 128 * sh else 133840 + 128 * sh
/-- C2: every lower fold writes its packed tweak word from an immediate (`addi gp,t3,K; sd gp,16(a0)`), so it costs
like the old register-heap levels; the top tree keeps register heaps on its last three levels only. -/
def mkReg (lay l : Nat) : Bool := decide (lay ≠ 0 ∨ hL lay ≤ l + 3)
/-- Words of the level-`l` block (its ecall included). C4 top: one label store per level (`srli gp,s7,5+l; sd gp,16(a0)`
in the lower copy, `addi gp,zero,heap; sd gp,16(a0)` or `sd REG,16(a0)` in the upper copy); the last level (11) counts
a virtual `addi a2` (`mkMove 0 11 = 0`). -/
def mkWords (lay l : Nat) : Nat :=
  (if l = 0 then (if lay = 0 then 5 else 9) else (if lay = 0 then 4 else 5)) + (if mkReg lay l then 0 else 1)
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
/-- C4: every layer (the top included) places its windows by the plan (`plan 0` = the two-line top plan). -/
def mkBo (lay leaf l : Nat) : Nat := mkBase lay + 16 * plan lay leaf l
def mkBlk (lay leaf l : Nat) : Nat := 0x1020 + mkBo lay leaf l
/-- Position of the value a level reads as its current input (left slot for bit 0, right slot for bit 1). -/
def mkVal (lay leaf l b : Nat) : Nat := mkBlk lay leaf l + 48 * b
/-- Hash destination (`a2`) feeding level `l`: the value position, except that a left child (C2, and C4 on the top:
HIGH half) is written 16 bytes earlier so that its high half lands in the left slot. -/
def mkCur (lay leaf l b : Nat) : Nat := mkVal lay leaf l b + 16 * b - 16
/-- Representative leaf of chunk pattern `sh` (C4: the top's upper copies are indexed by `leaf / 64`). -/
def mkLeafOf (lay ci sh : Nat) : Nat := sh * 2 ^ mkLo lay ci
/-- C4: the top root is the low half of the last fold's answer, written where node 11's input was delivered. -/
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then mkCur 0 leaf 11 (leaf / 2048 % 2) else 256
def mkMove (lay level : Nat) : Nat := if lay = 0 ∧ level = 11 then 0 else 1
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2),
    (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x5, 0)] ++
    (if lay = 0 then [] else [(.x9, BitVec.ofNat 64 TOPB9)])
def mkKc (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2),
    (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x5, 0)]
def mkKeep : List Reg := [.x4, .x1, .x2, .x16, .x17, .x8, .x9, .x24, .x23, .x6, .x25, .x27, .x29, .x31]
def mkEntSpec (lay ci sh : Nat) : Spec := let st := if lay = 0 ∧ ci = 1 then 2 else 1; ⟨[], [], mkShp lay ci sh + 1, true, st, [], none, st⟩
def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x12, BitVec.ofNat 64 (mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci) (sh % 2)))]
def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14, .x4, .x28]
def mkEntK (lay ci : Nat) : List (Reg × Word) :=
  mkKc lay ++ (if lay = 0 ∧ ci = 1 then [(.x10, BitVec.ofNat 64 (mkBlk 0 0 5))] else [])
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] baseK (mkEntK lay ci) [] (mkTabW lay ci sh) [] (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 5)) else kw (mkHeap lay ci sh l)
def t3E (l' : Nat) : E := .bin .or (.bin .sll (.reg .x31) (kw 16)) (.ld (kw (hdrA l')))
def mkHdrE (lay l : Nat) : E := if lay = 0 then kw 64 else if l = 0 then t3E (lay - 1) else .reg .x28
/-- C2 lower fold constant `K heap = mkK7 + heap` (= `WCT9.lowerK`). -/
def mkK7 : Nat := 1407
/-- C2: lower levels write only the packed tweak word `hyperWord + mkK7 + heap`; its high word is witness memory.
C4: a top level writes only its one-word label, the heap. -/
def mkLabE (lay ci sh l : Nat) : E :=
  if lay = 0 then mkHeapE lay ci sh l else addC (mkHdrE lay l) (BitVec.ofNat 64 (mkK7 + mkHeap lay ci sh l))
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) l + 16)⟩, mkLabE lay ci sh l)]
def mkLvlRegs (lay l : Nat) : List (Reg × E) := if l = 0 ∧ lay ≠ 0 then [(.x28, t3E (lay - 1))] else []
def mkLvlKeep (lay l : Nat) : List Reg := if l = 0 ∧ lay ≠ 0 then [] else [.x28]
def mkLvlAllow (lay sh l : Nat) : List Nat := [mkBlk lay sh l + 16, mkBlk lay sh l + 24]
def mkDispTgt (sh : Nat) : E :=
  .bin .and (addC (.reg .x23) (BitVec.ofNat 64 1432 - BitVec.ofNat 64 (16 * sh))) (.c (~~~1#64))
def mkBody (lay l : Nat) : Nat :=
  (if l = 0 then (if lay = 0 then 2 else 6) else (if lay = 0 then 1 else 2)) + (if mkReg lay l then 1 else 2)
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2)
  else if lay = 0 then mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci + kk) (sh / 2 ^ kk % 2) else 256
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
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))]
def mkLvlPostD (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) (mkLo lay ci + kk))), (.x7, 1)]
def mkLvlKN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkLvlK lay (mkLo lay ci + kk) ++
    (if lay = 0 then
      [(.x12, BitVec.ofNat 64 (mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci + kk) (sh / 2 ^ kk % 2)))] else [])
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] baseK
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) []
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk) (mkKeep ++ (.x14 :: mkLvlKeep lay (mkLo lay ci + kk)))
def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] baseK
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [.jmp]
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci sh kk) (mkKeep ++ mkLvlKeep lay (mkLo lay ci + kk))
def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then mkLvlCheckD lay ci sh kk else mkLvlCheckN lay ci sh kk
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh && (List.range (mkBits lay ci)).all (mkLvlCheck lay ci sh)
def mkChunkCheck (lay ci lo n : Nat) : Bool := (List.range' lo n).all (mkBlockCheck lay ci)
/-- C4: the root compare moved up 6 words (`133868 + 128 c`) and reads the root where upper copy `c` wrote it. -/
def cmpPc (c : Nat) : Nat := 133868 + 128 * c
def cmpDst (c : Nat) : Nat := 11792 + 16 * topRootSlot.getD c 0
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
