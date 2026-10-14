import SigGolfCandidate.T3M.Verify.LayerRuns

/-! Campaign S1 code model of the Merkle path routines.

Every routine starts with the 2-word entry `addi a2,..; ecall` (the leaf hash; second top half: the stub `j` and
`addi a2,a2,D`). Level blocks (`mkWords` words, ending with the fold's ecall):
* lower layers (lay 1..3): level 0 `li a1,64; slli t3,t6,16; ld gp,HDR(s1); or t3,t3,gp; addi a0,s6,B; addi gp,t3,h-1;
  sd gp,16(a0); addi a2,s6,wa; ecall`, levels `1..h-2`: `addi a0,s6,B; addi gp,t3,h-1; sd gp,16(a0); addi a2,s6,wa; ecall`,
  L1 additionally `addi s0,a0,X` (top-chain anchor) right after `addi a0` at level `lminTab leaf`; the root fold (level
  `h-1`) is the next layer's encoding block (`trPc`).
* top first half (levels 0..5, s0-relative): `li a1,64` (level 0 only), `addi a0,s0,B; srli gp,s7,5+l; sd gp,16(a0);
  addi a2,s0,wa; ecall`, level 5 ends with `jalr zero,OFF(s7)` (stub `j` to the second half, `addi a2,a2,D`).
* top second half (levels 6..11, a2-relative): `addi a0,a2,16|-48; (li gp,heap; sd gp,16(a0) | sd REG,16(a0));
  addi a2,a0,d; ecall` (no `addi a2` at level 11: the root is written at node 11's write address).
Left nodes (bit 0) are the HIGH half of their answer: written at `mkWa = slot - 16`; right nodes at `mkWa = slot`.
One-word labels (bytes 16..24); bytes 24..48 stay witness (`wmerkleHigh`, `wmerklePad`). -/
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
  if lay = 3 then 133760 + 128 * sh else if lay = 2 then 141952 + 128 * sh
  else if lay = 1 then 1024 + 1024 * sh else if ci = 0 then 142032 + 128 * sh else 133840 + 128 * sh
def lminTab : List Nat := [0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5]
/-- L1: the level whose block sets `s0` (lowest non-root window). -/
def mkS0 (lay sh : Nat) : Nat := if lay = 1 then lminTab.getD sh 0 else 99
def mkSx (lay sh kk : Nat) : Nat := if lay = 1 ∧ kk = mkS0 lay sh then 1 else 0
def mkWords (lay ci sh kk : Nat) : Nat :=
  if lay = 0 then
    (if ci = 0 then (if kk = 0 then 6 else if kk = 5 then 4 else 5)
     else (if kk < 3 then 5 else if kk < 5 then 4 else 3))
  else (if kk = 0 then 9 else 5) + mkSx lay sh kk
def mkOff (lay ci sh : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci sh kk + mkWords lay ci sh kk
/-- Window offset of level `l` inside the layer's path area (top: VER two-line plan, lower: plan slots). -/
def mkPath (lay leaf l : Nat) : Nat := if lay = 0 then ClaudeWCT.W9.T3M.topPlan leaf l else 16 * plan lay leaf l
def mkBo (lay leaf l : Nat) : Nat := mkBase lay + mkPath lay leaf l
def mkBlk (lay leaf l : Nat) : Nat := 0x4c0 + mkBo lay leaf l
def mkBit (leaf l : Nat) : Nat := leaf / 2 ^ l % 2
/-- Node slot of the level-`l` input node (left: window start, right: window + 48). -/
def mkCur (lay leaf l : Nat) : Nat := mkBlk lay leaf l + 48 * mkBit leaf l
/-- Write address of the level-`l` input node (left nodes keep the high half: 16 below the slot). -/
def mkWa (lay leaf l : Nat) : Nat := mkBlk lay leaf l + 64 * mkBit leaf l - 16
/-- Representative leaf of chunk pattern `sh` (the chunk's bits at their place, other bits 0). -/
def mkLeafOf (lay ci sh : Nat) : Nat := sh * 2 ^ mkLo lay ci
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then mkWa 0 leaf 11 else 256
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2),
    (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x5, 0)] ++
    (if lay = 0 then [] else [(.x9, BitVec.ofNat 64 TOPB9)])
def mkKc (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2),
    (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x5, 0)]
def mkKeep : List Reg := [.x4, .x1, .x2, .x16, .x17, .x9, .x24, .x23, .x6, .x25, .x27, .x29, .x31]
def mkEntSpec (lay ci sh : Nat) : Spec := let st := if lay = 0 ∧ ci = 1 then 2 else 1; ⟨[], [], mkShp lay ci sh + 1, true, st, [], none, st⟩
def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x12, BitVec.ofNat 64 (mkWa lay (mkLeafOf lay ci sh) (mkLo lay ci)))]
def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14, .x4, .x28, .x8]
/-- The top second half starts from node 5's write address, the constant `P = 448` of the line-A table. -/
def mkP5 : Nat := 0x4c0 + 8256 + 448
def mkEntK (lay ci : Nat) : List (Reg × Word) :=
  mkKc lay ++ (if lay = 0 ∧ ci = 1 then [(.x12, BitVec.ofNat 64 mkP5)] else [])
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] baseK (mkEntK lay ci) [] (mkTabW lay ci sh) [] (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def t3E (l' : Nat) : E := .bin .or (.bin .sll (.reg .x31) (kw 16)) (.ld (kw (hdrA l')))
def mkHdrE (lay l : Nat) : E := if lay = 0 then kw 64 else if l = 0 then t3E (lay - 1) else .reg .x28
/-- The one-word label: top `heap` (first half `srli gp,s7,l+5`, second half a constant), lower `t3 + heap - 1`. -/
def mkLabelE (lay ci sh l : Nat) : E :=
  if lay = 0 then (if ci = 0 then .bin .srl (.reg .x23) (kw (l + 5)) else kw (mkHeap lay ci sh l))
  else addC (mkHdrE lay l) (BitVec.ofNat 64 (mkHeap lay ci sh l - 1))
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) l + 16)⟩, mkLabelE lay ci sh l)]
def mkLvlRegs (lay l : Nat) : List (Reg × E) := if l = 0 ∧ lay ≠ 0 then [(.x28, t3E (lay - 1))] else []
def mkLvlKeep (lay l : Nat) : List Reg := if l = 0 ∧ lay ≠ 0 then [] else [.x28]
def mkLvlAllow (lay sh l : Nat) : List Nat := [mkBlk lay sh l + 16]
def mkDispTgt (sh : Nat) : E :=
  .bin .and (addC (.reg .x23) (BitVec.ofNat 64 1432 - BitVec.ofNat 64 (16 * sh))) (.c (~~~1#64))
def mkBody (lay ci sh kk : Nat) : Nat := mkWords lay ci sh kk - 1
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkWa lay (mkLeafOf lay ci sh) (mkLo lay ci + kk + 1)
  else mkWa lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk),
    mkShp lay ci sh + mkOff lay ci sh (kk + 1) + 1, true, mkBody lay ci sh kk, [], none, mkBody lay ci sh kk⟩
def mkLvlSpecD (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk), 0, false,
    mkWords lay ci sh kk, [], some (mkDispTgt sh), mkWords lay ci sh kk⟩
def mkLvlK (lay l : Nat) : List (Reg × Word) := if l = 0 then mkK lay else mkKc lay ++ [(.x11, 64)]
/-- L1 sets `s0` at level `mkS0`. -/
def mkS0Post (lay sh kk : Nat) : List (Reg × Word) := if lay = 1 ∧ kk = mkS0 lay sh then [(.x8, BitVec.ofNat 64 s3v)] else []
def mkS0Keep (lay sh kk : Nat) : List Reg := if lay = 1 ∧ kk = mkS0 lay sh then [] else [.x8]
def mkLvlPostN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))] ++ mkS0Post lay sh kk
def mkLvlPostD (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) (mkLo lay ci + kk))), (.x7, 1),
    (.x12, BitVec.ofNat 64 mkP5)]
def mkLvlKN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkLvlK lay (mkLo lay ci + kk) ++
    (if lay = 0 ∧ ci = 1 then
      [(.x12, BitVec.ofNat 64 (mkWa lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)))] else []) ++
    (if lay = 0 ∧ ci = 0 ∧ kk = 5 then [(.x12, BitVec.ofNat 64 mkP5)] else [])
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] baseK
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci sh kk + 2) []
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk)
    (mkKeep ++ (.x14 :: mkLvlKeep lay (mkLo lay ci + kk)) ++ mkS0Keep lay sh kk)
def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] baseK
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci sh kk + 2) [.jmp]
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci sh kk) (mkKeep ++ mkLvlKeep lay (mkLo lay ci + kk) ++ [.x8])
def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then mkLvlCheckD lay ci sh kk else mkLvlCheckN lay ci sh kk
def cmpPc (c : Nat) : Nat := 133868 + 128 * c
def cmpDst (c : Nat) : Nat := mkWa 0 (64 * c) 11
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
