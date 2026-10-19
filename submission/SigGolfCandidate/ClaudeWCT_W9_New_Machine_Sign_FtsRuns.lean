import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_Common

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def runA (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux { noAlias := true } look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
def cE (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldc (a : Nat) : E := .ld (cE a)
def mwc (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def regsOf (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def pres2 (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ecall : Bool) (k cyc : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ecall, k, cyc, brs, none⟩
def pres (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ecall : Bool) (k : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ecall, k, k, brs, none⟩
def qI (c i : Nat) : Nat := qIdx.getD (6 * c + i) 0
def chkI (c i s : Nat) : Nat := chkIdx.getD (30 * c + 5 * i + s) 0
def skipI (c i s : Nat) : Nat := skipIdx.getD (30 * c + 5 * i + s) 0
def leafI (c : Nat) : Nat := leafIdx.getD c 0
def lI (c : Nat) : Nat := lIdx.getD c 0
def tI (c : Nat) : Nat := tIdx.getD c 0
def nodeI (c : Nat) : Nat := nodeIdx.getD c 0
def ntI (c : Nat) : Nat := ntIdx.getD c 0
def rI (c : Nat) : Nat := rIdx.getD c 0
def lwuI (c : Nat) : Nat := lwuIdx.getD c 0
def pcI (c l : Nat) : Nat := rI c + 12 + 13 * l
def lcEnd (c i : Nat) : Nat := if i = 5 then lI c else qI c (i + 1)
def hdr8 (c : Nat) : Nat := 2049 + 65536 * c
def hdr6 (c : Nat) : Nat := 1537 + 65536 * c
/-- FTS chain word constant. C4 (FTS coordinate + 1, as b3cc11b's campaign S2): coordinate nibble `c + 1`. -/
def chainK (c i : Nat) : Nat := 0x80 + 4 * i + 65536 * (c + 1)
def nodeK (c : Nat) : Nat := 769 + 65536 * (4 + c)
def slotV (c i : Nat) : Nat := SIG + 16 + 208 * c + 16 * i
def slotP (c l : Nat) : Nat := SIG + 112 + 208 * c + 16 * l
def leafOff (i : Nat) : Nat := if i = 0 then 0 else 16 * (i + 2)
def forOff (c : Nat) : Nat := 32 + 32 * c
def w1E : E := .bin .or (.bin .sll (.reg .x18) (cE 32)) (.reg .x22)
def qE (c i : Nat) : E := .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (chainK c i))
def idx32E : E := .bin .sll (.reg .x22) (cE 32)
/-- FTS node word base. C4: coordinate nibble `c + 1`; coordinate 0 goes through the arena trampoline
`lui t2,16; or t1,t1,t2; ori t1,t1,1537`, which produces the same expression. -/
def nodeLoE (c : Nat) : E := .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (cE (65536 * (c + 1)))) (cE 1537)
/-- FTS leaf word. C4: coordinate nibble `c + 1`; for coordinate 0 the arena trampoline ORs `65536` and `1537`
separately. -/
def leafLoE (c : Nat) : E :=
  if c = 0 then
    .bin .or (.bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE 65536)) (cE 1537)
  else .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (1537 + 65536 * (c + 1)))
def leafX7 (c : Nat) : E := if c = 0 then cE 65536 else cE (65536 * (c + 1) + 1537)
def x29A (off : Nat) : Addr := ⟨some (.reg .x29), BitVec.ofNat 64 off⟩
def nodeLo7 (c index : Nat) : Nat := 1537 + 65536 * (c + 1) + 2 ^ 27 * index
def leafLo7 (c index j : Nat) : Nat := 1537 + 65536 * (c + 1) + 2 ^ 20 * j + 2 ^ 27 * index
def dE (i : Nat) : E := .bin .sub (cE 4) (.bin .and (.bin .srl (.reg .x25) (cE (3 * i))) (cE 7))
def x18p1 : E := .bin .add (.reg .x18) (cE 1)
def x18m1 : E := .bin .add (.reg .x18) (cE (2 ^ 64 - 1))
def heapLeafE : E := .bin .sll (.bin .add (.reg .x18) (cE 128)) (cE 4)
def sh5 : E := .bin .sll (.reg .x18) (cE 5)
def sh4 : E := .bin .sll (.reg .x18) (cE 4)
def pathE (l : Nat) : E := .bin .sll (.bin .xor (.bin .srl (.bin .add (.reg .x24) (cE 128)) (cE l)) (cE 1)) (cE 4)
def fdw (c : Nat) : Nat := WCT9.childBase c / 64
def fsh (c : Nat) : Nat := [0,0,21,36,0,21,36,0,21].getD c 0
def fhas (c : Nat) : Bool := c % 3 != 1
def fsrcE (c : Nat) : E :=
  if fhas c then .bin .srl (ldc (NBUF + 8 * fdw c)) (cE (fsh c)) else ldc (NBUF + 8 * fdw c)
def fchildE (c : Nat) : E := if c = 3 ∨ c = 6 then .bin .srl (fsrcE c) (cE 21) else .bin .and (fsrcE c) (cE 127)
def fieldE (c : Nat) : E := .bin .and (.bin .srl (fsrcE c) (cE 7)) (cE 1023)
def expF (c : Nat) : PRes :=
  pres [(.x6, .bin .sll (fieldE c) (cE 2)), (.x24, fchildE c), (.x25, fieldE c),
    (.x28, .bin .add (.bin .sll (fieldE c) (cE 2)) (cE TBL))] [] [] (lwuI c) false
    (if fhas c then 13 else 12) []
def expChk (c i s v : Nat) : PRes :=
  if v = 0 then pres [] [] [] (skipI c i s) false 1 [⟨.ne, .reg .x18, .reg .x24, true⟩]
  else if v = 1 then
    pres [(.x6, cE s)] [] [] (skipI c i s) false 3 [⟨.ne, .reg .x26, cE s, true⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
  else
    pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE (slotV c i))]
      [mwc (slotV c i + 8) (ldc (CHAINW + 56)), mwc (slotV c i) (ldc (CHAINW + 48))] [] (skipI c i s) false 11
      [⟨.ne, .reg .x26, cE s, false⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
def expStp (c i s : Nat) : PRes :=
  pres [(.x6, cE (s - 1)), (.x10, cE CHAINW), (.x11, cE 64), (.x12, cE (CHAINW + 48)), (.x29, cE CHAINW)]
    [mwc (CHAINW + 16) (.bin (.st .b 1) (ldc (CHAINW + 16)) (cE (s - 1)))] [] (chkI c i s - 1) true 9 []
def expLc (c i : Nat) : PRes :=
  pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE LEAFW)]
    [mwc (LEAFW + leafOff i + 8) (ldc (CHAINW + 56)), mwc (LEAFW + leafOff i) (ldc (CHAINW + 48))] []
    (lcEnd c i) false 8 []
/-- Nested FTS (r1-1): the leaf pad word `off` of coordinate `c`, i.e. `L_{c-1}` from the previous forest pair. -/
def padE (c off : Nat) : E := if c = 0 then cE 0 else ldc (FORW + forOff (c - 1) + off)
def expL (c : Nat) : PRes :=
  pres [(.x6, heapLeafE), (.x7, leafX7 c), (.x10, cE LEAFW), (.x11, cE 128), (.x12, .bin .add heapLeafE (cE HEAPW))]
    [(x29A 24, cE 0), (x29A 16, leafLoE c), (x29A 40, padE c 8), (x29A 32, padE c 0)]
    ([.valid (x29A 24) 8, .valid (x29A 16) 8, .valid (x29A 40) 8] ++
      (if c = 0 then [] else [.ne ⟨none, BitVec.ofNat 64 (FORW + forOff (c - 1) + 8)⟩ (x29A 32)]) ++
      [.valid (x29A 32) 8]) (tI c - 1) true
    (if c = 0 then 21 else 23) []
def expT (c : Nat) (back : Bool) : PRes :=
  if back then pres [(.x6, cE 128), (.x18, x18p1)] [] [] (leafI c) false 3 [⟨.ltu, x18p1, cE 128, true⟩]
  else pres [(.x6, cE 128), (.x18, cE 127)] [] [] (nodeI c) false 4 [⟨.ltu, x18p1, cE 128, false⟩]
def nodeLd (off : Nat) : E := .ld (.bin .add sh5 (cE (HEAPW + off)))
def nodeAddr (off : Nat) : Addr := ⟨some sh5, BitVec.ofNat 64 (HEAPW + off)⟩
def nodeX7 (c : Nat) : E := cE (65536 * (c + 1))
/-- Packed node tweak (heaps `8..127`): high word `[h < 8] * h`, low word `nodeLo7 + [h < 8] * h - h`. -/
def nodeHiE : E := .bin .mul (.bin .sltu (.reg .x18) (cE 8)) (.reg .x18)
def nodeDE : E := .bin .sub nodeHiE (.reg .x18)
def nodeLoNE (c : Nat) : E := .bin .add (nodeLoE c) nodeDE
def expN (c : Nat) : PRes :=
  pres2 [(.x6, nodeLoNE c), (.x7, nodeDE), (.x10, cE NODEW), (.x11, cE 64), (.x12, cE NOUTW),
    (.x28, .bin .add sh5 (cE HEAPW)), (.x29, nodeHiE)]
    [mwc (NODEW + 24) nodeHiE, mwc (NODEW + 16) (nodeLoNE c), mwc (NODEW + 56) (nodeLd 24),
      mwc (NODEW + 48) (nodeLd 16), mwc (NODEW + 8) (nodeLd 8), mwc NODEW (nodeLd 0)]
    [.ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 NODEW⟩, .ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩,
      .valid (nodeAddr 24) 8, .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 NODEW⟩,
      .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩, .valid (nodeAddr 16) 8, .valid (nodeAddr 8) 8,
      .valid (nodeAddr 0) 8]
    (ntI c - 1) true (if c = 0 then 29 else 25) (if c = 0 then 32 else 28) []
def heapAddr (off : Nat) : Addr := ⟨some sh4, BitVec.ofNat 64 (HEAPW + off)⟩
/-- Nested FTS (r1-1): the fold output half, `16 * [heap < 4]` (heaps 2 and 3 keep the HIGH half). -/
def hiSelE : E := .bin .sll (.bin .sltu (.reg .x18) (cE 4)) (cE 4)
def outE : E := .bin .add hiSelE (cE NOUTW)
def outAddr (off : Nat) : Addr := ⟨some hiSelE, BitVec.ofNat 64 (NOUTW + off)⟩
def outLd (off : Nat) : E := .ld (.bin .add hiSelE (cE (NOUTW + off)))
/-- Fold post-hash kind for `c >= 1`: 0 = heap other than 4 and 2, 1 = heap 4 (pad := R_{c-1}), 2 = heap 2 (pad := 0). -/
def ntDirs (c kd : Nat) (back : Bool) : List Dir :=
  if c = 0 then [.br back] else if kd = 1 then [.br false, .br back] else if kd = 2 then [.br true, .br false, .br back]
  else [.br true, .br true, .br back]
def ntPadMem (c kd : Nat) : SymMem :=
  if c = 0 then [] else if kd = 1 then
    [mwc (NODEW + 40) (ldc (FORW + forOff (c - 1) + 24)), mwc (NODEW + 32) (ldc (FORW + forOff (c - 1) + 16))]
  else if kd = 2 then [mwc (NODEW + 40) (cE 0), mwc (NODEW + 32) (cE 0)] else []
def ntOutObl (c kd : Nat) : List Oblig :=
  if c = 0 ∨ kd = 0 then [.valid (outAddr 8) 8, .valid (outAddr 0) 8]
  else [.ne (outAddr 8) ⟨none, BitVec.ofNat 64 (NODEW + 32)⟩, .ne (outAddr 8) ⟨none, BitVec.ofNat 64 (NODEW + 40)⟩,
    .valid (outAddr 8) 8, .ne (outAddr 0) ⟨none, BitVec.ofNat 64 (NODEW + 32)⟩,
    .ne (outAddr 0) ⟨none, BitVec.ofNat 64 (NODEW + 40)⟩, .valid (outAddr 0) 8]
def ntBrs (c kd : Nat) : List Br :=
  if c = 0 then [] else if kd = 1 then [⟨.ne, .reg .x18, cE 4, false⟩]
  else if kd = 2 then [⟨.ne, .reg .x18, cE 2, false⟩, ⟨.ne, .reg .x18, cE 4, true⟩]
  else [⟨.ne, .reg .x18, cE 2, true⟩, ⟨.ne, .reg .x18, cE 4, true⟩]
def expNT (c kd : Nat) (back : Bool) : PRes :=
  pres [(.x6, cE 1), (.x7, outLd 8), (.x18, x18m1), (.x28, outE),
    (.x29, .bin .add sh4 (cE HEAPW))]
    ([(heapAddr 8, outLd 8), (heapAddr 0, outLd 0)] ++ ntPadMem c kd)
    ([.valid (heapAddr 8) 8, .valid (heapAddr 0) 8] ++ ntOutObl c kd)
    (if back then nodeI c else rI c) false (if c = 0 then 18 else if kd = 0 then 22 else 25)
    (⟨.ne, x18m1, cE 1, back⟩ :: ntBrs c kd)
def expR0 (c : Nat) : PRes :=
  pres [(.x6, ldc (HEAPW + 48)), (.x7, ldc (HEAPW + 56)), (.x28, cE (HEAPW + 32)), (.x29, cE (FORW + forOff c))]
    [mwc (FORW + forOff c + 24) (ldc (HEAPW + 56)), mwc (FORW + forOff c + 16) (ldc (HEAPW + 48)),
      mwc (FORW + forOff c + 8) (ldc (HEAPW + 40)), mwc (FORW + forOff c) (ldc (HEAPW + 32))] [] (pcI c 0) false 12 []
def pathAddr (l off : Nat) : Addr := ⟨some (pathE l), BitVec.ofNat 64 (HEAPW + off)⟩
def pathLd (l off : Nat) : E := .ld (.bin .add (pathE l) (cE (HEAPW + off)))
def expPC (c l : Nat) : PRes :=
  pres [(.x6, pathLd l 0), (.x7, pathLd l 8), (.x28, .bin .add (pathE l) (cE HEAPW)), (.x29, cE (slotP c l))]
    [mwc (slotP c l + 8) (pathLd l 8), mwc (slotP c l) (pathLd l 0)] [.valid (pathAddr l 8) 8, .valid (pathAddr l 0) 8]
    (pcI c (l + 1)) false 13 []
def expSK : PRes :=
  pres [(.x6, ldc 0x90), (.x7, ldc 0x98), (.x28, cE 0x80), (.x29, cE PRIVW)]
    [mwc (PRIVW + 40) (ldc 0x98), mwc (PRIVW + 32) (ldc 0x90), mwc (PRIVW + 8) (ldc 0x88), mwc PRIVW (ldc 0x80)] []
    (fieldIdx.getD 0 0) false 11 []
/-- Nested FTS (r1-1): the forest hash is replaced by copying `(L8, R8)` to `FOUT` and the encoding R slot. -/
def expFor : PRes :=
  pres [(.x6, ldc (FORW + forOff 8 + 16)), (.x7, ldc (FORW + forOff 8 + 24)), (.x28, cE PRIVW), (.x29, cE 0x20000)]
    [mwc (0x20290 + 8) (ldc (FORW + forOff 8 + 24)), mwc 0x20290 (ldc (FORW + forOff 8 + 16)),
      mwc (FOUT + 8) (ldc (FORW + forOff 8 + 8)), mwc FOUT (ldc (FORW + forOff 8))] [] 370 false 12 []
def expJ : PRes := pres [] [] [] 370 false 1 []
def runF (c : Nat) : Option PRes := run (coordLook c) [lwuI c] (cbase c) []
def chkDirs (v : Nat) : List Dir := if v = 0 then [.br true] else if v = 1 then [.br false, .br true] else [.br false, .br false]
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 4) []
def runL (c : Nat) : Option PRes := runA (coordLook c) [] (lI c) []
def runT (c : Nat) (back : Bool) : Option PRes := run (coordLook c) [leafI c, nodeI c] (tI c) [.br back]
def runN (c : Nat) : Option PRes := runA (coordLook c) [] (nodeI c) []
def runNT (c kd : Nat) (back : Bool) : Option PRes := runA (coordLook c) [nodeI c, rI c] (ntI c) (ntDirs c kd back)
def runR0 (c : Nat) : Option PRes := run (coordLook c) [pcI c 0] (rI c) []
def runPC (c l : Nat) : Option PRes := run (coordLook c) [pcI c (l + 1)] (pcI c l) []
def runSK : Option PRes := run headLook [fieldIdx.getD 0 0] 11175 []
def runFor : Option PRes := run forLook [370] 20715 []
def runJ : Option PRes := run tailLook [370] 20729 []
/-! ### Stage A (campaign X1): coefficient prologue, call sites and the shared GF(2^128) Horner routine HORN -/
def paIdx : List Nat := [11962,13021,14081,15141,16200,17260,18320,19379,20439]
def paI (c : Nat) : Nat := paIdx.getD c 0
def ecI (c : Nat) : Nat := paI c - 1
def hornI : Nat := 11368
def hkI : Nat := 11220
def hbI : Nat := 11226
def hfI : Nat := 11374
def orIdx : E := .bin .or (cE 0) (.reg .x22)
def x7p1 : E := .bin .add (.reg .x7) (cE 1)
def pairWE : E := .bin .or (.bin .sll x7p1 (cE 32)) (.reg .x22)
def expZ (c : Nat) : PRes :=
  pres [(.x6, orIdx), (.x7, cE 0), (.x10, cE PRIVW), (.x11, cE 64), (.x12, cE COEF), (.x29, cE PRIVW)]
    [mwc (PRIVW + 24) orIdx, mwc (PRIVW + 16) (cE (hdr8 c))] [] (ecI c) true 14 []
def expCL (c : Nat) (b : Bool) : PRes :=
  if b then
    pres [(.x6, pairWE), (.x7, x7p1), (.x10, cE PRIVW), (.x11, cE 64), (.x12, .bin .add (.reg .x12) (cE 32)),
      (.x29, cE PRIVW)] [mwc (PRIVW + 24) pairWE] [] (ecI c) true 10 [⟨.ne, x7p1, cE 27, true⟩]
  else
    pres [(.x6, cE 27), (.x7, x7p1), (.x12, .bin .add (.reg .x12) (cE 32)), (.x18, cE 0)] [] [] (leafI c) false 6
      [⟨.ne, x7p1, cE 27, false⟩]
def ptE (i : Nat) : E :=
  .bin .add (.bin .sll (.bin .add (.bin .sll (.reg .x18) (cE 1)) (.reg .x18)) (cE 1)) (cE (i + 1))
def retW (c i : Nat) : Nat := 0x1000 + 4 * (qI c i + 5)
def expQ (c i : Nat) : PRes := pres [(.x1, cE (retW c i)), (.x6, ptE i)] [] [] hornI false 5 []
def expS (c i : Nat) : PRes :=
  pres [(.x6, cE 4), (.x7, cE (chainK c i)), (.x26, dE i), (.x29, cE CHAINW)]
    [mwc (CHAINW + 24) (cE 0), mwc (CHAINW + 16) (qE c i)] [] (chkI c i 0) false (if c = 0 then 17 else 15) []
def expH0 : PRes := pres [(.x7, cE (COEF + 864)), (.x10, cE 0), (.x11, cE 0), (.x28, cE COEF)] [] [] hkI false 6 []
def expHK : PRes :=
  pres [(.x7, .bin .add (.reg .x7) (cE (2 ^ 64 - 16))), (.x12, cE 0), (.x13, cE 0), (.x14, cE 0), (.x15, cE 0),
    (.x16, .reg .x6)] [] [] hbI false 6 []
def sh1 (r : Reg) : E := .bin .sll (.reg r) (cE 1)
def hi63 (r : Reg) : E := .bin .srl (.reg r) (cE 63)
def xr (a b : Reg) : E := .bin .xor (.reg a) (.reg b)
def hbShift : List (Reg × E) :=
  [(.x10, sh1 .x10), (.x11, .bin .or (sh1 .x11) (hi63 .x10)), (.x12, .bin .or (sh1 .x12) (hi63 .x11)),
    (.x16, .bin .srl (.reg .x16) (cE 1)), (.x17, hi63 .x10)]
def expHB (b1 b2 : Bool) : PRes :=
  pres ((if b1 then [] else [(.x13, xr .x13 .x10), (.x14, xr .x14 .x11), (.x15, xr .x15 .x12)]) ++ hbShift) [] []
    (if b2 then hbI else hfI) false ((if b1 then 11 else 14) + (if b2 then 0 else 1))
    [⟨.ne, .bin .srl (.reg .x16) (cE 1), cE 0, b2⟩, ⟨.eq, .bin .and (.reg .x16) (cE 1), cE 0, b1⟩]
def shE (r : Reg) (k : Nat) : E := .bin .sll (.reg r) (cE k)
def foldE : E := .bin .xor (.bin .xor (.bin .xor (.bin .xor (.reg .x13) (shE .x15 1)) (shE .x15 2)) (shE .x15 7)) (.reg .x15)
def c0E : E := .ld (.reg .x7)
def c1E : E := .ld (.bin .add (.reg .x7) (cE 8))
def hfRegs : List (Reg × E) :=
  [(.x10, .bin .xor foldE c0E), (.x11, .bin .xor (.reg .x14) c1E), (.x13, foldE), (.x17, c1E)]
def hfObl : List Oblig := [.valid ⟨some (.reg .x7), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x7), 0⟩ 8]
def expHF (b : Bool) : PRes :=
  if b then pres hfRegs [] hfObl hkI false 12 [⟨.ne, .reg .x7, .reg .x28, true⟩]
  else ⟨⟨regsOf (hfRegs ++ [(.x29, cE CHAINW)]),
      [mwc (CHAINW + 56) (.bin .xor (.reg .x14) c1E), mwc (CHAINW + 48) (.bin .xor foldE c0E)], hfObl⟩,
    0, false, 17, 17, [⟨.ne, .reg .x7, .reg .x28, false⟩], some (.bin .and (.reg .x1) (cE (2 ^ 64 - 2)))⟩
def runZ (c : Nat) : Option PRes := run (coordLook c) [] (lwuI c + 1) []
def runCL (c : Nat) (b : Bool) : Option PRes := run (coordLook c) [leafI c] (paI c) [.br b]
def runQ (c i : Nat) : Option PRes := run (coordLook c) [hornI] (qI c i) []
def runS (c i : Nat) : Option PRes := run (coordLook c) [chkI c i 0] (qI c i + 5) []
def runH0 : Option PRes := run (coordLook 0) [hkI] hornI []
def runHK : Option PRes := run (coordLook 0) [hbI] hkI []
def runHB (b1 b2 : Bool) : Option PRes := run (coordLook 0) [hbI, hfI] hbI [.br b1, .br b2]
def runHF (b : Bool) : Option PRes := run (coordLook 0) [hkI] hfI (if b then [.br true] else [.br false, .jmp])
def okC (c : Nat) : Bool := optBeq (runCL c true) (expCL c true) && optBeq (runCL c false) (expCL c false)
def okQ (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runQ c i) (expQ c i)
def okS (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runS c i) (expS c i)
def okHorn : Bool :=
  optBeq runH0 expH0 && optBeq runHK expHK && optBeq (runHB true true) (expHB true true) &&
    optBeq (runHB true false) (expHB true false) && optBeq (runHB false true) (expHB false true) &&
    optBeq (runHB false false) (expHB false false) && optBeq (runHF true) (expHF true) &&
    optBeq (runHF false) (expHF false)
def okF (c : Nat) : Bool := optBeq (runF c) (expF c) && optBeq (runZ c) (expZ c)
def okChk (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range 5).all fun s => (List.range 3).all fun v =>
    optBeq (runChk c i s v) (expChk c i s v)
def okStp (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range' 1 4).all fun s => optBeq (runStp c i s) (expStp c i s)
def okLc (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runLc c i) (expLc c i)
def okTail (c : Nat) : Bool :=
  optBeq (runL c) (expL c) && optBeq (runT c true) (expT c true) && optBeq (runT c false) (expT c false) &&
    optBeq (runN c) (expN c) && optBeq (runNT c 0 true) (expNT c 0 true) &&
    optBeq (runNT c (if c = 0 then 0 else 2) false) (expNT c (if c = 0 then 0 else 2) false) &&
    optBeq (runNT c 1 true) (expNT c 1 true) &&
    optBeq (runR0 c) (expR0 c) && (List.range 7).all fun l => optBeq (runPC c l) (expPC c l)
def okCoord (c : Nat) : Bool := okF c && okC c && okQ c && okS c && okChk c && okStp c && okLc c && okTail c
def okGlobal : Bool := optBeq runSK expSK && optBeq runFor expFor && optBeq runJ expJ && okHorn
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-- The unchanged chain and coefficient region excludes the replaced field and leaf hooks. -/
def coordLookW (c n : Nat) : Option (BitVec 32) := (coordCodesW.getD c [])[n - cbase c]?
/-- Witness stack (charge 86): the installed coordinate windows (`coordCodesW`), the FTS G stubs at 21200..21229 and
the C4 arena. -/
def coordLook (c n : Nat) : Option (BitVec 32) :=
  if cbase c < n ∧ n < lI c then coordLookW c n
  else if 21200 ≤ n ∧ n < 21230 then ftsStub[n - 21200]? else arenaLook n
structure Fetch (im : Image) : Prop where
  head : LookOK im headLook
  coordinate : ∀ c, c < 9 → LookOK im (coordLook c)
theorem coordLook_ok {im : Image} (h : Fetch im) {c : Nat} (hc : c<9) : LookOK im (coordLook c) := h.coordinate c hc
theorem headLook_ok {im : Image} (h : Fetch im) : LookOK im headLook := h.head
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 4) []
def runZ (c : Nat) : Option PRes := run (coordLook c) [] (lwuI c + 1) []
def runCL (c : Nat) (b : Bool) : Option PRes := run (coordLook c) [leafI c] (paI c) [.br b]
def runQ (c i : Nat) : Option PRes := run (coordLook c) [hornI] (qI c i) []
def runS (c i : Nat) : Option PRes := run (coordLook c) [chkI c i 0] (qI c i + 5) []
def runH0 : Option PRes := run (coordLook 0) [hkI] hornI []
def runHK : Option PRes := run (coordLook 0) [hbI] hkI []
def runHB (b1 b2 : Bool) : Option PRes := run (coordLook 0) [hbI, hfI] hbI [.br b1, .br b2]
def runHF (b : Bool) : Option PRes := run (coordLook 0) [hkI] hfI (if b then [.br true] else [.br false, .jmp])
def okC (c : Nat) : Bool := optBeq (runCL c true) (expCL c true) && optBeq (runCL c false) (expCL c false)
def okQ (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runQ c i) (expQ c i)
def okS (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runS c i) (expS c i)
def okHorn : Bool :=
  optBeq runH0 expH0 && optBeq runHK expHK && optBeq (runHB true true) (expHB true true) &&
    optBeq (runHB true false) (expHB true false) && optBeq (runHB false true) (expHB false true) &&
    optBeq (runHB false false) (expHB false false) && optBeq (runHF true) (expHF true) &&
    optBeq (runHF false) (expHF false)
def okChk (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range 5).all fun s => (List.range 3).all fun v =>
    optBeq (runChk c i s v) (expChk c i s v)
/-! Witness stack: FTS G chains 1, 3. The HASH site `lui a0` becomes `jal t3,stub`; the stub copies the header to
`CHAINW+64`, zeroes `CHAINW+80..111`, hashes `CHAINW+48..111` into `CHAINW+32` (interior: the high half lands on the
value slot `CHAINW+48`) or `CHAINW+48` (terminal step, low half), zeroes `CHAINW+32/40` and returns to the site + 6. -/
def stubAt (s : Nat) : Nat := if s = 4 then 21215 else 21200
def stubOut (s : Nat) : Nat := if s = 4 then CHAINW + 48 else CHAINW + 32
def hdrE (s : Nat) : E := .bin (.st .b 1) (ldc (CHAINW + 16)) (cE (s - 1))
def expStpG (c i s : Nat) : PRes :=
  pres [(.x6, ldc (CHAINW + 24)), (.x10, cE (CHAINW + 48)), (.x11, cE 64), (.x12, cE (stubOut s)),
      (.x28, .c (pcOf (chkI c i s - 5))), (.x29, cE CHAINW)]
    [mwc (CHAINW + 104) (cE 0), mwc (CHAINW + 96) (cE 0), mwc (CHAINW + 88) (cE 0), mwc (CHAINW + 80) (cE 0),
      mwc (CHAINW + 72) (ldc (CHAINW + 24)), mwc (CHAINW + 64) (hdrE s), mwc (CHAINW + 16) (hdrE s)] []
    (stubAt s + 11) true 16 []
def knownG (c i s : Nat) : List (Reg × Word) := [(.x28, pcOf (chkI c i s - 5)), (.x29, BitVec.ofNat 64 CHAINW)]
def runPostG (c i s : Nat) : Option PRes :=
  pathAux scfg (coordLook c) [pcOf (chkI c i s)] 200 (pcOf (stubAt s + 12)) [] (σK (knownG c i s)) []
def expPostG (c i s : Nat) : PRes :=
  ⟨⟨RegFile.withKnown (knownG c i s), [mwc (CHAINW + 40) (cE 0), mwc (CHAINW + 32) (cE 0)], []⟩,
    pcOf (chkI c i s), false, 3, 3, [], none⟩
def okStp (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range' 1 4).all fun s =>
    if WCT9.ftsIsG i then optBeq (runStp c i s) (expStpG c i s) && optBeq (runPostG c i s) (expPostG c i s)
    else optBeq (runStp c i s) (expStp c i s)
def okLc (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runLc c i) (expLc c i)
def okCoord (c : Nat) : Bool := optBeq (runZ c) (expZ c) && okC c && okQ c && okS c && okChk c && okStp c && okLc c
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x20eb023,0x20eb423,0x1bb1313,0x1491393,0x730333,0xeeceb06f,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words1 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0xe0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x203b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words2 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x640e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x303b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words3 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0x40e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x403b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words4 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x680e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x503b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words5 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0x80e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x603b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words6 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x6c0e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x703b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words7 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0xc0e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x803b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words8 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x700e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x903b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def entry (c : Nat) : Nat := [22780,22970,23192,23394,23616,23818,24040,24242,24464].getD c 0
def hashPc (c : Nat) : Nat := [22800,23002,23217,23426,23641,23850,24065,24274,24493].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def c4StubPc : Nat := 1726
def c4Stub : List (BitVec 32) := bv_list% 32 [0x103b7,0x60138393,0x1111406f]
def look (c n : Nat) : Option (BitVec 32) := if entry c ≤ n then (words c)[n-entry c]? else if c = 0 ∧ c4StubPc ≤ n then c4Stub[n-c4StubPc]? else none
def runLeaf (c : Nat) : Option PRes := run (look c) [] (entry c) []
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def branchE : E := .bin .and (.reg .x18) (cE 1)
def branchShift (k : Nat) : E := .bin .sll branchE (cE k)
def physicalE (c : Nat) : E := if first c then .reg .x18 else .bin .add (.bin .srl (.reg .x18) (cE 1)) (branchShift 6)
def outOffset (c : Nat) : E := .bin .sll (.bin .add (physicalE c) (cE 128)) (cE 4)
def padAddr (c off : Nat) : E :=
  if c%2=1 then .bin .add (branchShift 5) (cE (0x67000+64*(c/2)+off)) else cE (FORW+32*c+off)
def padLoad (c off : Nat) : E := if c=0 then cE 0 else .ld (padAddr c off)
def headerE (c : Nat) : E := .bin .add
  (.bin .add (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (1537+65536*(c+1)))
def leafRegs (c : Nat) : List (Reg × E) :=
  [(.x6,outOffset c),(.x7,if first c then cE (1537+65536*(c+1)) else branchShift 6),
   (.x10,cE LEAFW),(.x11,cE 128),(.x12,.bin .add (outOffset c) (cE HEAPW)),
   (.x28,if c=0 then .reg .x28 else padAddr c 0),(.x29,cE LEAFW)]
def leafMem (c : Nat) : SymMem :=
  [mwc (LEAFW+24) (cE 0),mwc (LEAFW+16) (headerE c),mwc (LEAFW+40) (padLoad c 8),mwc (LEAFW+32) (padLoad c 0)]
def leafObl (c : Nat) : List Oblig := if c%2=1 then
  [.valid ⟨some (branchShift 5),BitVec.ofNat 64 (0x67000+64*(c/2)+8)⟩ 8,
   .valid ⟨some (branchShift 5),BitVec.ofNat 64 (0x67000+64*(c/2))⟩ 8] else []
def cycles (c : Nat) : Nat := if c=0 then 23 else if c%2=1 then 32 else if c=8 then 29 else 25
def expected (c : Nat) : PRes := pres (leafRegs c) (leafMem c) (leafObl c) (hashPc c) true (cycles c) []
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0xe6ceb06f,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x180006f,0x653823,0x1253c23,0x400393,0x796463,0x40006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words1 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x203b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x10e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words2 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x303b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x650e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words3 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x403b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x50e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words4 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x503b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x690e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words5 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x603b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x90e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words6 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x703b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x6d0e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words7 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x803b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0xd0e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words8 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x903b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x710e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def entry (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
def hashPc (c : Nat) : Nat := [22840, 23058, 23264, 23482, 23688, 23906, 24112, 24330, 24545].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def c4StubPc : Nat := 1729
def c4Stub : List (BitVec 32) := bv_list% 32 [0x103b7,0x60138393,0x1911406f]
def look (c n : Nat) : Option (BitVec 32) := if entry c ≤ n then (words c)[n-entry c]? else if c = 0 ∧ c4StubPc ≤ n then c4Stub[n-c4StubPc]? else none
def dirs (mode : Nat) : List Dir := if mode=0 then [.br false] else [.br true,.br (mode=2)]
def runNode (c mode : Nat) : Option PRes := runA (look c) [] (entry c) (dirs mode)
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify

def loE (c : Nat) : E := .bin .add (.bin .sll (.reg .x22) (cE 27)) (cE (1537+65536*(c+1)))
def hdrLo (c mode : Nat) : E := if mode=0 then .bin .sub (loE c) (.reg .x18) else loE c
def hdrHi (mode : Nat) : E := if mode=0 then cE 0 else .reg .x18
def padShift : E := .bin .sll (.bin .add (.bin .srl (.reg .x18) (cE 1)) (cE (2^64-2))) (cE 5)
def padAddr (c off : Nat) : E :=
  if c%2=1 then .bin .add padShift (cE (0x67000+64*(c/2)+16+off)) else cE (FORW+32*c+16+off)
def padWord (c mode off : Nat) : E := if mode=1 ∧ c≠0 then .ld (padAddr c off) else cE 0

def regs (c mode : Nat) : List (Reg × E) :=
  [(.x6,if mode=1 ∧ c≠0 then padWord c mode 0 else hdrLo c mode),
   (.x7,if mode=1 ∧ c≠0 then padWord c mode 8 else cE (if mode=0 then 8 else 4)),
   (.x10,cE NODEW),(.x11,cE 64),(.x12,cE NOUTW),
   (.x28,if mode=1 ∧ c≠0 then padAddr c 0 else .bin .add sh5 (cE HEAPW))]
def mem (c mode : Nat) : SymMem :=
  [mwc (NODEW+40) (padWord c mode 8),mwc (NODEW+32) (padWord c mode 0),
   mwc (NODEW+24) (hdrHi mode),mwc (NODEW+16) (hdrLo c mode),
   mwc (NODEW+56) (nodeLd 24),mwc (NODEW+48) (nodeLd 16),mwc (NODEW+8) (nodeLd 8),mwc NODEW (nodeLd 0)]
def readObl : List Oblig :=
  [.ne (nodeAddr 24) ⟨none,BitVec.ofNat 64 NODEW⟩,.ne (nodeAddr 24) ⟨none,BitVec.ofNat 64 (NODEW+8)⟩,
   .valid (nodeAddr 24) 8,.ne (nodeAddr 16) ⟨none,BitVec.ofNat 64 NODEW⟩,
   .ne (nodeAddr 16) ⟨none,BitVec.ofNat 64 (NODEW+8)⟩,.valid (nodeAddr 16) 8,
   .valid (nodeAddr 8) 8,.valid (nodeAddr 0) 8]
def padReadAddr (c off : Nat) : Addr := ⟨some padShift,BitVec.ofNat 64 (0x67000+64*(c/2)+16+off)⟩
def padReadObl (c off : Nat) : List Oblig :=
  ([0,8,48,56,16,24].map fun n=>Oblig.ne (padReadAddr c off) ⟨none,BitVec.ofNat 64 (NODEW+n)⟩) ++
    [.valid (padReadAddr c off) 8]
def obligations (c mode : Nat) : List Oblig :=
  (if mode=1 ∧ c%2=1 then padReadObl c 8 ++ padReadObl c 0 else []) ++ readObl

def branches (mode : Nat) : List Br :=
  if mode=0 then [⟨.ltu,.reg .x18,cE 8,false⟩] else
    [⟨.ltu,.reg .x18,cE 4,mode=2⟩,⟨.ltu,.reg .x18,cE 8,true⟩]
def cycles (c mode : Nat) : Nat :=
  if mode=1 then if c=0 then 32 else if c%2=1 then 38 else 34 else if c=0 then 31 else 29
def expected (c mode : Nat) : PRes :=
  pres (regs c mode) (mem c mode) (obligations c mode) (hashPc c) true (cycles c mode) (branches mode)
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def hookWords : List (BitVec 32) := bv_list% 32 [0x7480a06f,0x1b90906f,0x4a10806f,0x7390706f,0x2240706f,0x4bc0606f,0x7a40506f,0x2410406f,0x5290306f]
def hookLook (c n : Nat) : Option (BitVec 32) := if n=lI c then some (hookWords.getD c 0) else none
def runHook (c : Nat) : Option PRes := run (hookLook c) [entry c] (lI c) []
def expectedHook (c : Nat) : PRes := pres [] [] [] (entry c) false 1 []
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-! C1 (stage 1): the first word after each leaf `ecall` is a hook `jal zero,stub`. The stub copies the HIGH half
of the leaf answer (`a2+16..31`) onto its LOW half (`a2+0..15`) when the physical child is even (heap `128+p`
even), re-executes the displaced instruction and jumps back to the word after the hook. -/
def words0 : List (BitVec 32) := bv_list% 32 [0xa94ff06f,0x8000313,0x696663,0x7f00913,0x80006f,0xaadf406f]
def words1 : List (BitVec 32) := bv_list% 32 [0xfadfe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xfdcf506f]
def words2 : List (BitVec 32) := bv_list% 32 [0xc95fe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xd24f606f]
def words3 : List (BitVec 32) := bv_list% 32 [0x991fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xa5cf706f]
def words4 : List (BitVec 32) := bv_list% 32 [0xf1cfe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xfa1f706f]
def words5 : List (BitVec 32) := bv_list% 32 [0xc18fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xcd9f806f]
def words6 : List (BitVec 32) := bv_list% 32 [0x900fe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xa21f906f]
def words7 : List (BitVec 32) := bv_list% 32 [0xce0fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xf54fa06f]
def words8 : List (BitVec 32) := bv_list% 32 [0x9b8fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xc78fb06f]
def stub0 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x5550006f]
def stub1 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x380106f]
def stub2 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x3540106f]
def stub3 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x6540106f]
def stub4 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0xcd0106f]
def stub5 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x3cd0106f]
def stub6 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x6e90106f]
def stub7 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x3050106f]
def stub8 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x62d0106f]
def entry (c : Nat) : Nat := [22801, 23003, 23218, 23427, 23642, 23851, 24066, 24275, 24494].getD c 0
def nodePc (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
/-- C1 leaf stub entry of coordinate `c` (in the former nop gaps of `signCode_85`). -/
def stubPc (c : Nat) : Nat := [21942, 21958, 21975, 21991, 22049, 22065, 22082, 22539, 22556].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def stubWords (c : Nat) : List (BitVec 32) := [stub0,stub1,stub2,stub3,stub4,stub5,stub6,stub7,stub8].getD c []
def look (c n : Nat) : Option (BitVec 32) :=
  if entry c ≤ n then (words c)[n-entry c]? else if stubPc c ≤ n then (stubWords c)[n-stubPc c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def dirs (c mode : Nat) : List Dir := if first c then [.br (mode≠2)] else
  if mode=2 then [.br true] else [.br false,.br (mode=1)]
/-- `odd`: the physical child is odd (the stub's `bne` is taken and the LOW half is kept). -/
def runNext (c mode : Nat) (odd : Bool) : Option PRes :=
  run (look c) [leafI c,nodePc c] (entry c) (.br odd :: dirs c mode)
def nextE (c mode : Nat) : E := if mode=2 then cE 127 else if first c then x18p1 else
  if mode=1 then cE 1 else .bin .add (.reg .x18) (cE 2)
def cycles (c mode : Nat) : Nat := if first c then if mode=2 then 5 else 4 else if mode=2 then 4 else 7
def branches (c mode : Nat) : List Br := if first c then [⟨.ltu,x18p1,cE 128,mode≠2⟩] else
  if mode=2 then [⟨.eq,.reg .x18,cE 127,true⟩] else
  [⟨.eq,.reg .x18,cE 126,mode=1⟩,⟨.eq,.reg .x18,cE 127,false⟩]
/-- The stub's parity test: physical parity is raw bit 0 on A coordinates and raw bit 1 on B/C coordinates. -/
def parityE (c : Nat) : E := if first c then .bin .and (.reg .x18) (cE 1) else
  .bin .and (.bin .srl (.reg .x18) (cE 1)) (cE 1)
def a2A (off : Nat) : Addr := ⟨some (.reg .x12),BitVec.ofNat 64 off⟩
def a2Ld (off : Nat) : E := .ld (.bin .add (.reg .x12) (cE off))
def stubMem (odd : Bool) : SymMem := if odd then [] else [(a2A 8,a2Ld 24),(a2A 0,a2Ld 16)]
def stubObl (odd : Bool) : List Oblig := if odd then [] else
  [.valid (a2A 8) 8,.valid (a2A 24) 8,.valid (a2A 0) 8,.valid (a2A 16) 8]
def stubCycles (c : Nat) (odd : Bool) : Nat := (if first c then 4 else 5)+(if odd then 0 else 4)
def expected (c mode : Nat) (odd : Bool) : PRes := pres
  [(.x6,cE (if first c then 128 else if mode=2 then 127 else 126)),(.x18,nextE c mode)]
  (stubMem odd) (stubObl odd) (if mode=2 then nodePc c else leafI c) false (cycles c mode+stubCycles c odd)
  (branches c mode++[⟨.ne,parityE c,cE 0,odd⟩])
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-! C1 (stage 1): the fold half selector is a hook `jal zero,stub` (A/B: the former `addi t2,zero,8|4`; C: the
displaced `lui t4,0x51`). The stub selects the HIGH half (`t3 += 16`) iff `heap < halfLimit` (A/B tops, as in
#884) or `heap ≥ 16` and even (C1), and jumps back past Ghost's (now dead) `bgeu`/`addi t3` pair.
Stage 2 (merged singleton "Cm"): the C stub (22565..22573, 9 words) has the A/B shape with the first test
`heap = 2` (`addi t1,s2,-2; beq t1,zero,HI`) in place of `heap < halfLimit`, so the singleton's left top node
(heap 2) keeps the HIGH half; heap 3 keeps the LOW half. -/
def words0 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xa0cff06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf2691ee3]
def words1 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xee9fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words2 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xbf1fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words3 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x8cdfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words4 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xe78fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words5 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xb54fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words6 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x85cfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words7 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xc1cfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words8 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x904fe06f,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf26916e3]
def stub0 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x5e50006f]
def stub1 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x1080106f]
def stub2 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x4000106f]
def stub3 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x7240106f]
def stub4 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x1790106f]
def stub5 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x49d0106f]
def stub6 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x7950106f]
def stub7 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x3d50106f]
def stub8 : List (BitVec 32) := bv_list% 32 [0xffe90313,0x30a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x51eb7,0x6e10106f]
def entry (c : Nat) : Nat := [22841, 23059, 23265, 23483, 23689, 23907, 24113, 24331, 24546].getD c 0
def finishPc (c : Nat) : Nat := [22857, 23075, 23281, 23499, 23705, 23923, 24129, 24347, 24559].getD c 0
def nodePc (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
/-- C1 fold stub entry of coordinate `c`. -/
def stubPc (c : Nat) : Nat := [21950, 21967, 21983, 22000, 22057, 22074, 22090, 22548, 22565].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def stubWords (c : Nat) : List (BitVec 32) := [stub0,stub1,stub2,stub3,stub4,stub5,stub6,stub7,stub8].getD c []
def look (c n : Nat) : Option (BitVec 32) :=
  if entry c ≤ n then (words c)[n-entry c]? else if stubPc c ≤ n then (stubWords c)[n-stubPc c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def limit (c : Nat) : Nat := if first c then 3 else 1
def halfLimit (c : Nat) : Nat := if first c then 8 else 4
/-- The stub's path class of heap `h`: `0` a top heap below `halfLimit` (A/B) or the singleton's heap 2 (C, stage 2)
(HIGH), `1` another heap below 16 (LOW), `2` an odd heap `≥ 16` (LOW), `3` an even heap `≥ 16` (HIGH, C1). -/
def cls (c h : Nat) : Nat :=
  if (c≠8 ∧ h<halfLimit c) ∨ (c=8 ∧ h=2) then 0 else if h<16 then 1 else if h%2=1 then 2 else 3
def clsHigh (_c k : Nat) : Bool := decide (k=0 ∨ k=3)
/-- Branch directions of the stub (the same for every coordinate since stage 2). -/
def stubDirs (_c k : Nat) : List Dir :=
  if k=0 then [.br true] else if k=1 then [.br false,.br true] else if k=2 then [.br false,.br false,.br true]
  else [.br false,.br false,.br false]
def dirs (c k : Nat) (back : Bool) : List Dir := stubDirs c k++[.br back]
def runTail (c k : Nat) (back : Bool) : Option PRes :=
  run (look c) [nodePc c,finishPc c] (entry c) (dirs c k back)
def halfOff (high : Bool) : Nat := if high then 16 else 0
def outWord (high : Bool) (off : Nat) : E := ldc (NOUTW+halfOff high+off)
/-- Tail cycles by class (stage 2: the singleton's 18/19/21/22 equal A/B's). -/
def cycles (_c k : Nat) : Nat := if k=0 then 18 else if k=1 then 19 else if k=2 then 21 else 22
def ltB (n : Nat) (d : Bool) : Br := ⟨.ne,.bin .sltu (.reg .x18) (cE n),cE 0,d⟩
def oddB (d : Bool) : Br := ⟨.ne,.bin .and (.reg .x18) (cE 1),cE 0,d⟩
/-- Stage 2 (C stub): `addi t1,s2,-2; beq t1,zero,HI`, i.e. `heap = 2`. -/
def eq2B (d : Bool) : Br := ⟨.eq,.bin .add (.reg .x18) (cE (2^64-2)),cE 0,d⟩
/-- The stub's first test: `heap < halfLimit` on A/B, `heap = 2` on the singleton C. -/
def topB (c : Nat) (d : Bool) : Br := if c=8 then eq2B d else ltB (halfLimit c) d
def stubBranches (c k : Nat) : List Br :=
  if k=0 then [topB c true] else if k=1 then [ltB 16 true,topB c false]
  else if k=2 then [oddB true,ltB 16 false,topB c false]
  else [oddB false,ltB 16 false,topB c false]
def branches (c k : Nat) (back : Bool) : List Br := ⟨.ne,x18m1,cE (limit c),back⟩::stubBranches c k
def expected (c k : Nat) (back : Bool) : PRes :=
  pres [(.x6,cE (limit c)),(.x7,outWord (clsHigh c k) 8),(.x18,x18m1),
    (.x28,cE (NOUTW+halfOff (clsHigh c k))),(.x29,.bin .add sh4 (cE HEAPW))]
    [(heapAddr 8,outWord (clsHigh c k) 8),(heapAddr 0,outWord (clsHigh c k) 0)]
    [.valid (heapAddr 8) 8,.valid (heapAddr 0) 8]
    (if back then nodePc c else finishPc c) false (cycles c k) (branches c k back)
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0xe8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words1 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x640e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words2 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0x40e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words3 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x680e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words4 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0x80e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words5 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x6c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words6 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0xc0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words7 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x700e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words8 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x720e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def entry (c : Nat) : Nat := [22857, 23075, 23281, 23499, 23705, 23923, 24129, 24347, 24559].getD c 0
def pathPc (c : Nat) : Nat := [22878, 23092, 23302, 23516, 23726, 23940, 24150, 24364, 24576].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def look (c n : Nat) : Option (BitVec 32) := if entry c≤n then (words c)[n-entry c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def source (c : Nat) : Nat := HEAPW+(if first c then 64 else 32)
def target (c : Nat) : Nat := if first c then 0x67000+64*(c/2) else FORW+32*(c+1)
def nwords (c : Nat) : Nat := if first c then 8 else 4
def loBit : E := .bin .sll (.bin .and (.reg .x24) (cE 1)) (cE 6)
def physicalE (c : Nat) : E := if first c then .reg .x24 else .bin .add (.bin .srl (.reg .x24) (cE 1)) loBit
def mem (c : Nat) : SymMem := ((List.range (nwords c)).reverse.map fun k=>mwc (target c+8*k) (ldc (source c+8*k)))
def expected (c : Nat) : PRes := pres
  [(.x6,if first c then ldc (source c+48) else loBit),(.x7,ldc (source c+8*(nwords c-1))),
   (.x24,.bin .add (physicalE c) (cE 128)),(.x28,cE (source c)),(.x29,cE (target c))]
  (mem c) [] (pathPc c) false ((words c).length) []
def runFinish (c : Nat) := runA (look c) [pathPc c] (entry c) []
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x70e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x80e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x90e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xa0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xb0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xc0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words1 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x140e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x150e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x160e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x170e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x180e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x190e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x1a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words2 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x210e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x220e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x230e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x240e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x250e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x260e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words3 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x2e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x2f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x300e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x310e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x320e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x330e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x340e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words4 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3b0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3d0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x400e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words5 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x480e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x490e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4b0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4d0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words6 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x550e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x560e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x570e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x580e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x590e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x5a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words7 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x620e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x630e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x640e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x650e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x660e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x670e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x680e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words8 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x6f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x700e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x710e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x720e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x730e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x740e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x750e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def basePc (c : Nat) : Nat := [22878, 23092, 23302, 23516, 23726, 23940, 24150, 24364, 24576].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def entry (c level : Nat) : Nat := basePc c+12*level
def look (c n : Nat) : Option (BitVec 32) := if basePc c≤n then (words c)[n-basePc c]? else none
def levels (c : Nat) : Nat := if c<8 ∧ c%2=0 then 6 else 7
def offsetE (level : Nat) : E := .bin .sll (.bin .xor (.bin .srl (.reg .x24) (cE level)) (cE 1)) (cE 4)
def address (level off : Nat) : Addr := ⟨some (offsetE level),BitVec.ofNat 64 (HEAPW+off)⟩
def word (level off : Nat) : E := .ld (.bin .add (offsetE level) (cE (HEAPW+off)))
def target (c level : Nat) : Nat := slotV c 6+16*level
def expected (c level : Nat) : PRes := pres
  [(.x6,word level 0),(.x7,word level 8),(.x28,.bin .add (offsetE level) (cE HEAPW)),(.x29,cE (target c level))]
  [mwc (target c level+8) (word level 8),mwc (target c level) (word level 0)]
  [.valid (address level 8) 8,.valid (address level 0) 8] (entry c (level+1)) false 12 []
def runPath (c level : Nat) := runA (look c) [entry c (level+1)] (entry c level) []
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x7eb7,0xd0e8e93,0xeb023,0xeb423,0x891f506f]
def words1 : List (BitVec 32) := bv_list% 32 [0xda4f606f]
def words2 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x270e8e93,0xeb023,0xeb423,0xb0cf706f]
def words3 : List (BitVec 32) := bv_list% 32 [0x824f806f]
def words4 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x410e8e93,0xeb023,0xeb423,0xd89f806f]
def words5 : List (BitVec 32) := bv_list% 32 [0xaa1f906f]
def words6 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x5b0e8e93,0xeb023,0xeb423,0x809fa06f]
def words7 : List (BitVec 32) := bv_list% 32 [0xd1cfb06f]
def words8 : List (BitVec 32) := bv_list% 32 [0xa5cfc06f]
def entry (c : Nat) : Nat := [22950, 23176, 23374, 23600, 23798, 24024, 24222, 24448, 24660].getD c 0
def nextPc (c : Nat) : Nat := [12238, 13297, 14357, 15417, 16476, 17536, 18596, 19655, 20715].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def look (c n : Nat) : Option (BitVec 32) := if entry c≤n then (words c)[n-entry c]? else none
def target (c : Nat) : Nat := slotP c 6
def expected (c : Nat) : PRes := pres (if first c then [(.x29,cE (target c))] else [])
  (if first c then [mwc (target c+8) (cE 0),mwc (target c) (cE 0)] else []) [] (nextPc c) false (if first c then 5 else 1) []
def runEnd (c : Nat) := run (look c) [nextPc c] (entry c) []
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0xe3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0xe3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xb11f406f]
def words1 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0xe3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0x885f506f]
def words2 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x8e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd9cf606f]
def words3 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x8e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0x25cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xb04f706f]
def words4 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x10e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0x818f806f]
def words5 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x10e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd81f806f]
def words6 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0x25cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xa99f906f]
def words7 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x18e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xffcfa06f]
def words8 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0x25c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x18e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd14fb06f]
def entry (c : Nat) : Nat := [22765, 22955, 23177, 23379, 23601, 23803, 24025, 24227, 24449].getD c 0
def hookWord (c : Nat) : BitVec 32 := [0x4ec0b06f,0x7740a06f,0x2610906f,0x4f90806f,0x7e10706f,0x27c0706f,0x5640606f,0x7fc0506f,0x2e90406f].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def rawBit (c : Nat) : Nat := [0, 6, 64, 70, 128, 134, 192, 198, 229].getD c 0
def rankBit (c : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD c 0
def look (c n : Nat) : Option (BitVec 32) := if n=cbase c then some (hookWord c) else if entry c ≤ n then (words c)[n-entry c]? else none
def fieldE (bit width : Nat) : E := .bin .and (.bin .srl (ldc (NBUF+8*(bit/64))) (cE (bit%64))) (cE (2^width-1))
def expected (c : Nat) : PRes := pres [(.x6,.bin .sll (fieldE (rankBit c) 10) (cE 2)),
  (.x24,fieldE (rawBit c) 7),(.x25,fieldE (rankBit c) 10),
  (.x28,.bin .add (.bin .sll (fieldE (rankBit c) 10) (cE 2)) (cE TBL))] [] [] (lwuI c) false ((words c).length+1) []
def runField (c : Nat) : Option PRes := run (look c) [lwuI c] (cbase c) []
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def base (expand : Bool) : Nat := if expand then 45056 else 22600
def signWords : List (BitVec 32) := bv_list% 32 [0x993,0x293,0x200337,0x30313,0x2869f063,0x20e37,0x120e0e13,0xe3823,0x13e3c23,0x20537,0x12050513,0x4000593,0x20637,0x16060613,0x73,0x20e37,0x160e0e13,0x18e3303,0x3235313,0x2de00393,0x22737c63,0xa13,0x208b7,0x16088893,0xfebab7,0xa8a93,0x8bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x206cf863,0x19a8e33,0xe4303,0x6a0a33,0x8bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x88bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x1c6cfc63,0x19a8e33,0xe4303,0x6a0a33,0x8bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x88bc83,0x19cdc93,0x3ffcfc93,0x23300313,0x1a6cf063,0x19a8e33,0xe4303,0x6a0a33,0x88bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x88bc83,0x25cdc93,0x3ffcfc93,0x23300313,0x166cf463,0x19a8e33,0xe4303,0x6a0a33,0x88bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x108bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x126cf863,0x19a8e33,0xe4303,0x6a0a33,0x108bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x108bc83,0x19cdc93,0x3ffcfc93,0x23300313,0xe6cfc63,0x19a8e33,0xe4303,0x6a0a33,0x108bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x108bc83,0x25cdc93,0x3ffcfc93,0x23300313,0xc6cf063,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x188bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x86cf463,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x188bc83,0x19cdc93,0x3ffcfc93,0x23300313,0x46cf863,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0x26c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x30a00313,0x26a7263,0x20e37,0x160e0e13,0xe3b03,0x21b5b13,0x20e37,0x550e0e13,0x16e3023,0xaf9f406f,0x198993,0xd7dff06f]
def expandWords : List (BitVec 32) := bv_list% 32 [0x993,0x293,0x200337,0x30313,0x2a69f263,0x20e37,0x120e0e13,0xe3823,0x13e3c23,0x20537,0x12050513,0x4000593,0x20637,0x16060613,0x73,0x208b7,0x16088893,0x188b303,0x3235313,0x2de00393,0x24737e63,0xff9a37,0xb90a0a13,0xa93,0x8bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x226c7e63,0x18a0333,0x34303,0x6a8ab3,0x8bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x1e6c7e63,0x18a0333,0x34303,0x6a8ab3,0x8bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0x19c5c13,0x3ffc7c13,0x23300313,0x1a6c7e63,0x18a0333,0x34303,0x6a8ab3,0x88bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0x25c5c13,0x3ffc7c13,0x23300313,0x166c7e63,0x18a0333,0x34303,0x6a8ab3,0x88bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x126c7e63,0x18a0333,0x34303,0x6a8ab3,0x108bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0x19c5c13,0x3ffc7c13,0x23300313,0xe6c7e63,0x18a0333,0x34303,0x6a8ab3,0x108bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0x25c5c13,0x3ffc7c13,0x23300313,0xa6c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x188bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x66c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x188bc03,0x19c5c13,0x3ffc7c13,0x23300313,0x26c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0x26c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x30a00313,0x6af463,0x180006f,0x198993,0xd59ff06f]
def words (expand : Bool) : List (BitVec 32) := if expand then expandWords else signWords
 def look (expand : Bool) (n : Nat) : Option (BitVec 32) := if base expand ≤ n then (words expand)[n-base expand]? else none
 def trial (expand : Bool) : Nat := base expand+2
 def next (expand : Bool) : Nat := if expand then 45227 else 22762
 def fail (expand : Bool) : Nat := next expand+2
 def firstField (expand : Bool) : Nat := if expand then 45080 else 22626
 def field (expand : Bool) (k : Nat) : Nat := firstField expand+(if expand then 16 else 14)*k
 def rankLoad (expand : Bool) (k : Nat) : Nat := field expand k+6
 def corrLoad (expand : Bool) (k : Nat) : Nat := field expand k+(if expand then 14 else 12)
 def cap (expand : Bool) : Nat := field expand 9
 def accepted (expand : Bool) : Nat := cap expand+2
 def sumReg (expand : Bool) : Reg := if expand then .x21 else .x20
 def tableReg (expand : Bool) : Reg := if expand then .x20 else .x21
 def rankReg (expand : Bool) : Reg := if expand then .x24 else .x25
 def addrReg (expand : Bool) : Reg := if expand then .x6 else .x28
 def tableBase (expand : Bool) : Nat := if expand then 0xff8b90 else 0xfeb000
 def correctionOffset (expand : Bool) (k : Nat) : Nat := (if expand then 1536 else 1024)+(if SharedLeaf.first k then 0 else 32)
 def fieldAddr (bit : Nat) : Addr := ⟨some (.reg .x17),BitVec.ofNat 64 (8*(bit/64))⟩
 def fieldE (bit width : Nat) : E := .bin .and (.bin .srl (.ld (fieldAddr bit).toE) (cE (bit%64))) (cE (2^width-1))
 def rankE (k : Nat) : E := fieldE (SharedField.rankBit k) 10
 def costBit (k : Nat) : Nat := SharedField.rawBit k+(if SharedLeaf.first k then 0 else 1)
 def costE (k : Nat) : E := fieldE (costBit k) 5
 def gateE : E := .bin .srl (ldc (NBUF+24)) (cE 50)
 def expectedHead (expand reject : Bool) : PRes := pres [(.x6,cE (2^21))] [] []
   (if reject then fail expand else trial expand+3) false 3 [⟨.geu,.reg .x19,cE (2^21),reject⟩]
 def expectedTrial (expand : Bool) : PRes := pres [(.x28,cE DIG),(.x10,cE DIG),(.x11,cE 64),(.x12,cE NBUF)]
   [mwc (DIG+24) (.reg .x19),mwc (DIG+16) (cE 0)] [] (base expand+14) true 9 []
 def expectedGate (expand reject : Bool) : PRes := pres [((if expand then .x17 else .x28),cE NBUF),(.x6,gateE),(.x7,cE 734)] [] []
   (if reject then next expand else base expand+21) false 6 [⟨.geu,gateE,cE 734,reject⟩]
 def expectedInit (expand : Bool) : PRes := pres (if expand then [(.x20,cE (tableBase expand)),(.x21,cE 0)]
   else [(.x20,cE 0),(.x17,cE NBUF),(.x21,cE (tableBase expand))]) [] [] (firstField expand) false (if expand then 3 else 5) []
 def expectedRank (expand : Bool) (k : Nat) (reject : Bool) : PRes := pres [(rankReg expand,rankE k),(.x6,cE 563)] [] [.valid (fieldAddr (SharedField.rankBit k)) 8]
   (if reject then next expand else field expand k+5) false 5 [⟨.geu,rankE k,cE 563,reject⟩]
 def expectedRankAddr (expand : Bool) (k : Nat) : PRes := pres [(addrReg expand,.bin .add (.reg (tableReg expand)) (.reg (rankReg expand)))] [] [] (rankLoad expand k) false 1 []
 def expectedCorrPrep (expand : Bool) (k : Nat) : PRes := pres
   [(sumReg expand,.bin .add (.reg (sumReg expand)) (.reg .x6)),(.x24,costE k),
     (addrReg expand,if expand then .bin .add (costE k) (cE (tableBase expand+correctionOffset expand k))
       else .bin .add (.reg (tableReg expand)) (costE k))] [] [.valid (fieldAddr (costBit k)) 8] (corrLoad expand k) false (if expand then 7 else 5) []
 def expectedSum (expand : Bool) (k : Nat) : PRes := pres [(sumReg expand,.bin .add (.reg (sumReg expand)) (.reg .x6))] [] [] (field expand (k+1)) false 1 []
 def expectedCap (expand reject : Bool) : PRes := pres [(.x6,cE 778)] [] [] (if reject then next expand else accepted expand) false 2
   [⟨.geu,.reg (sumReg expand),cE 778,reject⟩]
 def expectedNext (expand : Bool) : PRes := pres [(.x19,.bin .add (.reg .x19) (cE 1))] [] [] (trial expand) false 2 []
 def rankLbuWord (expand : Bool) : BitVec 32 := if expand then 0x00034303 else 0x000e4303
 def corrLbuWord (expand : Bool) (k : Nat) : BitVec 32 := if expand then 0x00034303 else if SharedLeaf.first k then 0x400e4303 else 0x420e4303
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem codeAt_get_word {im : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : b<2^30) (hc : CodeAt im (pcOf b) code) {i : Nat} {w : BitVec 32}
    (hi : code[i]?=some w) : im.code[b+i]?=some w := by
  have hpc : (pcOf b).toNat=4096+4*b := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest,hrest⟩ := hc.2.2.2
  rw [hpc,show (4096+4*b-4096)/4=b by omega] at hrest
  have hlen:= (List.getElem?_eq_some_iff.mp hi).1
  have hh : (code++rest)[i]?=some w := by rwa [List.getElem?_append_left hlen]
  rw [hrest,List.getElem?_drop] at hh
  simpa [Nat.add_comm] using hh

theorem look_of_code {im : Image} (m : Bool)
    (hc : CodeAt im (pcOf (base m)) (words m)) : LookOK im (look m) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hn
    have hb : base m<2^30 := by cases m <;> decide
    have hh:=codeAt_get_word hb hc hw
    simpa only [Nat.add_sub_cancel' hn] using hh
  · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedDigest
