import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Common

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def runA (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux { noAlias := true } look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
def cE (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldc (a : Nat) : E := .ld (cE a)
def mwc (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def regsOf (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
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
def chainK (c i : Nat) : Nat := 0x80 + 4 * i + 65536 * c
def nodeK (c : Nat) : Nat := 769 + 65536 * (4 + c)
def slotV (c i : Nat) : Nat := SIG + 16 + 208 * c + 16 * i
def slotP (c l : Nat) : Nat := SIG + 112 + 208 * c + 16 * l
def leafOff (i : Nat) : Nat := if i = 0 then 0 else 16 * (i + 2)
def forOff (c : Nat) : Nat := 32 + 32 * c
def w1E : E := .bin .or (.bin .sll (.reg .x18) (cE 32)) (.reg .x22)
def qE (c i : Nat) : E := .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (chainK c i))
def idx32E : E := .bin .sll (.reg .x22) (cE 32)
def nodeLoE (c : Nat) : E :=
  if c = 0 then .bin .or (.bin .sll (.reg .x22) (cE 27)) (cE 1537)
  else .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (cE (65536 * c))) (cE 1537)
def leafLoE (c : Nat) : E :=
  .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (1537 + 65536 * c))
def leafX7 (c : Nat) : E := if c = 0 then .bin .sll (.reg .x18) (cE 20) else cE (65536 * c + 1537)
def x29A (off : Nat) : Addr := ⟨some (.reg .x29), BitVec.ofNat 64 off⟩
def nodeLo7 (c index : Nat) : Nat := 1537 + 65536 * c + 2 ^ 27 * index
def leafLo7 (c index j : Nat) : Nat := 1537 + 65536 * c + 2 ^ 20 * j + 2 ^ 27 * index
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
def expL (c : Nat) : PRes :=
  pres [(.x6, heapLeafE), (.x7, leafX7 c), (.x10, cE LEAFW), (.x11, cE 128), (.x12, .bin .add heapLeafE (cE HEAPW))]
    [(x29A 24, cE 0), (x29A 16, leafLoE c), (x29A 40, cE 0), (x29A 32, cE 0)]
    [.valid (x29A 24) 8, .valid (x29A 16) 8, .valid (x29A 40) 8, .valid (x29A 32) 8] (tI c - 1) true
    (if c = 0 then 17 else 18) []
def expT (c : Nat) (back : Bool) : PRes :=
  if back then pres [(.x6, cE 128), (.x18, x18p1)] [] [] (leafI c) false 3 [⟨.ltu, x18p1, cE 128, true⟩]
  else pres [(.x6, cE 128), (.x18, cE 127)] [] [] (nodeI c) false 4 [⟨.ltu, x18p1, cE 128, false⟩]
def nodeLd (off : Nat) : E := .ld (.bin .add sh5 (cE (HEAPW + off)))
def nodeAddr (off : Nat) : Addr := ⟨some sh5, BitVec.ofNat 64 (HEAPW + off)⟩
def nodeX7 (c : Nat) : E := if c = 0 then nodeLd 24 else cE (65536 * c)
def expN (c : Nat) : PRes :=
  pres [(.x6, nodeLoE c), (.x7, nodeX7 c), (.x10, cE NODEW), (.x11, cE 64), (.x12, cE NOUTW),
    (.x28, .bin .add sh5 (cE HEAPW)), (.x29, cE NODEW)]
    [mwc (NODEW + 24) (.reg .x18), mwc (NODEW + 16) (nodeLoE c), mwc (NODEW + 56) (nodeLd 24),
      mwc (NODEW + 48) (nodeLd 16), mwc (NODEW + 8) (nodeLd 8), mwc NODEW (nodeLd 0)]
    [.ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 NODEW⟩, .ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩,
      .valid (nodeAddr 24) 8, .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 NODEW⟩,
      .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩, .valid (nodeAddr 16) 8, .valid (nodeAddr 8) 8,
      .valid (nodeAddr 0) 8]
    (ntI c - 1) true 25 []
def heapAddr (off : Nat) : Addr := ⟨some sh4, BitVec.ofNat 64 (HEAPW + off)⟩
def expNT (c : Nat) (back : Bool) : PRes :=
  pres [(.x6, cE 1), (.x7, ldc (NOUTW + 8)), (.x18, x18m1), (.x28, cE NOUTW),
    (.x29, .bin .add sh4 (cE HEAPW))]
    [(heapAddr 8, ldc (NOUTW + 8)), (heapAddr 0, ldc NOUTW)] [.valid (heapAddr 8) 8, .valid (heapAddr 0) 8]
    (if back then nodeI c else rI c) false 13 [⟨.ne, x18m1, cE 1, back⟩]
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
def expFor : PRes :=
  pres [(.x6, cE 3841), (.x10, cE FORW), (.x11, cE 320), (.x12, cE FOUT), (.x28, cE FORW)]
    [mwc (FORW + 8) (cE 0), mwc FORW (cE 0), mwc (FORW + 24) (.reg .x22), mwc (FORW + 16) (cE 3841)] [] 20728 true 13 []
def expJ : PRes := pres [] [] [] 370 false 1 []
def runF (c : Nat) : Option PRes := run (coordLook c) [lwuI c] (cbase c) []
def chkDirs (v : Nat) : List Dir := if v = 0 then [.br true] else if v = 1 then [.br false, .br true] else [.br false, .br false]
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 4) []
def runL (c : Nat) : Option PRes := run (coordLook c) [] (lI c) []
def runT (c : Nat) (back : Bool) : Option PRes := run (coordLook c) [leafI c, nodeI c] (tI c) [.br back]
def runN (c : Nat) : Option PRes := runA (coordLook c) [] (nodeI c) []
def runNT (c : Nat) (back : Bool) : Option PRes := run (coordLook c) [nodeI c, rI c] (ntI c) [.br back]
def runR0 (c : Nat) : Option PRes := run (coordLook c) [pcI c 0] (rI c) []
def runPC (c l : Nat) : Option PRes := run (coordLook c) [pcI c (l + 1)] (pcI c l) []
def runSK : Option PRes := run headLook [fieldIdx.getD 0 0] 11175 []
def runFor : Option PRes := run tailLook [370] 20715 []
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
      (.x29, cE PRIVW)] [mwc (PRIVW + 24) pairWE] [] (ecI c) true 10 [⟨.ne, x7p1, cE 51, true⟩]
  else
    pres [(.x6, cE 51), (.x7, x7p1), (.x12, .bin .add (.reg .x12) (cE 32)), (.x18, cE 0)] [] [] (leafI c) false 6
      [⟨.ne, x7p1, cE 51, false⟩]
def ptE (i : Nat) : E :=
  .bin .add (.bin .sll (.bin .add (.bin .sll (.reg .x18) (cE 1)) (.reg .x18)) (cE 1)) (cE (i + 1))
def retW (c i : Nat) : Nat := 0x1000 + 4 * (qI c i + 5)
def expQ (c i : Nat) : PRes := pres [(.x1, cE (retW c i)), (.x6, ptE i)] [] [] hornI false 5 []
def expS (c i : Nat) : PRes :=
  pres [(.x6, cE 4), (.x7, cE (chainK c i)), (.x26, dE i), (.x29, cE CHAINW)]
    [mwc (CHAINW + 24) (cE 0), mwc (CHAINW + 16) (qE c i)] [] (chkI c i 0) false (if c = 0 then 14 else 15) []
def expH0 : PRes := pres [(.x7, cE (COEF + 1632)), (.x10, cE 0), (.x11, cE 0), (.x28, cE COEF)] [] [] hkI false 6 []
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
    optBeq (runN c) (expN c) && optBeq (runNT c true) (expNT c true) && optBeq (runNT c false) (expNT c false) &&
    optBeq (runR0 c) (expR0 c) && (List.range 7).all fun l => optBeq (runPC c l) (expPC c l)
def okCoord (c : Nat) : Bool := okF c && okC c && okQ c && okS c && okChk c && okStp c && okLc c && okTail c
def okGlobal : Bool := optBeq runSK expSK && optBeq runFor expFor && optBeq runJ expJ && okHorn
end ClaudeWCT.W9.Machine.Sign
