import Mathlib.Tactic
import SigGolfCandidate.T3M.Verify.ChainRuns


section


namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
/-- Largest digit of the chains of top group `q` (campaign R6): the 8 radix-6 groups (q < 8, chains 0..23) have 5,
the 9 radix-5 groups (8 <= q < 17, chains 24..50) have 4, group 17 (the radix-8 checksum chain 51) has 7. -/
def mx (q : Nat) : Nat := if q<8 then 5 else if q<17 then 4 else 7
def off (i : Nat) : Word := BitVec.ofNat 64 (64*(53-i))-BitVec.ofNat 64 1664
/-- R6: top leaf slots start at 25264 (leaf = [P | 32-byte gap | ends]). -/
def slot (i : Nat) : Nat := 25264+16*i
def slotOffset (a : Nat) : Nat := a-24688
def rungR (d : Nat) (sl : Option Nat) (p : Nat) : Result :=
  T3M.rungRB d (sl.map slotOffset) p
def copyN (rb : Reg) (o : Word) (sl tgt : Nat) : Result :=
  T3M.copyNB rb o (slotOffset sl) tgt
def copyFH (rb : Reg) (o : Word) (sl p : Nat) : Result :=
  T3M.copyFHB rb o (slotOffset sl) p
def headRH (rb : Reg) (o : Word) (d : Nat) (sl : Option Nat) (p i : Nat) : Result :=
  T3M.headRHB rb o d (sl.map slotOffset) p i
def emptyR (p : Nat) : Result := ⟨SymState.init,.c (pcOf p),.fuel,0,0⟩
def baseTab : List Nat := [184791,130112,98124,184908,129996,130212,185013,185050,133292,186153,185147,122700,711,186183,77482,185310,133324,186281,102698,83032,133356,186311,77610,84056,268,93382,132863,185676,127564,133388,185779,185818,122828,133420,186409,98252,123212,805,186665,77738,127692,133452,186921,102826,103513,133484,187100,77910,104537,1105,97478,186442,98636,127820,186552,186584,98764,123340,186695,187433,101964,186794,186829,187689,78122,127948,186954,187817,102954,108633,187068,187847,78250,118314,1804,187206,132902,102092,187323,187357,132941,102220,187465,133516,187945,187562,187599,933,187975,97834,187725,133548,188128,103082,118442,133580,188201,97962,118570,2129,98504,132980,188091,128332,133612,133019,188233,123468,133644,188337,188367,123596,967,188472,98090,128460,133676,188596,103210,118698,133708,188502,98218,119082,2316,101574,188857,102348,128588,184873,188999,102732,123724,189110,189142,102860,123852,189244,189277,98602,128716,189369,189401,103338,119210,189483,189515,98730,122410,2572,189621,133058,102988,189738,189772,133097,103116,189880,189915,188626,103244,190014,1317,188713,101930,190140,190174,188743,103722,122538,190288,188896,102058,190378,190403,102600,133136,190506,190543,185184,133175,190648,190685,185257,188969,190782,124236,1351,189662,190917,128844,185385,190049,191041,191068,185417,190249,191155,191183,191208,117958,133214,191311,128972,185513,191414,103372,124364,185545,191557,103756,126540,191659,191692,102186,129356,185641,191816,103850,122666,185897,191930,191960,122794,2829,192036,192077,192116,192153,192187,192219,192258,192295,192330,192362,192392,192429,192464,192497,192527,192555,192589,192621,192651,192678,192703,192735,192765,192793,192818,192841,133253,103884,192958,192992,193024,193063,193100,193135,193167,193197,193234,193269,193302,193332,193360,193394,193426,193456,193483,193508,193540,193570,193598,193623,193646,193687,193726,193763,193797,193829,193868,193905,193940,193972,194002,194039,194074,194107,194137,194165,194199,194231,194261,194288,194313,194345,194375,194403,194428,194451,194492,194531,194568,194602,194634,194673,194710,194745,194777,194807,194844,194879,194912,194942,194970,195004,195036,195066,195093,195118,195150,195180,195208,195233,195256,195297,195336,195373,195407,195439,195478,195515,195550,195582,195612,195649,195684,195717,195747,195775,195809,195841,195871,195898,195923,195955,195985,196013,196038,196061,196102,196141,196178,196212,196244,196283,196320,196355,196387,196417,196454,196489,196522,196552,196580,196614,196646,196676,196703,196728,196760,196790,196818,196843,196866,196907,196946,196983,197017,197049,197088,197125,197160,197192,197222,197259,197294,197327,197357,197385,197419,197451,197481,197508,197533,197565,197595,197623,197648,197671,197712,197751,197788,197822,197854,197893,197930,197965,197997,198027,198064,198099,198132,198162,198190,198224,198256,198286,198313,198338,198370,198400,198428,198453,254621,254661,254699,254734,254768,254806,254842,254875,254907,254942,254975,255005,255034,255068,255100,255129]
/-! ### R6 radix-6 groups (verify image RC_T153_g804, generator sig-r6/verify/py/gen_r6v.py)
Group `g < 8` (chains 3g..3g+2, largest digit 5) reads the 8-bit field `raw` (g = 0: bits 0..7, valid iff raw >= 40,
rank = raw - 40; g = 1..6: bits 8g..8g+7; g = 7: bits 119..126; g >= 1 valid iff raw < 216, rank = raw).
Its cell `cell6 g raw` (g = 0: base-free column `512 (raw - 3) + 326`; g = 1..3: table B rows `3327 - raw`;
g = 4..7: table A rows `3328 + raw`; offset `r6Off g` inside the 64-word FTS rows) holds the s8 update and chain A's
head / copy, then jumps into the shared body `body6 g dB dC` (chain A rung ladder, chain B, chain C, next dispatch).
Invalid raws land on zero words (guards) or, for g = 0 and raw < 3, below the code start. -/
/-- R6 top target (the checksum digit is `topT - sum`). -/
def topT : Nat := 153
def r6Off (g : Nat) : Nat := 40+6*(g%4)
/-- The 8-bit field value of rank `k` in r6 group `g`. -/
def rawOf6 (g k : Nat) : Nat := if g=0 then k+40 else k
def cell6 (g raw : Nat) : Nat :=
  if g=0 then 512*(raw-3)+326 else if g<4 then 64*(3327-raw)+r6Off g else 64*(3328+raw)+r6Off g
/-- Body start (chain A ladder) of r6 group `g` with digits `dB`, `dC`: entry `36 g + 6 dB + dC`. -/
def body6Tab : List Nat := [185713,185085,98758,93382,51748,26148,185855,101958,97478,126243,26405,21028,102854,98504,130112,26182,21285,711,101574,130212,27044,21062,16165,14884,51782,26917,21797,16677,11045,9764,27078,21924,805,14918,9798,4644,186537,189172,187130,186439,132863,52644,190320,188404,188532,127558,52005,46628,189804,190279,128454,52678,21958,25381,191093,128582,72485,46662,933,20261,132902,52517,25124,967,10788,11557,72997,47524,25893,20773,13860,5411,189353,190819,191988,191722,132941,76581,191017,189097,191273,185216,67108,47558,191846,190889,185673,77093,25158,41508,190761,187719,77255,50724,1317,24357,132980,67142,26020,1351,10822,13894,92743,50758,41542,24869,14756,6437,185001,187049,188773,185449,133019,92965,187305,189609,186862,188926,68004,51620,190121,191453,187206,93477,26054,42404,184942,188585,93639,51654,15908,40484,133058,68038,50981,15942,11684,14790,96839,67365,42438,40518,21324,11084,185769,187500,189038,186986,133097,97061,188270,185129,186341,189947,71204,67877,185289,190945,190577,97573,51493,45604,186213,77220,97735,71461,16804,41380,133136,71238,66084,16838,11718,21836,100935,71973,45638,41414,22052,11596,186481,189225,186727,188005,133175,101157,190633,188073,185960,92708,72100,72265,188841,186086,93604,101669,66118,46500,190426,96804,101831,73161,20004,44580,186584,72134,66980,20038,15141,22086,113188,75557,46534,44614,22948,12069,189865,191587,185577,187877,188231,113222,187247,189993,72228,97700,75300,76069,130300,73124,100900,114084,67014,49700,76324,101796,114118,76361,20900,45476,188329,75334,70180,20934,15653,22982,117541,87588,49734,45510,23333,22821,189545,187759,102982,102600,118053,76196,188457,187634,123334,188999,87622,70214,188656,123462,189431,76230,50596,24100,184791,191145,91684,71076,52044,15780,121637,88484,50630,52556,23845,10660,91718,71110,24134,15814,10694,4678]
def body6 (g dB dC : Nat) : Nat := body6Tab.getD (36*g+6*dB+dC) 0
def base (q dB dC : Nat) : Nat :=
  if q<8 then body6 q dB dC else baseTab.getD (if q<17 then 25*q+5*dB+dC else 425+4*dB+dC) 0
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 5 else 4+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
/-- R6 bodies omit chain C's copy when chains B and C both have the largest digit (C is buffer-safe). -/
def skipBody (q dB dC : Nat) : Bool := decide (q<8 ∧ dB=mx q ∧ dC=mx q)
def pcX (q dB dC : Nat) : Nat := pcC q dB dC+partLen q dC-(if skipBody q dB dC then 4 else 0)
def entOff (q : Nat) : Nat :=
  if q=0 then 1315 else if q=1 then 1350 else if q=2 then 548 else if q=3 then 582
  else if q=4 then 804 else if q=5 then 838 else if q=6 then 1444 else if q=7 then 1478
  else if q=8 then 676 else if q=9 then 64 else if q=10 then 710 else if q=11 then 932
  else if q=12 then 966 else if q=13 then 1276 else if q=14 then 1532 else if q=15 then 764 else 1188
def cellW (q k : Nat) : Nat :=
  if q<8 then cell6 q (rawOf6 q k) else if q<17 then 1024*(125-k)+entOff q else 0
def entW (q k : Nat) : Nat := cellW q k + (if q=9 ∧ k%2=0 then 1 else 0)
def inl (q : Nat) : Bool := decide (q=9 ∨ (13 ≤ q ∧ q ≤ 16))
def leadOff (q : Nat) : Nat := 1
def leadPc (q k : Nat) : Nat := entW q k+leadOff q
def kdig (q k j : Nat) : Nat := k/(mx q+1)^j%(mx q+1)
def kss (q k : Nat) : Nat := kdig q k 0+kdig q k 1+kdig q k 2
def rowInl (q k : Nat) : Bool := inl q || decide (8≤q ∧ q<17 ∧ 3≤kss q k)
def gbase (q k : Nat) : Nat :=
  if rowInl q k then
    (if kdig q k 0=mx q then leadPc q k+3-2*mx q
     else if kdig q k 0+1=mx q then leadPc q k+2-2*kdig q k 0
     else leadPc q k+3-2*kdig q k 0)
  else base q (kdig q k 1) (kdig q k 2)
def skipA (q k : Nat) : Bool := decide (q=0 ∧ kdig q k 0=mx q)
def skipB (q k : Nat) : Bool := (rowInl q k || decide (q<8)) && decide (kdig q k 0=mx q ∧ kdig q k 1=mx q)
def skipC (q k : Nat) : Bool := (rowInl q k || decide (q<8)) && decide (kdig q k 1=mx q ∧ kdig q k 2=mx q)
/-- Start of chain B. R6 groups (q < 8): the body keeps chain B's copy, a buffer-safe chain B is jumped over (+4). -/
def gB (q k : Nat) : Nat :=
  if q<8 then gbase q k+2*mx q+1+(if skipB q k then 4 else 0) else gbase q k+2*mx q+1-(if skipA q k then 4 else 0)
def gC (q k : Nat) : Nat := gB q k+partLen q (kdig q k 1)-(if skipB q k then 4 else 0)
def gX (q k : Nat) : Nat := gC q k+partLen q (kdig q k 2)-(if skipC q k then 4 else 0)
def headJD (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12 (addC (addC (.reg rb) o) 48)).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,5,5⟩
def headJDTerm (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg rb) o)).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,4,4⟩
def headJDF (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  {headJD rb o tgt i d with stop:=.fuel,steps:=4,cycles:=4}
def headJDTermF (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  {headJDTerm rb o tgt i d with stop:=.fuel,steps:=3,cycles:=3}
def s8R (n p : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (addC (.reg .x24) (-BitVec.ofNat 64 n)),[],[]⟩,.c (pcOf (p+1)),.fuel,1,1⟩
/-- R6 group 0's first cell word `addi s8,zero,T-kss`. -/
def guardR (k : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (.c (BitVec.ofNat 64 topT-BitVec.ofNat 64 (kss 0 k))),[],[]⟩,
    .c (pcOf (cellW 0 k+1)),.fuel,1,1⟩
def bge9R (p : Nat) : Result :=
  ⟨SymState.init,.ite .ge (.reg .x16) (.c 0) (.c (BitVec.ofNat 64 (0x1000+4*p-4096))) (.c (pcOf (p+1))),.branch,1,1⟩
def tailR (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 1 else 0
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (addC (.reg .x4) (BitVec.ofNat 64 (slotOffset a)))
      | none => RegFile.init), [], []⟩, .c (pcOf (p + n)), .ecall, n, n⟩
def headRHT (rb : Reg) (o : Word) (d sl p i : Nat) : Result :=
  {headRH rb o d (some sl) p i with pc:=.c (pcOf (p+4)),steps:=4,cycles:=4}
def shift12 (w : Reg) (b : Nat) : E :=
  if b<12 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (12-b)))
  else .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b-12)))
def dispatchR (q : Nat) : Result :=
  let sh := shift12 (if q<9 then .x16 else .x17) (if q<9 then 7*q else 7*q-64)
  let a := .bin .and sh (.reg .x6)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c (BitVec.ofNat 64 (2^64+4*entOff q-4096)))) (.c (~~~1#64)),.jump,3,3⟩
def dispatch9R : Result :=
  let a := .bin .and (.bin .sll (.reg .x17) (.c (BitVec.ofNat 64 13))) (.reg .x6)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c 256)) (.c (~~~1#64)),.jump,3,3⟩
/-- Field source of the dispatch into r6 group `h` (1..7): g1 = a6 bits 8..15 (no shift), g2..g6 = a6 >> 8(h-1),
g7 = a7 >> 47 (bits 119..126); masked with t4 = 0xFF00. -/
def r6Src (h : Nat) : E :=
  if h=1 then .reg .x16 else if h<7 then .bin .srl (.reg .x16) (.c (BitVec.ofNat 64 (8*h-8)))
  else .bin .srl (.reg .x17) (.c 47#64)
/-- `a4 = s2 - 256 raw` (table B, h < 4) or `256 raw + s2` (table A). -/
def r6A (h : Nat) : E :=
  if h<4 then .bin .sub (.reg .x18) (.bin .and (r6Src h) (.reg .x29))
  else .bin .add (.bin .and (r6Src h) (.reg .x29)) (.reg .x18)
/-- The jalr immediate of the dispatch into r6 group `h` (sign-extended): 4 (64 row0 + off - 212992). -/
def r6Imm (h : Nat) : Word :=
  if h<4 then BitVec.ofNat 64 (2^64+4*r6Off h-256) else BitVec.ofNat 64 (4*r6Off h)
def r6DispR (h : Nat) : Result :=
  ⟨⟨RegFile.init.set .x14 (r6A h),[],[]⟩,.bin .and (.bin .add (r6A h) (.c (r6Imm h))) (.c (~~~1#64)),.jump,
    (if h=1 then 3 else 4),(if h=1 then 3 else 4)⟩
/-! ### R6 checksum chain 51
Group 16's dispatch is `addi a4,s8,89; slli a4,a4,11; jalr 1168(a4)`: with s8 = T - sum(d0..d50) it lands on word
`44836 + 512 s8`; `ckArm d` (d = s8 in 0..7) holds chain 51's code for digit d followed by the final tail at
`ckTail d` (main's tail without its sum check); every other reachable s8 (sum <= 228) lands on a zero word. -/
def ckE : E := .bin .sll (.bin .add (.reg .x24) (.c 89#64)) (.c 11#64)
def ckDispR : Result :=
  ⟨⟨RegFile.init.set .x14 ckE,[],[]⟩,.bin .and (.bin .add ckE (.c 1168#64)) (.c (~~~1#64)),.jump,3,3⟩
def ckArm (d : Nat) : Nat := 44836+512*d
def ckTail (d : Nat) : Nat := ckArm d+partLen 17 d
/-- Landing word of the checksum dispatch for data digit sum `ds` (s8 = topT - ds). -/
def ckWord (ds : Nat) : Nat := 44836+512*topT-512*ds
/-- The dispatch at the end of top group `q` (into group q+1, or the checksum dispatch after group 16). -/
def nextDispR (q : Nat) : Result :=
  if q<7 then r6DispR (q+1) else if q=8 then dispatch9R else if q<16 then dispatchR (q+1) else ckDispR
def rungsOK (q d0 sl p : Nat) : Bool :=
  (List.range' d0 (mx q-d0)).all fun m =>
    rOK (vrun (p+2*(m-d0)) 3)
      (rungR m (if m+1=mx q then some sl else none) (p+2*(m-d0)))
def tailsOK (q sl p : Nat) : Bool :=
  (List.range (mx q)).all fun m =>
    rOK (vrun (p+2*m+1) 2) (tailR (if m+1=mx q then some sl else none) (p+2*m+1))
def partOK (q i d p : Nat) (skip : Bool := false) : Bool :=
  if d=mx q then (if skip then rOK (vrun p 0) (emptyR p) else rOK (vrun p 4) (copyFH .x8 (off i) (slot i) p))
  else rOK (vrun p 8)
      (if d+1=mx q then headRHT .x8 (off i) d (slot i) p i
       else headRH .x8 (off i) d none p i) &&
    rungsOK q (d+1) (slot i) (p+5)
def s8Check (q k : Nat) : Bool :=
  (if q=0 then rOK (vrun (entW 0 k) 1) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k))) &&
  (if q=9 ∧ k%2=0 then rOK (vrun (cellW 9 k) 1) (bge9R (cellW 9 k)) else true)
def dispatchOK (q dB dC : Nat) : Bool :=
  if q<17 then rOK (vrun (pcX q dB dC) 5) (nextDispR q)
  else true
def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (slot (3*q)) (base q dB dC) &&
  rungsOK q 0 (slot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  partOK q (3*q+2) dC (pcC q dB dC) (skipBody q dB dC) && dispatchOK q dB dC
def inlineCheck (q k : Nat) : Bool :=
  let dA := kdig q k 0
  s8Check q k &&
  (if dA=mx q then
    (if skipA q k then rOK (vrun (leadPc q k) 0) (emptyR (leadPc q k))
     else rOK (vrun (leadPc q k) 4) (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q k)))
   else
    rOK (vrun (leadPc q k) (if dA+1=mx q then 3 else 4))
      (if dA+1=mx q then headJDTermF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
       else headJDF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA) &&
    rOK (vrun (gbase q k+2*dA+1) 2)
      (tailR (if dA+1=mx q then some (slot (3*q)) else none) (gbase q k+2*dA+1)) &&
    rungsOK q (dA+1) (slot (3*q)) (gbase q k+2*(dA+1))) &&
  partOK q (3*q+1) (kdig q k 1) (gB q k) (skipB q k) && partOK q (3*q+2) (kdig q k 2) (gC q k) (skipC q k) &&
  rOK (vrun (gX q k) 5) (nextDispR q)
def entCheck (q k : Nat) : Bool :=
  if rowInl q k then inlineCheck q k else
  let dA := kdig q k 0
  if dA=mx q then
    (if q=0 then rOK (vrun (leadPc q k) 1) (T3M.skipJB (gB q k))
     else rOK (vrun (leadPc q k) 7) (copyN .x8 (off (3*q)) (slot (3*q)) (gB q k)))
  else rOK (vrun (leadPc q k) 7)
    (if dA+1=mx q then headJDTerm .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
     else headJD .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA)
def tripleCheck (q : Nat) : Bool :=
  ((List.range ((mx q+1)^3)).all fun k => entCheck q k && s8Check q k) &&
  ((List.range ((mx q+1)^2)).all fun x => blockCheck q (x/(mx q+1)) (x%(mx q+1)))
def inlineGroupCheck (q lo n : Nat) : Bool := (List.range' lo n).all fun k => inlineCheck q k
/-- The word at `p` is zero (an illegal instruction: fetch faults). -/
def zeroAt (p : Nat) : Bool := (lcode p).head? == some 0#32
def raw6Valid (g raw : Nat) : Bool := if g=0 then decide (40≤raw) else decide (raw<216)
/-- Invalid r6 fields (g = 0: raw 3..39; g >= 1: raw 216..255) land on zero words. -/
def guard6Check (g raw : Nat) : Bool := raw6Valid g raw || (g=0 && decide (raw<3)) || zeroAt (cell6 g raw)
def guard6All (g : Nat) : Bool := (List.range 256).all (guard6Check g)
/-- Reachable checksum landings (data sum <= 228) outside the 8 arms are zero words. -/
def ckGuardCheck (ds : Nat) : Bool := decide (topT-7≤ds ∧ ds≤topT) || zeroAt (ckWord ds)
def ckGuardAll : Bool := (List.range 229).all ckGuardCheck
def ckArmCheck (d : Nat) : Bool := partOK 17 51 d (ckArm d)
def ckArmAll : Bool := (List.range 8).all ckArmCheck
theorem piece_steps45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<257181) (s : MachineState) (hpc : s.pc=pcOf p)
    (ho : ∀o∈r.st.obl,o.holds s) :
    Steps Images.verifyImage s r.steps r.cycles (r.toState s) := by
  exact symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)
theorem piece_ecall45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<257181) (s : MachineState) (ho : ∀o∈r.st.obl,o.holds s)
    (hst : r.stop=.ecall) :
    fetch Images.verifyImage (r.toState s)=some (.base .ECALL) := by
  exact symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst
end SigGolfCandidate.T3M.Nonbinary
end
