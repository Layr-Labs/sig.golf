import Mathlib.Tactic
import SigGolfCandidate.T3M_Verify_ChainRuns

section


namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
/-! ### T51 top layer (verify image T51_T152_g791_c0hi, generator t51/verify/py/gen_t51v.py --c0hi)
Groups `q` in dispatch (= chain) order:
* `q < 9`: the radix-6 triples g0..g8 (chains `3q .. 3q+2`, largest digit 5, 216 ranks); cells `cell6`, shared
  bodies `body6` (chain-A rung ladder, chain B, chain C, next dispatch);
* `9 ≤ q < 16`: #938's radix-5 groups q9..q15 (chains 27..47, largest digit 4, 125 ranks), #938's code with the
  leaf-slot immediates moved by `-16` (endpad leaf); q15's last dispatch is #938's dispatch into group 8;
* `q = 16`: the radix-7 pair (chains 48 = A, 49 = B, largest digit 6, 49 ranks `k = d48 + 7 d49`, no chain C);
  cells in #938's q8 column `1024 (125 - k) + 676`, bodies `body7Tab` (ladder, chain 49, checksum dispatch);
* `q = 17`: the radix-6 checksum chain 50 (largest digit 5), arms `ckArm d` (d = 0..5). -/
/-- Largest digit of the chains of top group `q` (T51): r6 groups 5, #938's r5 groups 4, the r7 pair 6, the
checksum chain (group 17) 5. -/
def mx (q : Nat) : Nat := if q<9 then 5 else if q<16 then 4 else if q=16 then 6 else 5
/-- Top chain `i`'s block in the top chain area (even pairing, charge 86: pair `p = (2p, 2p+1)` at `104 (26 - p)`,
G chain at `+16`, F chain at `+40`; `= W9.T3M.chainSlot 0 i`). -/
def topSlot (i : Nat) : Nat := 104*(26-i/2)+16+24*(i%2)
/-- Top chain format (T51): chain `i` is G (value first) iff it is even and `i ≤ 50` (`= T3.topIsG`). -/
def topG (i : Nat) : Bool := decide (i%2=0 ∧ i ≤ 50)
def off (i : Nat) : Word := BitVec.ofNat 64 (topSlot i)-BitVec.ofNat 64 1664
/-- T51 endpad top leaf: `end_0` at 25216 (tp + 512), the tweak at 25232, `end_i` at `25232 + 16 i` (i ≥ 1). -/
def slot (i : Nat) : Nat := if i=0 then 25216 else 25232+16*i
/-- Target of chain `i`'s terminal hash: chain 0 (c0hi) writes its last 32-byte answer at `slot 0 - 16 = 25200`
(the HIGH half lands on `end_0`); every other chain at its slot. -/
def termSlot (i : Nat) : Nat := if i=0 then 25200 else slot i
def slotOffset (a : Nat) : Nat := a-24704
def rungR (d : Nat) (sl : Option Nat) (p : Nat) : Result :=
  T3M.rungRB d (sl.map slotOffset) p
def copyN (rb : Reg) (o : Word) (sl tgt : Nat) (g : Bool := false) : Result :=
  T3M.copyNB rb o (slotOffset sl) tgt g
def copyFH (rb : Reg) (o : Word) (sl p : Nat) (g : Bool := false) : Result :=
  T3M.copyFHB rb o (slotOffset sl) p g
def headRH (rb : Reg) (o : Word) (d : Nat) (sl : Option Nat) (p i : Nat) (g : Bool := false) : Result :=
  T3M.headRHB rb o d (sl.map slotOffset) p i g
def emptyR (p : Nat) : Result := ⟨SymState.init,.c (pcOf p),.fuel,0,0⟩
/-- T51 top target (the checksum digit is `topT - sum`). -/
def topT : Nat := 152
/-- r6 group `g` dispatches through table B (`s2 - 256 raw`: g1, g2, g3, g8) or table A (`256 raw + s2`: g4..g7). -/
def r6B (g : Nat) : Bool := decide (g<4 ∨ g=8)
def r6Off (g : Nat) : Nat := 40+6*(g%4)
/-- The 8-bit field value of rank `k` in r6 group `g` (g0: raw = rank + 40). -/
def rawOf6 (g k : Nat) : Nat := if g=0 then k+40 else k
/-- Cell of r6 group `g` for field value `raw`: g0 base-free column `512 (raw - 3) + 326`, table B rows
`3327 - raw`, table A rows `3328 + raw` (offset `r6Off g` inside the 64-word rows). -/
def cell6 (g raw : Nat) : Nat :=
  if g=0 then 512*(raw-3)+326 else if r6B g then 64*(3327-raw)+r6Off g else 64*(3328+raw)+r6Off g
def body6Tab : List Nat := [185001,185713,129188,98758,127558,72868,190819,185085,101958,77988,51748,26182,185855,102854,118948,76964,26405,21062,102982,123044,122020,26277,21285,805,128454,51782,26917,21797,14918,10788,126243,26788,21157,933,10822,1105,186537,189172,187130,186439,130112,51877,190320,188404,188532,128582,27044,46628,189804,190279,185216,52388,21668,25381,191093,185673,52644,46662,967,16165,130212,27078,21924,1317,10917,11557,52678,46757,25893,16677,13860,5925,189353,187049,191988,191722,132863,72357,187305,189097,187634,187719,52005,47268,191846,188656,188926,72485,21958,41508,191785,127140,72997,47524,1351,20261,132902,52517,25124,15908,11428,13894,76453,47558,41542,20773,13989,6437,191913,187500,189038,184942,132941,76581,188270,185129,186986,184791,67108,50724,185289,186341,187206,77093,25158,41637,190945,188585,92965,50758,15942,24357,132980,67142,25253,16037,11684,14500,93477,50853,42148,24869,14756,11084,185769,189225,186727,186213,133019,97061,190633,188073,188005,189947,67237,51364,188841,185960,190577,97573,25764,42404,186086,117284,101157,51620,16548,40484,133058,67748,26020,16804,11718,14790,101669,51654,42438,40518,21324,11596,186481,191401,185577,190426,133097,113188,191587,189993,187877,118180,68004,67365,130300,72228,121380,113222,26054,45604,73124,122276,113828,67877,16838,40613,133136,68038,50981,20004,15141,21836,114084,71461,45638,41124,22052,12069,189865,187247,190889,76324,133175,114118,188773,190761,77220,184832,71204,71973,185449,92708,93348,117319,51493,45733,93604,93383,117541,72265,20038,41380,133214,71238,66084,20133,15653,22086,118053,73161,46244,41414,22181,22821,189545,189609,191529,96804,184867,118215,190121,186862,97700,97444,71333,75557,191453,100900,97479,121415,66118,46500,101796,101540,121637,76069,20644,44580,186584,71844,66213,20900,19237,22692,122149,76361,46534,44614,22948,23372,191017,187759,103588,123334,122311,72100,188457,124068,123462,188231,77257,66724,128164,124358,188329,72134,49700,20934,126534,188999,75300,66980,44709,15013,125476,87588,49734,45220,22982,9764,75334,67014,24100,15524,9798,4644]
def body7Tab : List Nat := [26148,21028,711,14884,11045,8740,268]
def body6 (g dB dC : Nat) : Nat := body6Tab.getD (36*g+6*dB+dC) 0
def baseTab : List Nat := [184791,130112,98124,184908,129996,130212,185013,185050,133292,186153,185147,122700,711,186183,77482,185310,133324,186281,102698,83032,133356,186311,77610,84056,268,93382,132863,185676,127564,133388,185779,185818,122828,133420,186409,98252,123212,805,186665,77738,127692,133452,186921,102826,103513,133484,187100,77910,104537,1105,97478,186442,98636,127820,186552,186584,98764,123340,186695,187433,101964,186794,186829,187689,78122,127948,186954,187817,102954,108633,187068,187847,78250,118314,1804,187206,132902,102092,187323,187357,132941,102220,187465,133516,187945,187562,187599,933,187975,97834,187725,133548,188128,103082,118442,133580,188201,97962,118570,2129,98504,132980,188091,128332,133612,133019,188233,123468,133644,188337,188367,123596,967,188472,98090,128460,133676,188596,103210,118698,133708,188502,98218,119082,2316,101574,188857,102348,128588,184873,188999,102732,123724,189110,189142,102860,123852,189244,189277,98602,128716,189369,189401,103338,119210,189483,189515,98730,122410,2572,189621,133058,102988,189738,189772,133097,103116,189880,189915,188626,103244,190014,1317,188713,101930,190140,190174,188743,103722,122538,190288,188896,102058,190378,190403,102600,133136,190506,190543,185184,133175,190648,190685,185257,188969,190782,124236,1351,189662,190917,128844,185385,190049,191041,191068,185417,190249,191155,191183,191208,117958,133214,191311,128972,185513,191414,103372,124364,185545,191557,103756,126540,191659,191692,102186,129356,185641,191816,103850,122666,185897,191930,191960,122794,2829,192036,192077,192116,192153,192187,192219,192258,192295,192330,192362,192392,192429,192464,192497,192527,192555,192589,192621,192651,192678,192703,192735,192765,192793,192818,192841,133253,103884,192958,192992,193024,193063,193100,193135,193167,193197,193234,193269,193302,193332,193360,193394,193426,193456,193483,193508,193540,193570,193598,193623,193646,193687,193726,193763,193797,193829,193868,193905,193940,193972,194002,194039,194074,194107,194137,194165,194199,194231,194261,194288,194313,194345,194375,194403,194428,194451,194492,194531,194568,194602,194634,194673,194710,194745,194777,194807,194844,194879,194912,194942,194970,195004,195036,195066,195093,195118,195150,195180,195208,195233,195256,195297,195336,195373,195407,195439,195478,195515,195550,195582,195612,195649,195684,195717,195747,195775,195809,195841,195871,195898,195923,195955,195985,196013,196038,196061,196102,196141,196178,196212,196244,196283,196320,196355,196387,196417,196454,196489,196522,196552,196580,196614,196646,196676,196703,196728,196760,196790,196818,196843,196866,196907,196946,196983,197017,197049,197088,197125,197160,197192,197222,197259,197294,197327,197357,197385,197419,197451,197481,197508,197533,197565,197595,197623,197648,197671,197712,197751,197788,197822,197854,197893,197930,197965,197997,198027,198064,198099,198132,198162,198190,198224,198256,198286,198313,198338,198370,198400,198428,198453,254621,254661,254699,254734,254768,254806,254842,254875,254907,254942,254975,255005,255034,255068,255100,255129]
def base (q dB dC : Nat) : Nat :=
  if q<9 then body6 q dB dC else if q<16 then baseTab.getD (25*q+5*dB+dC) 0
  else if q=16 then body7Tab.getD dB 0 else baseTab.getD (425+4*dB+dC) 0
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 5 else 4+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
/-- r6 bodies omit chain C's copy when chains B and C both have the largest digit (C is buffer-safe). -/
def skipBody (q dB dC : Nat) : Bool := decide (q<9 ∧ dB=mx q ∧ dC=mx q)
/-- End of the body (next dispatch). The r7 pair (q = 16) has no chain C: its checksum dispatch is at `pcC`. -/
def pcX (q dB dC : Nat) : Nat :=
  if q=16 then pcC q dB dC else pcC q dB dC+partLen q dC-(if skipBody q dB dC then 4 else 0)
def entOff (q : Nat) : Nat :=
  if q=0 then 1315 else if q=1 then 1350 else if q=2 then 548 else if q=3 then 582
  else if q=4 then 804 else if q=5 then 838 else if q=6 then 1444 else if q=7 then 1478
  else if q=8 then 676 else if q=9 then 64 else if q=10 then 710 else if q=11 then 932
  else if q=12 then 966 else if q=13 then 1276 else if q=14 then 1532 else if q=15 then 764 else 1188
/-- First cell word of rank `k` in group `q`: r6 cells, #938's r5 column `1024 (125 - k) + entOff q`, the r7 pair in
#938's q8 column (`entOff 8 = 676`). -/
def cellW (q k : Nat) : Nat :=
  if q<9 then cell6 q (rawOf6 q k) else if q<16 then 1024*(125-k)+entOff q
  else if q=16 then 1024*(125-k)+entOff 8 else 0
def entW (q k : Nat) : Nat := cellW q k + (if q=9 ∧ k%2=0 then 1 else 0)
def inl (q : Nat) : Bool := decide (q=9 ∨ (13 ≤ q ∧ q ≤ 15))
def leadOff (q : Nat) : Nat := 1
def leadPc (q k : Nat) : Nat := entW q k+leadOff q
def kdig (q k j : Nat) : Nat := k/(mx q+1)^j%(mx q+1)
def kss (q k : Nat) : Nat := kdig q k 0+kdig q k 1+kdig q k 2
def rowInl (q k : Nat) : Bool := inl q || decide (9≤q ∧ q<16 ∧ 3≤kss q k)
def gbase (q k : Nat) : Nat :=
  if rowInl q k then
    (if kdig q k 0=mx q then leadPc q k+3-2*mx q
     else if kdig q k 0+1=mx q then leadPc q k+2-2*kdig q k 0
     else leadPc q k+3-2*kdig q k 0)
  else base q (kdig q k 1) (kdig q k 2)
/-- Shared-body groups: the r6 groups and the r7 pair. -/
def sharedG (q : Nat) : Bool := decide (q<9 ∨ q=16)
def skipA (q k : Nat) : Bool := decide (q=0 ∧ kdig q k 0=mx q)
def skipB (q k : Nat) : Bool := (rowInl q k || sharedG q) && decide (kdig q k 0=mx q ∧ kdig q k 1=mx q)
def skipC (q k : Nat) : Bool := (rowInl q k || decide (q<9)) && decide (kdig q k 1=mx q ∧ kdig q k 2=mx q)
/-- Start of chain B. Shared-body groups keep chain B's copy in the body; a buffer-safe chain B is jumped over (+4). -/
def gB (q k : Nat) : Nat :=
  if sharedG q then gbase q k+2*mx q+1+(if skipB q k then 4 else 0)
  else gbase q k+2*mx q+1-(if skipA q k then 4 else 0)
def gC (q k : Nat) : Nat := gB q k+partLen q (kdig q k 1)-(if skipB q k then 4 else 0)
/-- End of the group's code for rank `k` (the next dispatch); the r7 pair has no chain C. -/
def gX (q k : Nat) : Nat :=
  if q=16 then gC q k else gC q k+partLen q (kdig q k 2)-(if skipC q k then 4 else 0)
def headJD (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12 (addC (addC (.reg rb) o) (gOut g))).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,5,5⟩
def headJDTerm (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg rb) o)).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,4,4⟩
def headJDF (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) : Result :=
  {headJD rb o tgt i d g with stop:=.fuel,steps:=4,cycles:=4}
def headJDTermF (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  {headJDTerm rb o tgt i d with stop:=.fuel,steps:=3,cycles:=3}
def s8R (n p : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (addC (.reg .x24) (-BitVec.ofNat 64 n)),[],[]⟩,.c (pcOf (p+1)),.fuel,1,1⟩
/-- T51 group 0's first cell word `addi s8,zero,T-kss`. -/
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
/-- Field source of the dispatch into r6 group `h` (1..8): g1 = a6 bits 8..15 (no shift), g2..g6 = a6 >> 8(h-1),
g7 = a7 >> 40 (bits 112..119), g8 = a7 >> 48 (bits 120..127); masked with t4 = 0xFF00. -/
def r6Src (h : Nat) : E :=
  if h=1 then .reg .x16 else if h<7 then .bin .srl (.reg .x16) (.c (BitVec.ofNat 64 (8*h-8)))
  else if h=7 then .bin .srl (.reg .x17) (.c 40#64) else .bin .srl (.reg .x17) (.c 48#64)
/-- `a4 = s2 - 256 raw` (table B) or `256 raw + s2` (table A). -/
def r6A (h : Nat) : E :=
  if r6B h then .bin .sub (.reg .x18) (.bin .and (r6Src h) (.reg .x29))
  else .bin .add (.bin .and (r6Src h) (.reg .x29)) (.reg .x18)
/-- The jalr immediate of the dispatch into r6 group `h` (sign-extended): 4 (64 row0 + off - 212992). -/
def r6Imm (h : Nat) : Word :=
  if r6B h then BitVec.ofNat 64 (2^64+4*r6Off h-256) else BitVec.ofNat 64 (4*r6Off h)
def r6DispR (h : Nat) : Result :=
  ⟨⟨RegFile.init.set .x14 (r6A h),[],[]⟩,.bin .and (.bin .add (r6A h) (.c (r6Imm h))) (.c (~~~1#64)),.jump,
    (if h=1 then 3 else 4),(if h=1 then 3 else 4)⟩
/-- T51: the r6 mask word `0xFF00` is loaded by group 0's bodies (`ld t4,-288(s1)`: verify data word 16). -/
def maskE : E := .ld (.bin .add (.reg .x2) (.c (BitVec.ofNat 64 16)))
def g0A : E := .bin .sub (.c 856064#64) (.bin .and (.reg .x16) maskE)
/-- Group 0's next dispatch `ld t4,-288(s1); lui s2,209; and a4,a6,t4; sub a4,s2,a4; jalr -72(a4)` (into g1). -/
def g0DispR : Result :=
  ⟨⟨((RegFile.init.set .x29 maskE).set .x18 (.c 856064#64)).set .x14 g0A,[],
    [.valid ⟨some (.reg .x2),BitVec.ofNat 64 16⟩ 8]⟩,
    .bin .and (.bin .add g0A (.c (BitVec.ofNat 64 (2^64-72)))) (.c (~~~1#64)),.jump,5,5⟩
/-! ### T51 checksum chain 50
The r7 pair's bodies end with `addi a4,s8,89; slli a4,a4,11; jalr 1168(a4)`: with s8 = T - sum(d0..d49) it lands on
word `44836 + 512 s8`; `ckArm d` (d = s8 in 0..5) holds chain 50's code for digit d followed by the final tail at
`ckTail d` (#938's tail without its sum check); every other reachable s8 (sum <= 231) lands on a zero word. -/
def ckE : E := .bin .sll (.bin .add (.reg .x24) (.c 89#64)) (.c 11#64)
def ckDispR : Result :=
  ⟨⟨RegFile.init.set .x14 ckE,[],[]⟩,.bin .and (.bin .add ckE (.c 1168#64)) (.c (~~~1#64)),.jump,3,3⟩
def ckArm (d : Nat) : Nat := 44836+512*d
def ckTail (d : Nat) : Nat := ckArm d+partLen 17 d
/-- Landing word of the checksum dispatch for data digit sum `ds` (s8 = topT - ds). -/
def ckWord (ds : Nat) : Nat := 44836+512*topT-512*ds
/-- The dispatch at the end of top group `q`: q = 0 the 5-word g1 dispatch (mask/table setup), r6 groups into the
next r6 group, g8 into q9 (#938's dispatch9), q9..q14 into q+1, q15 into the r7 pair (#938's dispatch into group 8),
the r7 pair into the checksum arms. -/
def nextDispR (q : Nat) : Result :=
  if q=0 then g0DispR else if q<8 then r6DispR (q+1) else if q=8 then dispatch9R
  else if q<15 then dispatchR (q+1) else if q=15 then dispatchR 8 else ckDispR
def rungsOK (q d0 sl p : Nat) : Bool :=
  (List.range' d0 (mx q-d0)).all fun m =>
    rOK (vrun (p+2*(m-d0)) 3)
      (rungR m (if m+1=mx q then some sl else none) (p+2*(m-d0)))
def tailsOK (q sl p : Nat) : Bool :=
  (List.range (mx q)).all fun m =>
    rOK (vrun (p+2*m+1) 2) (tailR (if m+1=mx q then some sl else none) (p+2*m+1))
def partOK (q i d p : Nat) (skip : Bool := false) : Bool :=
  if d=mx q then (if skip then rOK (vrun p 0) (emptyR p) else rOK (vrun p 4) (copyFH .x8 (off i) (slot i) p (topG i)))
  else rOK (vrun p 8)
      (if d+1=mx q then headRHT .x8 (off i) d (slot i) p i
       else headRH .x8 (off i) d none p i (topG i)) &&
    rungsOK q (d+1) (slot i) (p+5)
def s8Check (q k : Nat) : Bool :=
  (if q=0 then rOK (vrun (entW 0 k) 1) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k))) &&
  (if q=9 ∧ k%2=0 then rOK (vrun (cellW 9 k) 1) (bge9R (cellW 9 k)) else true)
def dispatchOK (q dB dC : Nat) : Bool :=
  if q<17 then rOK (vrun (pcX q dB dC) 5) (nextDispR q) else true
/-- A shared body: chain A's rung ladder (tails and rungs; its terminal step targets `termSlot`), chain B, chain C
(absent for the r7 pair), the next dispatch. -/
def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (termSlot (3*q)) (base q dB dC) &&
  rungsOK q 0 (termSlot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  (decide (q=16) || partOK q (3*q+2) dC (pcC q dB dC) (skipBody q dB dC)) && dispatchOK q dB dC
def inlineCheck (q k : Nat) : Bool :=
  let dA := kdig q k 0
  s8Check q k &&
  (if dA=mx q then
    (if skipA q k then rOK (vrun (leadPc q k) 0) (emptyR (leadPc q k))
     else rOK (vrun (leadPc q k) 4) (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q k) (topG (3*q))))
   else
    rOK (vrun (leadPc q k) (if dA+1=mx q then 3 else 4))
      (if dA+1=mx q then headJDTermF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
       else headJDF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA (topG (3*q))) &&
    rOK (vrun (gbase q k+2*dA+1) 2)
      (tailR (if dA+1=mx q then some (termSlot (3*q)) else none) (gbase q k+2*dA+1)) &&
    rungsOK q (dA+1) (termSlot (3*q)) (gbase q k+2*(dA+1))) &&
  partOK q (3*q+1) (kdig q k 1) (gB q k) (skipB q k) && partOK q (3*q+2) (kdig q k 2) (gC q k) (skipC q k) &&
  rOK (vrun (gX q k) 5) (nextDispR q)
def entCheck (q k : Nat) : Bool :=
  if rowInl q k then inlineCheck q k else
  let dA := kdig q k 0
  if dA=mx q then
    (if q=0 then rOK (vrun (leadPc q k) 1) (T3M.skipJB (gB q k))
     else rOK (vrun (leadPc q k) 7) (copyN .x8 (off (3*q)) (slot (3*q)) (gB q k) (topG (3*q))))
  else rOK (vrun (leadPc q k) 7)
    (if dA+1=mx q then headJDTerm .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
     else headJD .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA (topG (3*q)))
/-- Live shared blocks: every block of an r6 group; the r7 pair's 7 bodies (`x = dB`); for #938's non-inline r5
groups only the blocks with `dB + dC < 3` (a row with `kss ≥ 3` is inline; the dead blocks are not checked). -/
def liveBlock (q x : Nat) : Bool :=
  if q=16 then blockCheck 16 x 0
  else if q<9 ∨ x/(mx q+1)+x%(mx q+1) < 3 then blockCheck q (x/(mx q+1)) (x%(mx q+1)) else true
/-- Number of ranks of group `q` (`216` r6, `125` r5, `49` the r7 pair). -/
def nRank (q : Nat) : Nat := if q=16 then 49 else (mx q+1)^3
/-- Number of shared-body indices of group `q` (`(mx+1)^2`; the r7 pair: 7, indexed by `dB`). -/
def nBlock (q : Nat) : Nat := if q=16 then 7 else (mx q+1)^2
def tripleCheck (q : Nat) : Bool :=
  ((List.range (nRank q)).all fun k => entCheck q k && s8Check q k) &&
  ((List.range (nBlock q)).all (liveBlock q))
def inlineGroupCheck (q lo n : Nat) : Bool := (List.range' lo n).all fun k => inlineCheck q k
/-! ### T51 guards -/
/-- The word at `p` is zero (an illegal instruction: fetch faults). -/
def zeroAt (p : Nat) : Bool := (lcode p).head? == some 0#32
def raw6Valid (g raw : Nat) : Bool := if g=0 then decide (40≤raw) else decide (raw<216)
/-- Invalid r6 fields (g = 0: raw 3..39; g >= 1: raw 216..255) land on zero words (g = 0, raw < 3: below the code). -/
def guard6Check (g raw : Nat) : Bool := raw6Valid g raw || (g=0 && decide (raw<3)) || zeroAt (cell6 g raw)
def guard6All (g : Nat) : Bool := (List.range 256).all (guard6Check g)
/-- Invalid r7 ranks 49..125 land on zero words (126, 127 land below the code). -/
def r7GuardCheck (k : Nat) : Bool := decide (k<49) || zeroAt (cellW 16 k)
def r7GuardAll : Bool := (List.range 126).all r7GuardCheck
/-- Reachable checksum landings (data sum <= 231) outside the 6 arms are zero words. -/
def ckGuardCheck (ds : Nat) : Bool := decide (topT-5≤ds ∧ ds≤topT) || zeroAt (ckWord ds)
def ckGuardAll : Bool := (List.range 232).all ckGuardCheck
def ckArmCheck (d : Nat) : Bool := partOK 17 50 d (ckArm d)
def ckArmAll : Bool := (List.range 6).all ckArmCheck
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
