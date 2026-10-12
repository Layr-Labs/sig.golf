import Mathlib.Tactic
import SigGolfCandidate.T3M.Verify.ChainRuns

section



namespace SigGolfCandidate.T3M.Nonbinary.TailDispatch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
def lstBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && lstBeq f as bs
  | _, _ => false
theorem lstBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, lstBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [lstBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [lstBeq] at h
    | cons b bs =>
      simp only [lstBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]
def rfBeq (a b : RegFile) : Bool := lstBeq E.beq a.fields b.fields
theorem rfBeq_eq {a b : RegFile} (h : rfBeq a b = true) : a = b := by
  have := lstBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl
def wBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2
theorem wBeq_eq {a b : Addr × E} (h : wBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [wBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]
def stBeq (a b : SymState) : Bool :=
  rfBeq a.regs b.regs && lstBeq wBeq a.mem b.mem && lstBeq Oblig.beq a.obl b.obl
theorem stBeq_eq {a b : SymState} (h : stBeq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [stBeq, Bool.and_eq_true] at h
  rw [rfBeq_eq h.1.1, lstBeq_eq (fun _ _ => wBeq_eq) h.1.2, lstBeq_eq (fun _ _ => Oblig.beq_eq) h.2]
def resBeq (a b : Result) : Bool :=
  stBeq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles
theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [stBeq_eq h1, E.beq_eq h2, h3, h4, h5]
def rOK (o : Option Result) (r : Result) : Bool :=
  match o with
  | some r' => resBeq r' r
  | none => false
theorem rOK_eq {o : Option Result} {r : Result} (h : rOK o r = true) : o = some r := by
  cases o with
  | none => simp [rOK] at h
  | some r' => simp only [rOK] at h; rw [resBeq_eq h]
def dispatchWords : List (BitVec 32) := [0x5ace8713,0x00971713,0x00070067]
def armPC (rank : Nat) : Nat := 184832 + 128 * rank
def dispatchR : Result :=
  let ptr := .bin .sll (.bin .add (.reg .x29) (.c 1452)) (.c 9)
  ⟨⟨RegFile.init.set .x14 ptr, [], []⟩,
    .bin .and ptr (.c (~~~1#64)), .jump, 3, 3⟩
theorem dispatch_run (pc : Word) : symRun {} dispatchWords pc 3 = some dispatchR := by
  rfl
def pcOf (p : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * p)
theorem dispatch_target (k : Nat) (hk : k < 64) :
    ((((BitVec.ofNat 64 k + 1452#64) <<< 9) + 0#64) &&& ~~~1#64) =
      pcOf (armPC k) := by
  interval_cases k <;> decide +kernel
theorem dispatch_steps {image : Image} (pc : Word) (hc : CodeAt image pc dispatchWords)
    (s : MachineState) (hp : s.pc = pc) (k : Nat) (hk : k < 64)
    (hr : s.getReg .x29 = BitVec.ofNat 64 k) (hb : s.getReg .x2 = 0x7fc00#64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (armPC k) ∧
      (∀ r, r ≠ .x14 → t.getReg r = s.getReg r) ∧
      (∀ a, t.getMem a = s.getMem a) ∧ t.getReg .x2 = 0x7fc00#64 := by
  let t := dispatchR.toState s
  have st : Steps image s 3 3 t := symRun_sound (dispatch_run pc) hc s hp (by simp [dispatchR, Result.obligs, Oblig.all])
  refine ⟨t, st, ?_, ?_, ?_, ?_⟩
  · change (((s.getReg .x29 + 1452#64) <<< 9) &&& ~~~1#64) = _
    rw [hr]
    simpa using dispatch_target k hk
  · intro r hn
    rw [Result.toState_getReg]
    change (RegFile.get (RegFile.set RegFile.init .x14 _) r).eval s = _
    rw [RegFile.get_set_ne _ _ hn, RegFile.init_get_eval]
  · intro a
    simp [t, dispatchR, Result.toState_getMem, memEval]
  · rw [Result.toState_getReg]
    change (RegFile.get (RegFile.set RegFile.init .x14 _) .x2).eval s = _
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.init_get_eval, hb]
end SigGolfCandidate.T3M.Nonbinary.TailDispatch
end

section


namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
/-- Largest digit of the chains of top group `q`: the 17 base-5 triples (q < 17) have 4; group 17 (chains 51..53,
campaign T8D / TOP2 NF17) holds the three radix-8 chains, largest digit 7. -/
def mx (q : Nat) : Nat := if q<17 then 4 else 7
def off (i : Nat) : Word := BitVec.ofNat 64 (64*(53-i))-BitVec.ofNat 64 1664
def slot (i : Nat) : Nat := 25168+16*i
def slotOffset (a : Nat) : Nat := a-24624
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
def base (q dB dC : Nat) : Nat :=
  baseTab.getD (if q<17 then 25*q+5*dB+dC else 425+4*dB+dC) 0
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 5 else 4+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
def pcX (q dB dC : Nat) : Nat := pcC q dB dC+partLen q dC
def entOff (q : Nat) : Nat :=
  if q=0 then 1315 else if q=1 then 1350 else if q=2 then 548 else if q=3 then 582
  else if q=4 then 804 else if q=5 then 838 else if q=6 then 1444 else if q=7 then 1478
  else if q=8 then 676 else if q=9 then 64 else if q=10 then 710 else if q=11 then 932
  else if q=12 then 966 else if q=13 then 1276 else if q=14 then 1532 else if q=15 then 764 else 1188
def cellW (q k : Nat) : Nat := if q<17 then 1024*(125-k)+entOff q else TailDispatch.armPC (k%64)
def entW (q k : Nat) : Nat := cellW q k + (if q=0 ∨ (q=9 ∧ k%2=0) then 1 else 0)
def inl (q : Nat) : Bool := decide (q=9 ∨ (13 ≤ q ∧ q ≤ 16))
def leadOff (q : Nat) : Nat := 1
def leadPc (q k : Nat) : Nat := entW q k+leadOff q
def kdig (q k j : Nat) : Nat := k/(mx q+1)^j%(mx q+1)
def kss (q k : Nat) : Nat := kdig q k 0+kdig q k 1+kdig q k 2
def rowInl (q k : Nat) : Bool := inl q || decide (q<17 ∧ 3≤kss q k)
def gbase (q k : Nat) : Nat :=
  if rowInl q k then
    (if kdig q k 0=mx q then leadPc q k+3-2*mx q
     else if kdig q k 0+1=mx q then leadPc q k+2-2*kdig q k 0
     else leadPc q k+3-2*kdig q k 0)
  else base q (kdig q k 1) (kdig q k 2)
def skipA (q k : Nat) : Bool := decide (q=0 ∧ kdig q k 0=mx q)
def skipB (q k : Nat) : Bool := rowInl q k && decide (kdig q k 0=mx q ∧ kdig q k 1=mx q)
def skipC (q k : Nat) : Bool := rowInl q k && decide (kdig q k 1=mx q ∧ kdig q k 2=mx q)
def gB (q k : Nat) : Nat := gbase q k+2*mx q+1-(if skipA q k then 4 else 0)
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
def guardR (k : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (.c (144#64-BitVec.ofNat 64 (kss 0 k))),[],[]⟩,
    .c (pcOf (cellW 0 k+2)),.fuel,1,1⟩
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
def tailDispatchR : Result := TailDispatch.dispatchR
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
  if q<17 then rOK (vrun (pcX q dB dC) 5) (if q=8 then dispatch9R else if q<16 then dispatchR (q+1) else tailDispatchR)
  else true
def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (slot (3*q)) (base q dB dC) &&
  rungsOK q 0 (slot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  partOK q (3*q+2) dC (pcC q dB dC) && dispatchOK q dB dC
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
  rOK (vrun (gX q k) 5) (if q=8 then dispatch9R else if q<16 then dispatchR (q+1) else tailDispatchR)
def entCheck (q k : Nat) : Bool :=
  if rowInl q k then inlineCheck q k else
  let dA := kdig q k 0
  if dA=mx q then rOK (vrun (leadPc q k) 7)
    (copyN .x8 (off (3*q)) (slot (3*q)) (gB q k))
  else rOK (vrun (leadPc q k) 7)
    (if dA+1=mx q then headJDTerm .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
     else headJD .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA)
def tripleCheck (q : Nat) : Bool :=
  ((List.range ((mx q+1)^3)).all fun k => entCheck q k && s8Check q k) &&
  ((List.range ((mx q+1)^2)).all fun x => blockCheck q (x/(mx q+1)) (x%(mx q+1)))
def inlineGroupCheck (q lo n : Nat) : Bool := (List.range' lo n).all fun k => inlineCheck q k
/-! ### Group 17 (campaign T8D, TOP2 NF17): the radix-8 chains 51..53
The tail dispatch of group 16 jumps to the slot `33512 + 64*k` with `k = d51 + 8 d52` (the top field, bits 122..127):
`addi s8,s8,-(d51+d52)`, falling directly into `BLOCK[k]`. `BLOCK[k]` = chain 51 code, chain 52 code (main's top chain code with largest digit
7: copy / terminal head / head + rungs, `partOK 17`), then the general-field dispatch `srli a4,a7,47;
andi a4,a4,1792; add a4,a4,t1; jalr 2032(a4)` directly into the complete copied chain-53 suffix
(`y = d53`, bits 119..121), bypassing the dead padding slot `r8SlotW y = 130299+64*y`.
The reverse checksum remains `144 - sum (digits 0..52)` throughout chain 53.
`SUFFIX[y]` = chain 53 code, then main's final tail at `finW y` (its `bne`
goes to a local `j REJ` stub). -/
def r8Blk : List Nat := [219217,219258,219297,219334,219369,219402,219433,219461,219488,219527,219564,219599,219632,219663,219692,219718,219743,219780,219815,219848,219879,219908,219935,219959,219982,220017,220050,220081,220110,220137,220162,220184,220205,220238,220269,220298,220325,220350,220373,220393,220412,220443,220472,220499,220524,220547,220568,220586,220603,220631,220657,220681,220703,220723,220741,220756,220770,220797,220822,220845,220866,220885,220902,220916]
def r8Suf : List Nat := [220929,220956,220981,221004,221025,221044,221061,221075]
def blkW (k : Nat) : Nat := TailDispatch.armPC k + 1
def r8SlotW (y : Nat) : Nat := 130299+64*y
def sufW (y : Nat) (alt : Bool := false) : Nat := r8SlotW y+1+(if alt then 32 else 0)
def finW (y : Nat) (alt : Bool := false) : Nat := sufW y alt+partLen 17 y-(if alt && decide (y=7) then 4 else 0)
/-- Two-instruction slot `addi s8,s8,-n; j tgt`. -/
def jR (n tgt : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (addC (.reg .x24) (-BitVec.ofNat 64 n)),[],[]⟩,.c (pcOf tgt),.jump,2,2⟩
def genDispE : E := .bin .add (.bin .and (.bin .srl (.reg .x17) (.c 47#64)) (.c 1792#64)) (.reg .x2)
/-- The general-field dispatch `srli a4,a7,47; andi a4,a4,1792; add a4,a4,t1; jalr 2032(a4)`. -/
def genDispR (alt : Bool := false) : Result :=
  ⟨⟨RegFile.init.set .x14 genDispE,[],[]⟩,.bin .and (.bin .add genDispE (.c (if alt then 2032#64 else 1904#64))) (.c (~~~1#64)),.jump,4,4⟩
theorem r8Blk_lt_all : (List.range 64).all (fun k => decide (blkW k+41<257181))=true := by decide +kernel
theorem r8Suf_lt_all : (List.range 8).all (fun y => decide (finW y+8<257181))=true := by decide +kernel
theorem blkW_lt (k : Nat) (hk : k<64) : blkW k+41<257181 := by
  have h := List.all_eq_true.mp r8Blk_lt_all k (List.mem_range.mpr hk)
  simpa using h
theorem finW_lt (y : Nat) (hy : y<8) : finW y+8<257181 := by
  have h := List.all_eq_true.mp r8Suf_lt_all y (List.mem_range.mpr hy)
  simpa using h
def r8BlkCheck (k : Nat) : Bool :=
  rOK (vrun (TailDispatch.armPC k) 1) (s8R (k%8+k/8) (TailDispatch.armPC k)) &&
  partOK 17 51 (k%8) (blkW k) && partOK 17 52 (k/8) (blkW k+partLen 17 (k%8)) (decide (k=63)) &&
  rOK (vrun (blkW k+partLen 17 (k%8)+partLen 17 (k/8)-(if k=63 then 4 else 0)) 4) (genDispR (decide (k/8=7)))
def r8SufCheck (y : Nat) (alt : Bool := false) : Bool :=
  partOK 17 53 y (sufW y alt) (alt && decide (y=7))
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
