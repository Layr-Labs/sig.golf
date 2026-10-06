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
def dispatchWords : List (BitVec 32) := [0x5e8713,0xa71713,0x70067]
def armPC (rank : Nat) : Nat := 256 * (rank + 1)
def dispatchR : Result :=
  let ptr := .bin .sll (.bin .add (.reg .x29) (.c 5)) (.c 10)
  ⟨⟨RegFile.init.set .x14 ptr, [], []⟩,
    .bin .and ptr (.c (~~~1#64)), .jump, 3, 3⟩
theorem dispatch_run (pc : Word) : symRun {} dispatchWords pc 3 = some dispatchR := by
  rfl
def pcOf (p : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * p)
theorem dispatch_target (k : Nat) (hk : k < 64) :
    (((BitVec.ofNat 64 k + 5#64) <<< 10) &&& ~~~1#64) =
      pcOf (armPC k) := by
  interval_cases k <;> decide +kernel
theorem dispatch_steps {image : Image} (pc : Word) (hc : CodeAt image pc dispatchWords)
    (s : MachineState) (hp : s.pc = pc) (k : Nat) (hk : k < 64)
    (hr : s.getReg .x29 = BitVec.ofNat 64 k) (hb : s.getReg .x15 = 262144#64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (armPC k) ∧
      (∀ r, r ≠ .x14 → t.getReg r = s.getReg r) ∧
      (∀ a, t.getMem a = s.getMem a) ∧ t.getReg .x15 = 262144#64 := by
  let t := dispatchR.toState s
  have st : Steps image s 3 3 t := symRun_sound (dispatch_run pc) hc s hp (by simp [dispatchR, Result.obligs, Oblig.all])
  refine ⟨t, st, ?_, ?_, ?_, ?_⟩
  · change (((s.getReg .x29 + 5#64) <<< 10) &&& ~~~1#64) = _
    rw [hr]
    exact dispatch_target k hk
  · intro r hn
    rw [Result.toState_getReg]
    change (RegFile.get (RegFile.set RegFile.init .x14 _) r).eval s = _
    rw [RegFile.get_set_ne _ _ hn, RegFile.init_get_eval]
  · intro a
    simp [t, dispatchR, Result.toState_getMem, memEval]
  · rw [Result.toState_getReg]
    change (RegFile.get (RegFile.set RegFile.init .x14 _) .x15).eval s = _
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.init_get_eval, hb]
end SigGolfCandidate.T3M.Nonbinary.TailDispatch
end

section


namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
def mx (q : Nat) : Nat := if q<17 then 4 else 3
def off (i : Nat) : Word := BitVec.ofNat 64 (64*(53-i))-BitVec.ofNat 64 1664
def slot (i : Nat) : Nat := if i=0 then 512 else 528+16*i
def baseTab : List Nat := [184791,184832,184871,184908,184942,184974,185013,185050,185085,185117,185147,185184,185219,185252,185282,185310,185344,185376,185406,185433,185458,185490,185520,185548,185573,185596,185637,185676,185713,185747,185779,185818,185855,185890,185922,185952,185989,186024,186057,186087,186115,186149,186181,186211,186238,186263,186295,186325,186353,186378,186401,186442,186481,186518,186552,186584,186623,186660,186695,186727,186757,186794,186829,186862,186892,186920,186954,186986,187016,187043,187068,187100,187130,187158,187183,187206,187247,187286,187323,187357,187389,187428,187465,187500,187532,187562,187599,187634,187667,187697,187725,187759,187791,187821,187848,187873,187905,187935,187963,187988,188011,188052,188091,188128,188162,188194,188233,188270,188305,188337,188367,188404,188439,188472,188502,188530,188564,188596,188626,188653,188678,188710,188740,188768,188793,188816,188857,188896,188933,188967,188999,189038,189075,189110,189142,189172,189209,189244,189277,189307,189335,189369,189401,189431,189458,189483,189515,189545,189573,189598,189621,189662,189701,189738,189772,189804,189843,189880,189915,189947,189977,190014,190049,190082,190112,190140,190174,190206,190236,190263,190288,190320,190350,190378,190403,190426,190467,190506,190543,190577,190609,190648,190685,190720,190752,190782,190819,190854,190887,190917,190945,190979,191011,191041,191068,191093,191125,191155,191183,191208,191231,191272,191311,191348,191382,191414,191453,191490,191525,191557,191587,191624,191659,191692,191722,191750,191784,191816,191846,191873,191898,191930,191960,191988,192013,192036,192077,192116,192153,192187,192219,192258,192295,192330,192362,192392,192429,192464,192497,192527,192555,192589,192621,192651,192678,192703,192735,192765,192793,192818,192841,192882,192921,192958,192992,193024,193063,193100,193135,193167,193197,193234,193269,193302,193332,193360,193394,193426,193456,193483,193508,193540,193570,193598,193623,193646,193687,193726,193763,193797,193829,193868,193905,193940,193972,194002,194039,194074,194107,194137,194165,194199,194231,194261,194288,194313,194345,194375,194403,194428,194451,194492,194531,194568,194602,194634,194673,194710,194745,194777,194807,194844,194879,194912,194942,194970,195004,195036,195066,195093,195118,195150,195180,195208,195233,195256,195297,195336,195373,195407,195439,195478,195515,195550,195582,195612,195649,195684,195717,195747,195775,195809,195841,195871,195898,195923,195955,195985,196013,196038,196061,196102,196141,196178,196212,196244,196283,196320,196355,196387,196417,196454,196489,196522,196552,196580,196614,196646,196676,196703,196728,196760,196790,196818,196843,196866,196907,196946,196983,197017,197049,197088,197125,197160,197192,197222,197259,197294,197327,197357,197385,197419,197451,197481,197508,197533,197565,197595,197623,197648,197671,197712,197751,197788,197822,197854,197893,197930,197965,197997,198027,198064,198099,198132,198162,198190,198224,198256,198286,198313,198338,198370,198400,198428,198453,251343,251383,251421,251456,251490,251528,251564,251597,251629,251664,251697,251727,251756,251790,251822,251851]
def base (q dB dC : Nat) : Nat :=
  baseTab.getD (if q<17 then 25*q+5*dB+dC else 425+4*dB+dC) 0
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 5 else 4+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
def pcX (q dB dC : Nat) : Nat := pcC q dB dC+partLen q dC
def entOff (q : Nat) : Nat := if q=0 then 8 else if q≤9 then 9+6*q else if q≤13 then 10+6*q else if q=14 then 129 else if q=15 then 170 else 211
def cellW (q k : Nat) : Nat := if q<17 then 256*(124-k)+entOff q else 256*(k+1)
def entW (q k : Nat) : Nat := cellW q k + (if q=9 ∧ k%2=0 then 1 else 0)
def inl (q : Nat) : Bool := decide (13 ≤ q ∧ q ≤ 16)
def leadOff (q : Nat) : Nat := if q=0 then 2 else 1
def leadPc (q k : Nat) : Nat := entW q k+leadOff q
def kdig (q k j : Nat) : Nat := k/(mx q+1)^j%(mx q+1)
def gbase (q k : Nat) : Nat :=
  if inl q then
    (if kdig q k 0=mx q then leadPc q k+3-2*mx q
     else if kdig q k 0+1=mx q then leadPc q k+2-2*kdig q k 0
     else leadPc q k+3-2*kdig q k 0)
  else base q (kdig q k 1) (kdig q k 2)
def gB (q k : Nat) : Nat := gbase q k+2*mx q+1
def gC (q k : Nat) : Nat := gB q k+partLen q (kdig q k 1)
def gX (q k : Nat) : Nat := gC q k+partLen q (kdig q k 2)
def kss (q k : Nat) : Nat := kdig q k 0+kdig q k 1+kdig q k 2
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
  ⟨⟨RegFile.init.set .x24 (addC (.reg .x24) (BitVec.ofNat 64 n)),[],[]⟩,.c (pcOf (p+1)),.fuel,1,1⟩
def guardW (k : Nat) : Nat := 256*(124-k)+255
def guardR (k : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (.c (BitVec.ofNat 64 (kss 0 k)-129#64)),[],[]⟩,
    .ite .geu (.reg .x29) (.reg .x11) (.c (pcOf (guardW k))) (.c (pcOf (cellW 0 k+2))),.branch,2,2⟩
def rejJ : Result := ⟨SymState.init,.c (pcOf 129638),.jump,1,1⟩
def bge9R (p : Nat) : Result :=
  ⟨SymState.init,.ite .ge (.reg .x16) (.c 0) (.c (BitVec.ofNat 64 (0x1000+4*p-1024))) (.c (pcOf (p+1))),.branch,1,1⟩
def tailR (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 1 else 0
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (.c (BitVec.ofNat 64 a))
      | none => RegFile.init), [], []⟩, .c (pcOf (p + n)), .ecall, n, n⟩
def headRHT (rb : Reg) (o : Word) (d sl p i : Nat) : Result :=
  {headRH rb o d (some sl) p i with pc:=.c (pcOf (p+4)),steps:=4,cycles:=4}
def shift10 (w : Reg) (b : Nat) : E :=
  if b<10 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (10-b)))
  else .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b-10)))
def dispatchR (q : Nat) : Result :=
  let sh := shift10 (if q<9 then .x16 else .x17) (if q<9 then 7*q else 7*q-64)
  let a := .bin .and sh (.reg .x6)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c (BitVec.ofNat 64 (1024+4*entOff q)))) (.c (~~~1#64)),.jump,3,3⟩
def dispatch9R : Result :=
  let a := .bin .and (.bin .sll (.reg .x17) (.c (BitVec.ofNat 64 11))) (.reg .x6)
  ⟨⟨RegFile.init.set .x14 (.bin .add a (.c 1536)),[],[]⟩,
    .bin .and (.bin .add a (.c 2300)) (.c (~~~1#64)),.jump,4,4⟩
def tailDispatchR : Result := TailDispatch.dispatchR
def rungsOK (q d0 sl p : Nat) : Bool :=
  (List.range' d0 (mx q-d0)).all fun m =>
    rOK (vrun (p+2*(m-d0)) 3)
      (rungR m (if m+1=mx q then some sl else none) (p+2*(m-d0)))
def tailsOK (q sl p : Nat) : Bool :=
  (List.range (mx q)).all fun m =>
    rOK (vrun (p+2*m+1) 2) (tailR (if m+1=mx q then some sl else none) (p+2*m+1))
def partOK (q i d p : Nat) : Bool :=
  if d=mx q then rOK (vrun p 4) (copyFH .x8 (off i) (slot i) p)
  else rOK (vrun p 8)
      (if d+1=mx q then headRHT .x8 (off i) d (slot i) p i
       else headRH .x8 (off i) d none p i) &&
    rungsOK q (d+1) (slot i) (p+5)
def entCheck (q k : Nat) : Bool :=
  let dA := kdig q k 0
  if dA=mx q then rOK (vrun (leadPc q k) 7)
    (copyN .x8 (off (3*q)) (slot (3*q)) (gB q k))
  else rOK (vrun (leadPc q k) 7)
    (if dA+1=mx q then headJDTerm .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
     else headJD .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA)
def s8Check (q k : Nat) : Bool :=
  (if q=0 then rOK (vrun (entW 0 k) 3) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k))) &&
  (if q=9 ∧ k%2=0 then rOK (vrun (cellW 9 k) 1) (bge9R (cellW 9 k)) else true)
def dispatchOK (q dB dC : Nat) : Bool :=
  if q<17 then rOK (vrun (pcX q dB dC) 5) (if q=8 then dispatch9R else if q<16 then dispatchR (q+1) else tailDispatchR)
  else true
def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (slot (3*q)) (base q dB dC) &&
  rungsOK q 0 (slot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  partOK q (3*q+2) dC (pcC q dB dC) && dispatchOK q dB dC
def tripleCheck (q : Nat) : Bool :=
  ((List.range ((mx q+1)^3)).all fun k => entCheck q k && s8Check q k) &&
  ((List.range ((mx q+1)^2)).all fun x => blockCheck q (x/(mx q+1)) (x%(mx q+1)))
def inlineCheck (q k : Nat) : Bool :=
  let dA := kdig q k 0
  s8Check q k &&
  (if dA=mx q then rOK (vrun (leadPc q k) 4) (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q k))
   else
    rOK (vrun (leadPc q k) (if dA+1=mx q then 3 else 4))
      (if dA+1=mx q then headJDTermF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
       else headJDF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA) &&
    rOK (vrun (gbase q k+2*dA+1) 2)
      (tailR (if dA+1=mx q then some (slot (3*q)) else none) (gbase q k+2*dA+1)) &&
    rungsOK q (dA+1) (slot (3*q)) (gbase q k+2*(dA+1))) &&
  partOK q (3*q+1) (kdig q k 1) (gB q k) && partOK q (3*q+2) (kdig q k 2) (gC q k) &&
  rOK (vrun (gX q k) 5) (if q<16 then dispatchR (q+1) else tailDispatchR)
def inlineGroupCheck (q lo n : Nat) : Bool := (List.range' lo n).all fun k => inlineCheck q k
def rejCheck : Bool :=
  (List.range 125).all fun k => rOK (vrun (guardW k) 1) rejJ
theorem piece_steps45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<251927) (s : MachineState) (hpc : s.pc=pcOf p)
    (ho : ∀o∈r.st.obl,o.holds s) :
    Steps Images.verifyImage s r.steps r.cycles (r.toState s) := by
  exact symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)
theorem piece_ecall45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<251927) (s : MachineState) (ho : ∀o∈r.st.obl,o.holds s)
    (hst : r.stop=.ecall) :
    fetch Images.verifyImage (r.toState s)=some (.base .ECALL) := by
  exact symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst
end SigGolfCandidate.T3M.Nonbinary
end
