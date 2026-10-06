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
def dispatchWords : List (BitVec 32) := [0xae9713,0xf70733,0xd6870067]
def armPC (rank : Nat) : Nat := 176986 + 256 * rank
def dispatchR : Result :=
  let ptr := .bin .add (.bin .sll (.reg .x29) (.c 10)) (.reg .x15)
  ⟨⟨RegFile.init.set .x14 ptr, [], []⟩,
    .bin .and (.bin .add ptr (.c 18446744073709550952)) (.c (~~~1#64)), .jump, 3, 3⟩
theorem dispatch_run (pc : Word) : symRun {} dispatchWords pc 3 = some dispatchR := by
  rfl
def pcOf (p : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * p)
theorem dispatch_target (k : Nat) (hk : k < 64) :
    ((((BitVec.ofNat 64 k <<< 10) + 712704#64) + 18446744073709550952#64) &&& ~~~1#64) =
      pcOf (armPC k) := by
  interval_cases k <;> decide +kernel
theorem dispatch_steps {image : Image} (pc : Word) (hc : CodeAt image pc dispatchWords)
    (s : MachineState) (hp : s.pc = pc) (k : Nat) (hk : k < 64)
    (hr : s.getReg .x29 = BitVec.ofNat 64 k) (hb : s.getReg .x15 = 712704#64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (armPC k) ∧
      (∀ r, r ≠ .x14 → t.getReg r = s.getReg r) ∧
      (∀ a, t.getMem a = s.getMem a) ∧ t.getReg .x15 = 712704#64 := by
  let t := dispatchR.toState s
  have st : Steps image s 3 3 t := symRun_sound (dispatch_run pc) hc s hp (by simp [dispatchR, Result.obligs, Oblig.all])
  refine ⟨t, st, ?_, ?_, ?_, ?_⟩
  · change (((s.getReg .x29 <<< 10) + s.getReg .x15 + 18446744073709550952#64) &&& ~~~1#64) = _
    rw [hr, hb]
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
def baseTab : List Nat := [82075,82116,82155,82192,82226,82258,82297,82334,82369,82401,82431,82468,82503,82536,82566,82594,82628,82660,82690,82717,82742,82774,82804,82832,82857,82880,82921,82960,82997,83031,83063,83102,83139,83174,83206,83236,83273,83308,83341,83371,83399,83433,83465,83495,83522,83547,83579,83609,83637,83662,83685,83726,83765,83802,83836,83868,83907,83944,83979,84011,84041,84078,84113,84146,84176,84204,84238,84270,84300,84327,84352,84384,84414,84442,84467,84490,84531,84570,84607,84641,84673,84712,84749,84784,84816,84846,84883,84918,84951,84981,85009,85043,85075,85105,85132,85157,85189,85219,85247,85272,85295,85336,85375,85412,85446,85478,85517,85554,85589,85621,85651,85688,85723,85756,85786,85814,85848,85880,85910,85937,85962,85994,86024,86052,86077,86100,86141,86180,86217,86251,86283,86322,86359,86394,86426,86456,86493,86528,86561,86591,86619,86653,86685,86715,86742,86767,86799,86829,86857,86882,86905,86946,86985,87022,87056,87088,87127,87164,87199,87231,87261,87298,87333,87366,87396,87424,87458,87490,87520,87547,87572,87604,87634,87662,87687,87710,87751,87790,87827,87861,87893,87932,87969,88004,88036,88066,88103,88138,88171,88201,88229,88263,88295,88325,88352,88377,88409,88439,88467,88492,88515,88556,88595,88632,88666,88698,88737,88774,88809,88841,88871,88908,88943,88976,89006,89034,89068,89100,89130,89157,89182,89214,89244,89272,89297,89320,89361,89400,89437,89471,89503,89542,89579,89614,89646,89676,89713,89748,89781,89811,89839,89873,89905,89935,89962,89987,90019,90049,90077,90102,90125,90166,90205,90242,90276,90308,90347,90384,90419,90451,90481,90518,90553,90586,90616,90644,90678,90710,90740,90767,90792,90824,90854,90882,90907,90930,90971,91010,91047,91081,91113,91152,91189,91224,91256,91286,91323,91358,91391,91421,91449,91483,91515,91545,91572,91597,91629,91659,91687,91712,91735,91776,91815,91852,91886,91918,91957,91994,92029,92061,92091,92128,92163,92196,92226,92254,92288,92320,92350,92377,92402,92434,92464,92492,92517,92540,92581,92620,92657,92691,92723,92762,92799,92834,92866,92896,92933,92968,93001,93031,93059,93093,93125,93155,93182,93207,93239,93269,93297,93322,93345,93386,93425,93462,93496,93528,93567,93604,93639,93671,93701,93738,93773,93806,93836,93864,93898,93930,93960,93987,94012,94044,94074,94102,94127,94150,94191,94230,94267,94301,94333,94372,94409,94444,94476,94506,94543,94578,94611,94641,94669,94703,94735,94765,94792,94817,94849,94879,94907,94932,94955,94996,95035,95072,95106,95138,95177,95214,95249,95281,95311,95348,95383,95416,95446,95474,95508,95540,95570,95597,95622,95654,95684,95712,95737,251343,251383,251421,251456,251490,251528,251564,251597,251629,251664,251697,251727,251756,251790,251822,251851]
def base (q dB dC : Nat) : Nat :=
  baseTab.getD (if q<17 then 25*q+5*dB+dC else 425+4*dB+dC) 0
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 5 else 4+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
def pcX (q dB dC : Nat) : Nat := pcC q dB dC+partLen q dC
def entOff (q : Nat) : Nat := if q=0 then 0 else if q≤13 then 6*q+1 else if q=14 then 120 else if q=15 then 161 else if q=16 then 202 else 242
def entW (q k : Nat) : Nat := 176744+256*k+entOff q
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
def guardR (k : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (.c (BitVec.ofNat 64 (kss 0 k)-129#64)),[],[]⟩,
    .ite .geu (.reg .x29) (.reg .x11) (.c (pcOf (176744+256*k+250))) (.c (pcOf (176744+256*k+2))),.branch,2,2⟩
def rejJ : Result := ⟨SymState.init,.c (pcOf 96230),.jump,1,1⟩
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
  let sh := shift10 (if q<9 then .x16 else .x17) (if q<9 then 7*q else 7*(q-9))
  let a := .bin .add (.bin .and sh (.reg .x6)) (.reg .x15)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c (BitVec.ofNat 64 (4*entOff q) + 18446744073709549984#64))) (.c (~~~1#64)),.jump,4,4⟩
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
  if q=0 then rOK (vrun (entW 0 k) 3) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k))
def dispatchOK (q dB dC : Nat) : Bool :=
  if q<17 then rOK (vrun (pcX q dB dC) 5) (if q<16 then dispatchR (q+1) else tailDispatchR) else true
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
  ((List.range 17).all fun q => (List.range' 125 3).all fun k => rOK (vrun (entW q k) 1) rejJ) &&
  ((List.range 125).all fun k => rOK (vrun (176744+256*k+250) 1) rejJ)
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
