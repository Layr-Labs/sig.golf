import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_Main_C

set_option Elab.async false


namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def stageBound (lay : Layer) : Nat := if lay.val=1 then 56 else if lay.val=2 then 41 else 22

def preparedAt (p : PreparedRoots) (lay : Layer) : PreparedLower :=
  if lay.val=1 then p.one else if lay.val=2 then p.two else p.three

def messageAt (p : PreparedRoots) (forest : Digest×Digest) (lay : Layer) : Digest×Digest :=
  if lay.val=1 then topPair 2 p.two.levels else if lay.val=2 then topPair 3 p.three.levels else forest

theorem Stable.prepared {index : Nat} {p : PreparedRoots} {forest : Digest×Digest} {s : MachineState}
    (h : Stable index p forest s) (lay : Layer) (hl : lay≠0) :
    SharedRootControl.Stored lay index (preparedAt p lay) s := by
  fin_cases lay <;> first | exact (hl rfl).elim | exact h.one | exact h.two | exact h.three

theorem Stable.message {index : Nat} {p : PreparedRoots} {forest : Digest×Digest} {s : MachineState}
    (h : Stable index p forest s) (lay : Layer) (hl : lay≠0) :
    DigAt s (0x66040+32*lay.val) (messageAt p forest lay).1 ∧
    DigAt s (0x66050+32*lay.val) (messageAt p forest lay).2 := by
  fin_cases lay
  · exact (hl rfl).elim
  · exact ⟨h.two.left,h.two.right⟩
  · exact ⟨h.three.left,h.three.right⟩
  · exact ⟨h.forestL,h.forestR⟩

theorem floor_small (lay : Layer) (hl : lay≠0) (r : Nat) (hr : r<stageBound lay) :
    CanonicalPolicy.threshold lay.val r<22 ∧ (lay.val=1 → CanonicalPolicy.threshold lay.val r<16) := by
  fin_cases lay
  · exact (hl rfl).elim
  · change CanonicalPolicy.threshold 1 r<22 ∧ (1=1 → CanonicalPolicy.threshold 1 r<16)
    have : CanonicalPolicy.threshold 1 r<16 := CanonicalPolicy.lower_one_floor_lt ⟨r,hr⟩
    exact ⟨by omega, fun _ => this⟩
  · change CanonicalPolicy.threshold 2 r<22 ∧ (2=1 → _)
    have : CanonicalPolicy.threshold 2 r≤19 := (CanonicalPolicy.lower_two_progress ⟨r,hr⟩).1
    exact ⟨by omega, fun h => absurd h (by decide)⟩
  · change CanonicalPolicy.threshold 3 r<22 ∧ (3=1 → _)
    rw [CanonicalPolicy.lower_three_progress r hr];exact ⟨hr, fun h => absurd h (by decide)⟩

theorem next_stage_bound (lay : Layer) (hl : lay≠0) (r : Nat) (hr : r<stageBound lay)
    (low : Bool) (ds : List Nat) (hd : CanonicalPolicy.threshold lay.val r≤CanonicalPolicy.credit lay low ds) :
    (∀ hnext : lay.val<3, CanonicalPolicy.nextResidual r lay low ds<stageBound ⟨lay.val+1,by omega⟩) ∧
    (lay.val=3 → CanonicalPolicy.nextResidual r lay low ds=0) := by
  fin_cases lay
  · exact (hl rfl).elim
  · change CanonicalPolicy.threshold 1 r≤CanonicalPolicy.credit 1 low ds at hd
    change (∀ hnext : 1<3, r-CanonicalPolicy.credit 1 low ds<41) ∧ (1=3 → r-CanonicalPolicy.credit 1 low ds=0)
    have h : r-CanonicalPolicy.threshold 1 r<41 := (CanonicalPolicy.lower_one_progress ⟨r,hr⟩).2
    constructor <;> intro hnext <;> omega
  · change CanonicalPolicy.threshold 2 r≤CanonicalPolicy.credit 2 low ds at hd
    change (∀ hnext : 2<3, r-CanonicalPolicy.credit 2 low ds<22) ∧ (2=3 → r-CanonicalPolicy.credit 2 low ds=0)
    have h : r-CanonicalPolicy.threshold 2 r<22 := (CanonicalPolicy.lower_two_progress ⟨r,hr⟩).2
    constructor <;> intro hnext <;> omega
  · change CanonicalPolicy.threshold 3 r≤CanonicalPolicy.credit 3 low ds at hd
    rw [CanonicalPolicy.lower_three_progress r hr] at hd
    change (∀ hnext : 3<3, _) ∧ (3=3 → r-CanonicalPolicy.credit 3 low ds=0)
    constructor
    · intro hh;omega
    · intro _;exact Nat.sub_eq_zero_of_le hd

structure LowerSetupSteps (im : Image) : Prop where
  setup : ∀ s : MachineState,s.pc=pcOf 22240 → ∀ lay index residual hints : Nat,
    (1≤lay ∧ lay≤3) → index<2^31 → (residual<(if lay=1 then 56 else if lay=2 then 41 else 22)) →
    s.getReg .x8=BitVec.ofNat 64 lay → s.getMem (0x20550#64)=BitVec.ofNat 64 index →
    s.getMem (0x66008#64)=BitVec.ofNat 64 residual → s.getMem (0x66000#64)=BitVec.ofNat 64 hints →
    ∃ t k c,Steps im s k c t ∧ c≤120 ∧ SharedLowerSetup.CallPost lay index residual hints s t

structure LowerReady (lay : Layer) (index residual hints : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (low : Bool) (ds : List Nat) (s t : MachineState) : Prop where
  pc : t.pc=if lay.val<3 then pcOf 22240 else pcOf 22460
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  residualMem : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual residual lay low ds)
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (hints+SharedHints.hintWeight lay.val*CanonicalPolicy.threshold lay.val residual)
  c32 : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  stable : Stable index p forest t
  values : DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay (route index lay).1 (preparedAt p lay) ds).1
  path : DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay (route index lay).1 (preparedAt p lay) ds).2
  floor : CanonicalPolicy.threshold lay.val residual≤CanonicalPolicy.credit lay low ds
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t (LowerWrites lay)

def LowerStagePost (im : Image) (lay : Layer) (index residual hints : Nat) (p : PreparedRoots)
    (forest : Digest×Digest) (s : MachineState) : Option (BitVec 32×List Nat×Bool)→MachineState→Prop
  | none,t => SearchError im t
  | some (_,ds,low),t => LowerReady lay index residual hints p forest low ds s t

theorem lower_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : LowerSetupSteps im) (htail : LowerTailSteps im)
    (lay : Layer) (hl : lay≠0) (index residual hints : Nat) (hi : index<2^31) (hr : residual<stageBound lay)
    (p : PreparedRoots) (forest : Digest×Digest) (s : MachineState) (hp : s.pc=pcOf 22240)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hstable : Stable index p forest s)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual) (hhm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost lay+707)
      (CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val residual)
        (route index lay).2 (route index lay).1 (.pair (messageAt p forest lay).1 (messageAt p forest lay).2) 0 (searchLimit lay))
      (LowerStagePost im lay index residual hints p forest s) := by
  have hln : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt;have : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  obtain ⟨a,ka,ca,sa,hca,ha⟩ := ht.setup s hp lay.val index residual hints hln hi hr h8 hstable.indexMem hrm hhm
  have haf : Frame s a (LowerWrites lay) := ha.frame.mono (fun _ _=>lowerSetupWrites_subset lay)
  have hsta : Stable index p forest a := hstable.frame (haf.mono (fun _ _=>lowerWrites_subset lay hl)) ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold ENC;omega) (by unfold ENC;omega)).trans hcv⟩
  obtain ⟨hp0,hp1⟩ := hstable.message lay hl
  have H := hs.call (lowerArgs lay index (CanonicalPolicy.threshold lay.val residual) (messageAt p forest lay)) a
    (lower_pre lay hl index residual hints hi _ s a ha hsta.tables hac hp0 hp1 (floor_small lay hl residual hr).1)
  have HB := TBSim.bind H (f:=fun r=>pure r) (W₂:=587) (Q₂:=LowerStagePost im lay index residual hints p forest s) (by
    intro r u hu
    cases r with
    | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=LowerStagePost im lay index residual hints p forest s) hu).mono (by omega) (fun _ _ h=>h)
    | some pair =>
      obtain ⟨c,ds,low⟩ := pair
      rcases hu with ⟨up,hc,uc19,uc32,hdec,hlen,hdigs,ur,uf,usum,ucredit,hfloor⟩
      have huf : Frame a u (LowerWrites lay) := uf.mono (fun _ _=>csWrites_lower lay)
      have hstu : Stable index p forest u := hsta.frame (huf.mono (fun _ _=>lowerWrites_subset lay hl)) ur (by decide)
      have hsp := hstu.prepared lay hl
      have uh8 : u.getReg .x8=BitVec.ofNat 64 lay.val := (ur.get (by decide)).trans ha.layer
      have uhrm : u.getMem (0x66008#64)=BitVec.ofNat 64 residual :=
        (uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans
          ((ha.frame.get (by decide) (by unfold ENC;omega)).trans hrm)
      have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
      obtain ⟨t,k,ut,hk,ht⟩ := lower_tail htail lay hl (route index lay).1 residual (preparedAt p lay) low ds
        (lower_decode_digits lay hl hdec) u up uh8 (by simpa only [lowerArgs,hcc,Search.DIGITS,DIGITS] using hdigs)
        (fun j hj d hd=>hsp.saved j hj d (by omega)) hsp.path (by unfold stageBound at hr;split_ifs at hr <;> omega) uhrm ucredit
      have htf : Frame u t (LowerWrites lay) := ht.frame.mono (by intro A hA h;unfold LowerWrites;rcases h with h|rfl;tauto;omega)
      have hstt : Stable index p forest t := hstu.frame (htf.mono (fun _ _=>lowerWrites_subset lay hl)) ht.regs (by decide)
      refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
      refine ⟨ht.pc,ht.layer,ht.residual,?_,?_,hstt,ht.values,ht.path,hfloor,?_,?_⟩
      · exact (ht.frame.get (by decide) (by unfold LowerTailWrites SharedRootControl.sigBase;split_ifs <;> omega)).trans
          ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans ha.hints)
      · exact ⟨c.toNat,by omega,(ht.frame.get (by unfold ENC;omega)
          (by unfold LowerTailWrites SharedRootControl.sigBase ENC;split_ifs <;> omega)).trans uc32⟩
      · rw [ht.regs.get (by decide)]
        simpa [lowerArgs,CanonicalPolicy.normalLayer,hl,T3.target] using usum
      · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
  have HC := TBSim.steps sa HB
  simpa only [bind_pure,topArgs,lowerArgs] using HC.mono (by change ca+(Canonical.csCost lay+587)≤Canonical.csCost lay+707;omega) (fun _ _ h=>h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def PiecesStored (lay : Layer) (pieces : T3.Pieces) (s : MachineState) : Prop :=
  DigsAt s (SharedRootControl.sigBase lay.val) pieces.1 ∧
  DigsAt s (SharedRootControl.sigBase lay.val+688) pieces.2

theorem lowerWrites_other_values (old current : Layer) (ho : old≠0) (hc : current≠0)
    (hne : old≠current) (j half : Nat) (hj : j<43) (hh : half<2) :
    ¬LowerWrites current (SharedRootControl.sigBase old.val+16*j+8*half) := by
  intro h
  rcases h with h|h|h|h|h|h
  all_goals fin_cases old <;> fin_cases current <;>
    simp_all [SharedRootControl.sigBase,ENC,EOUT,DIGITS] <;> omega

theorem PiecesStored.frame_lower {s t : MachineState} {old current : Layer} {pieces : T3.Pieces}
    (ho : old≠0) (hc : current≠0) (hne : old≠current)
    (hlen : pieces.1.length=43) (hpath : pieces.2.length=height old)
    (h : PiecesStored old pieces s) (hf : Frame s t (LowerWrites current)) : PiecesStored old pieces t := by
  constructor
  · intro j hj
    have hj' : j<43 := by simpa only [hlen] using hj
    apply (h.1 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · simpa using lowerWrites_other_values old current ho hc hne j 0 hj' (by decide)
    · simpa using lowerWrites_other_values old current ho hc hne j 1 hj' (by decide)
  · intro j hj
    have hj' : j<height old := by simpa only [hpath] using hj
    have hheight : height old≤12 := by fin_cases old <;> decide
    apply (h.2 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw
      exact work_not_path old ho j 0 hj' (by decide) (by simpa using lowerWrites_subset current hc hw)
    · intro hw
      exact work_not_path old ho j 1 hj' (by decide) (by simpa using lowerWrites_subset current hc hw)

theorem PiecesStored.frame_finish {s t : MachineState} {lay : Layer} {pieces : T3.Pieces}
    (hl : lay≠0) (hlen : pieces.1.length=43) (hpath : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) (hf : Frame s t (fun A=>DIGITS≤A ∧ A<DIGITS+56)) : PiecesStored lay pieces t := by
  have hsbase : SharedRootControl.sigBase lay.val+1024<DIGITS := by
    unfold SharedRootControl.sigBase DIGITS;split_ifs <;> omega
  have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
  constructor
  · intro j hj
    have hj' : j<43 := by simpa only [hlen] using hj
    apply (h.1 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw;omega
    · intro hw;omega
  · intro j hj
    have hj' : j<height lay := by simpa only [hpath] using hj
    apply (h.2 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw;omega
    · intro hw;omega

theorem prepared_length (lay : Layer) (hl : lay≠0) (leaf : Nat) (p : PreparedLower) (ds : List Nat) :
    (preparedPieces lay leaf p ds).1.length=43 ∧ (preparedPieces lay leaf p ds).2.length=height lay := by
  have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
  simp [preparedPieces,hcc]

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000

theorem work_not_base {A : Nat} (hb : BaseA A) : ¬WorkWrites A := by
  intro hw
  rcases hw with hw|hw|hw|hw|hw|hw|⟨lay,hlo,hhi,ha,hb'⟩
  all_goals unfold BaseA NeverW at hb
  all_goals simp only [PRIV,REGION,FLEAF,Keygen.NODE,CHAIN,ZDIG,ENC,EOUT,DIGITS,NBUF,TOP_DATA] at *
  all_goals first | omega | skip
  all_goals unfold SharedRootControl.sigBase at *
  all_goals split_ifs at * <;> omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000

theorem stateBase_frame {sk : SecretKey} {cache : Bytes 131072} {s t : MachineState}
    (h : SharedTopPath.StateBase sk cache s) (hf : Frame s t WorkWrites)
    (hx5 : t.getReg .x5=0) : SharedTopPath.StateBase sk cache t := by
  have g : ∀ A,A<2^64→BaseA A→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (work_not_base hb)
  refine ⟨hx5,?_,?_,?_,?_,?_,?_,fun k hk=>?_,fun A hA hn h32 h40=>?_⟩
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p0
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p8
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p32
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p40
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p48
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p56
  · exact (g _ (by unfold REGION;omega) (by unfold BaseA;right;right;right;right;right;right;left;omega)).trans (h.region k hk)
  · exact (g _ hA (by unfold BaseA;right;right;right;right;right;right;right;left;exact hn)).trans (h.zero A hA hn h32 h40)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure Choices where
  c0 : BitVec 32
  c1 : BitVec 32
  c2 : BitVec 32
  c3 : BitVec 32
  d0 : List Nat
  d1 : List Nat
  d2 : List Nat
  d3 : List Nat
  l0 : Bool
  l1 : Bool
  l2 : Bool
  l3 : Bool

def Choices.r1 (a : Choices) := CanonicalPolicy.nextResidual 74 0 a.l0 a.d0
def Choices.r2 (a : Choices) := CanonicalPolicy.nextResidual a.r1 1 a.l1 a.d1
def Choices.r3 (a : Choices) := CanonicalPolicy.nextResidual a.r2 2 a.l2 a.d2
def Choices.hints (a : Choices) := 484*CanonicalPolicy.threshold 1 a.r1 +
  22*CanonicalPolicy.threshold 2 a.r2 + CanonicalPolicy.threshold 3 a.r3

def prefixSearch (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) : T3.M (Option Choices) := do
  let some (c0,d0,l0) ← CanonicalPolicy.layerCounterSearchAt 0 19 (route index 0).2 (route index 0).1
    (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0) | pure none
  let r1 := CanonicalPolicy.nextResidual 74 0 l0 d0
  let f1 := CanonicalPolicy.threshold 1 r1
  if f1≥16 then return none
  let some (c1,d1,l1) ← CanonicalPolicy.layerCounterSearchAt 1 f1 (route index 1).2 (route index 1).1
    (.pair (topPair 2 p.two.levels).1 (topPair 2 p.two.levels).2) 0 (searchLimit 1) | pure none
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  let f2 := CanonicalPolicy.threshold 2 r2
  if f2≥22 then return none
  let some (c2,d2,l2) ← CanonicalPolicy.layerCounterSearchAt 2 f2 (route index 2).2 (route index 2).1
    (.pair (topPair 3 p.three.levels).1 (topPair 3 p.three.levels).2) 0 (searchLimit 2) | pure none
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  let f3 := CanonicalPolicy.threshold 3 r3
  if f3≥22 then return none
  let some (c3,d3,l3) ← CanonicalPolicy.layerCounterSearchAt 3 f3 (route index 3).2 (route index 3).1
    (.pair forest.1 forest.2) 0 (searchLimit 3) | pure none
  pure (some ⟨c0,c1,c2,c3,d0,d1,d2,d3,l0,l1,l2,l3⟩)

structure PrefixReady (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (a : Choices)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=54
  n4 : t.getReg .x27=51
  target : t.getReg .x17=146
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some a.d0
  digits : ∀ j,j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (a.d0.getD j 0)
  sum : (t.getReg .x25).toNat≤201
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 a.hints
  residual : t.getMem (0x66008#64)=0
  credit : CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3=0
  frame : Frame s t WorkWrites

def PrefixPost (im : Image) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option Choices→MachineState→Prop
  | none,t => SearchError im t
  | some a,t => PrefixReady index p forest a s t

def prefixCost : Nat := Canonical.csCost 0+57+((Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)))

theorem prefix_good {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s prefixCost (prefixSearch index p forest) (PrefixPost im index p forest s) := by
  unfold prefixSearch
  have H0 := top_stage hs htop htail index hi p forest s hp hstable hh hc32
  refine (TBSim.bind H0 (W₂:=(Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30))) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=prefixCost) (by unfold prefixCost;omega) (fun _ _ h=>h)
  intro r0 t0 h0
  cases r0 with
  | none => exact (TBSim.pure (a:=none) (s:=t0) (Q:=PrefixPost im index p forest s) h0).mono (by omega) (fun _ _ h=>h)
  | some a0 =>
    obtain ⟨c0,d0,l0⟩ := a0
    change TopReady index p forest l0 d0 s t0 at h0
    let r1 := CanonicalPolicy.nextResidual 74 0 l0 d0
    let f1 := CanonicalPolicy.threshold 1 r1
    have hf1 : f1<16 := (floor_small 1 (by decide) r1 h0.small).2 rfl
    dsimp only [f1,r1] at hf1
    simp only [if_neg (Nat.not_le.mpr hf1)]
    have H1 := lower_stage hs hlower hltail 1 (by decide) index r1 0 hi h0.small p forest t0
      h0.pc h0.layer h0.stable h0.residual h0.hints h0.c32
    refine (TBSim.bind H1 (W₂:=(Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30))) (by omega) (fun _ _ h=>h)
    intro r1out t1 h1
    cases r1out with
    | none => exact (TBSim.pure (a:=none) (s:=t1) (Q:=PrefixPost im index p forest s) h1).mono (by omega) (fun _ _ h=>h)
    | some a1 =>
      obtain ⟨c1,d1,l1⟩ := a1
      change LowerReady 1 index r1 0 p forest l1 d1 t0 t1 at h1
      let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
      let f2 := CanonicalPolicy.threshold 2 r2
      have hr2 : r2<41 := (next_stage_bound 1 (by decide) r1 h0.small l1 d1 h1.floor).1 (by decide)
      have hf2 : f2<22 := (floor_small 2 (by decide) r2 hr2).1
      have hints1 : t1.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1) := by simpa [SharedHints.hintWeight] using h1.hints
      have saved1 : SavedTop d0 t1 := h0.saved.frame h1.frame (lowerWrites_saved 1)
      dsimp only [f2,r2,r1] at hf2
      simp only [if_neg (Nat.not_le.mpr hf2)]
      have H2 := lower_stage hs hlower hltail 2 (by decide) index r2 (484*f1) hi hr2 p forest t1
        h1.pc h1.layer h1.stable h1.residualMem hints1 h1.c32
      refine (TBSim.bind H2 (W₂:=(Canonical.csCost 3+707)+30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)) (by omega) (fun _ _ h=>h)
      intro r2out t2 h2
      cases r2out with
      | none => exact (TBSim.pure (a:=none) (s:=t2) (Q:=PrefixPost im index p forest s) h2).mono (by omega) (fun _ _ h=>h)
      | some a2 =>
        obtain ⟨c2,d2,l2⟩ := a2
        change LowerReady 2 index r2 (484*f1) p forest l2 d2 t1 t2 at h2
        let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
        let f3 := CanonicalPolicy.threshold 3 r3
        have hr3 : r3<22 := (next_stage_bound 2 (by decide) r2 hr2 l2 d2 h2.floor).1 (by decide)
        have hf3 : f3<22 := (floor_small 3 (by decide) r3 hr3).1
        have hints2 : t2.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1+22*f2) := by simpa [SharedHints.hintWeight] using h2.hints
        have saved2 : SavedTop d0 t2 := saved1.frame h2.frame (lowerWrites_saved 2)
        have one1 : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one d1) t1 := ⟨h1.values,h1.path⟩
        have one2 := one1.frame_lower (current:=2) (by decide) (by decide) (by decide)
          (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 h2.frame
        dsimp only [f3,r3,r2,r1] at hf3
        simp only [if_neg (Nat.not_le.mpr hf3)]
        have H3 := lower_stage hs hlower hltail 3 (by decide) index r3 (484*f1+22*f2) hi hr3 p forest t2
          h2.pc h2.layer h2.stable h2.residualMem hints2 h2.c32
        refine (TBSim.bind H3 (W₂:=30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 3+707)+30) (by omega) (fun _ _ h=>h)
        intro r3out t3 h3
        cases r3out with
        | none => exact (TBSim.pure (a:=none) (s:=t3) (Q:=PrefixPost im index p forest s) h3).mono (by omega) (fun _ _ h=>h)
        | some a3 =>
          obtain ⟨c3,d3,l3⟩ := a3
          change LowerReady 3 index r3 (484*f1+22*f2) p forest l3 d3 t2 t3 at h3
          have hz : CanonicalPolicy.nextResidual r3 3 l3 d3=0 :=
            (next_stage_bound 3 (by decide) r3 hr3 l3 d3 h3.floor).2 rfl
          have saved3 : SavedTop d0 t3 := saved2.frame h3.frame (lowerWrites_saved 3)
          have one3 := one2.frame_lower (current:=3) (by decide) (by decide) (by decide)
            (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 h3.frame
          have two2 : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two d2) t2 := ⟨h2.values,h2.path⟩
          have two3 := two2.frame_lower (current:=3) (by decide) (by decide) (by decide)
            (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 h3.frame
          have three3 : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three d3) t3 := ⟨h3.values,h3.path⟩
          obtain ⟨t,st,ht⟩ := finish_steps hfinish index hi p forest d0 t3 h3.pc h3.stable saved3 h3.sum
          refine (TBSim.steps st (TBSim.pure (s:=t) (a:=some ⟨c0,c1,c2,c3,d0,d1,d2,d3,l0,l1,l2,l3⟩) (Q:=PrefixPost im index p forest s) ?_)).mono (W':=30) (by omega) (fun _ _ h=>h)
          refine ⟨ht.pc,ht.layer,ht.tree,ht.height,ht.chains,ht.n4,ht.target,ht.leaf,ht.selected,ht.stable,
            h0.decoded,ht.digits,ht.sum,?_,?_,?_,?_,?_,hz,?_⟩
          · exact one3.frame_finish (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 ht.frame
          · exact two3.frame_finish (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 ht.frame
          · exact three3.frame_finish (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 ht.frame
          · have hm := (ht.frame.get (A:=0x66000) (by decide) (by unfold DIGITS;omega)).trans h3.hints
            change t.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1+22*f2+f3)
            simpa [SharedHints.hintWeight] using hm
          · have hm := (ht.frame.get (A:=0x66008) (by decide) (by unfold DIGITS;omega)).trans h3.residualMem
            change t.getMem (0x66008#64)=BitVec.ofNat 64 0
            simpa only [hz] using hm
          · have F1 := h1.frame.mono (fun _ _=>lowerWrites_subset 1 (by decide))
            have F2 := h2.frame.mono (fun _ _=>lowerWrites_subset 2 (by decide))
            have F3 := h3.frame.mono (fun _ _=>lowerWrites_subset 3 (by decide))
            have F4 : Frame t3 t WorkWrites := ht.frame.mono (by intro A hA h;unfold WorkWrites;omega)
            exact ((((h0.frame.trans F1).trans F2).trans F3).trans F4).mono (by
              intro A hA h;rcases h with (((h|h)|h)|h)|h <;> exact h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open OracleComp
set_option maxHeartbeats 500000
set_option maxRecDepth 32768

def finishSource (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots)
    (a : Choices) : M (Option CanonicalLayers) := do
  let top ← signTop cache (route index 0).1 a.d0
  pure (some ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3,
    BitVec.ofNat 16 a.hints⟩)

theorem searchPreparedLayers_prefix (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) :
    searchPreparedLayers cache index p forest =
      prefixSearch index p forest >>= fun
        | none => pure none
        | some a => finishSource cache index p a := by
  unfold searchPreparedLayers prefixSearch
  simp only [CanonicalPolicy.totalCredit,CanonicalPolicy.threshold_top]
  simp only [bind_assoc]
  congr 1
  funext o0
  cases o0 with
  | none => simp only [pure_bind]
  | some o0 =>
    obtain ⟨c0,d0,l0⟩ := o0
    dsimp only
    split
    · simp_all only [pure_bind, ite_true, ite_false]
    · simp_all only [bind_assoc, ite_true, ite_false]
      congr 1
      funext o1
      cases o1 with
      | none => simp only [pure_bind]
      | some o1 =>
        obtain ⟨c1,d1,l1⟩ := o1
        dsimp only
        split
        · simp_all only [pure_bind, ite_true, ite_false]
        · simp_all only [bind_assoc, ite_true, ite_false]
          congr 1
          funext o2
          cases o2 with
          | none => simp only [pure_bind]
          | some o2 =>
            obtain ⟨c2,d2,l2⟩ := o2
            dsimp only
            split
            · simp_all only [pure_bind, ite_true, ite_false]
            · simp_all only [bind_assoc, ite_true, ite_false]
              congr 1
              funext o3
              cases o3 with
              | none => simp only [pure_bind]
              | some o3 =>
                obtain ⟨c3,d3,l3⟩ := o3
                simp only [pure_bind,finishSource,Choices.r1,Choices.r2,Choices.r3,Choices.hints]

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open Packed.Boundary
open Packed (L0W)
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def TopFinishPost (s : MachineState) (top : T3.Pieces) (t : MachineState) : Prop :=
  t.pc=pcOf 540 ∧ (∀ i<54,DigAt t (SIG+2192+16*i) (top.1.getD i 0)) ∧
    (∀ j<12,DigAt t (SIG+3056+16*j) (top.2.getD j 0)) ∧ Frame s t L0W ∧
    t.getMem (0x66000#64)=s.getMem (0x66000#64) ∧
    t.getMem (0x66008#64)=s.getMem (0x66008#64)

structure TopCalls (im : Image) (sk : SecretKey) (cache : Bytes 131072) : Prop where
  call : ∀ (leaf : Nat),leaf<4096 → ∀ (ds : List Nat) (u : MachineState),u.pc=pcOf 441 →
    SharedTopPath.StateBase sk cache u → TopRegs leaf u →
    u.getReg .x18=BitVec.ofNat 64 leaf → (u.getReg .x25).toNat≤201 →
    (∀ i<54,ds.getD i 0≤T3.maxDigit 0 i) →
    (∀ i<54,u.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 (ds.getD i 0)) →
    TBSim im sk u 335006 (T3.signTop (cacheDec cache) leaf ds) (TopFinishPost u)

theorem PiecesStored.frame_top {s t : MachineState} {lay : Layer} {pieces : T3.Pieces}
    (hl : lay≠0) (hlen : pieces.1.length=43) (hpath : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) (hf : Frame s t L0W) : PiecesStored lay pieces t := by
  constructor
  · intro i hi
    have hi' : i<43 := by simpa only [hlen] using hi
    apply (h.1 i hi).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG] <;> omega
  · intro j hj
    have hj' : j<height lay := by simpa only [hpath] using hj
    apply (h.2 j hj).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG,height] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG,height] <;> omega

def layersValue (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces) : CanonicalLayers :=
  ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3,
    BitVec.ofNat 16 a.hints⟩

structure Completed (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces)
    (t : MachineState) : Prop where
  pc : t.pc=pcOf 540
  topValues : ∀ i<54,DigAt t (SIG+2192+16*i) (top.1.getD i 0)
  topPath : ∀ j<12,DigAt t (SIG+3056+16*j) (top.2.getD j 0)
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 a.hints
  residual : t.getMem (0x66008#64)=0
  credit : CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3=0

def LayersPost (im : Image) (index : Nat) (p : PreparedRoots) : Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => ∃ a top,layers=layersValue index p a top ∧ Completed index p a top t

theorem searchPreparedLayers_good {im : Image} {sk : SecretKey} {cache : Bytes 131072}
    (hc : TopCalls im sk cache) (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (LayersPost im index p) := by
  rw [searchPreparedLayers_prefix]
  refine TBSim.bind (prefix_good hs htop htail hlower hltail hfinish index hi p forest s hp hstable hh hc32)
    (W₂:=335006) (Q₂:=LayersPost im index p) ?_
  intro a u hu
  cases a with
  | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=LayersPost im index p) hu).mono (by omega) (fun _ _ h=>h)
  | some a =>
    change PrefixReady index p forest a s u at hu
    have hb := stateBase_frame hbase hu.frame hu.stable.tables.x5
    have hleaf : index/2^19<4096 := by omega
    have hregs : TopRegs (index/2^19) u :=
      ⟨hu.layer,hu.tree,hu.selected.trans hu.leaf,hu.chains,hu.n4⟩
    have hd7 : ∀ i<54,a.d0.getD i 0≤T3.maxDigit 0 i := by
      obtain ⟨v,hv⟩ := hu.decoded
      change T3.decode 0 v=some a.d0 at hv
      intro i hi
      exact T3.decode_digit_max hv i hi
    have H := hc.call (index/2^19) hleaf a.d0 u hu.pc hb hregs hu.leaf hu.sum hd7 hu.digits
    unfold finishSource
    have hr : (route index 0).1=index/2^19 := by
      change index/2^19%2^12=index/2^19
      exact Nat.mod_eq_of_lt hleaf
    rw [hr]
    refine (TBSim.bind H (W₂:=0) (Q₂:=LayersPost im index p) ?_).mono (by omega) (fun _ _ h=>h)
    intro top t ht
    rcases ht with ⟨htpc,htv,htp,htf,hth,htr⟩
    refine TBSim.pure (a:=some (layersValue index p a top)) (s:=t) (Q:=LayersPost im index p) ?_
    refine ⟨a,top,rfl,htpc,htv,htp,?_,?_,?_,hth.trans hu.hints,htr.trans hu.residual,hu.credit⟩
    · exact hu.one.frame_top (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 htf
    · exact hu.two.frame_top (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 htf
    · exact hu.three.frame_top (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 htf

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem installed_searchCalls (sk : BitVec 256) : SearchCalls Images.signImage sk :=
  ⟨fun _ _ hp => Canonical.counterSearch_good SharedSearchCode.installed_searchKernel hp⟩

theorem installed_topSetup : TopSetupSteps Images.signImage :=
  ⟨SharedTopSetup.steps SharedTopSetup.installed_code⟩

theorem installed_topTail : TopTailSteps Images.signImage :=
  ⟨SharedTopDigits.save_steps SharedTopDigits.installed_save,
   SharedControlTail.initResidual_steps SharedControlTail.installed_initResidual,
   SharedResidual.residual22230_steps SharedResidual.installed22230,
   SharedControlTail.firstLayer_steps SharedControlTail.installed_firstLayer⟩

theorem installed_lowerSetup : LowerSetupSteps Images.signImage :=
  ⟨SharedLowerSetup.call_steps SharedFloor.installed_dispatch SharedHints.installed_code SharedLowerRegisters.installed_code⟩

theorem installed_lowerTail : LowerTailSteps Images.signImage :=
  ⟨SharedReveal.prepared_steps SharedReveal.installed_stepCode SharedReveal.installed_byteCode SharedReveal.installed_setupCode,
   SharedResidual.residual22448_steps SharedResidual.installed22448,
   SharedControlTail.nextLayer_steps SharedControlTail.installed_nextLayer⟩

theorem installed_finish : FinishSteps Images.signImage :=
  ⟨SharedTopDigits.restore_steps SharedTopDigits.installed_restore,
   SharedControlTail.topProduce_steps SharedControlTail.installed_topProduce⟩

theorem installed_prefix_good {sk : BitVec 256}
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s prefixCost (prefixSearch index p forest) (PrefixPost Images.signImage index p forest s) :=
  prefix_good (installed_searchCalls sk) installed_topSetup installed_topTail installed_lowerSetup
    installed_lowerTail installed_finish index hi p forest s hp hstable hh hc32

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem installed_topCalls (sk : SecretKey) (cache : Bytes 131072) :
    TopCalls Images.signImage sk cache := by
  constructor
  intro leaf hl ds u up hb hr h18 h25 hd ud
  have H := SharedTopContinuation.top_only SharedTopBlocks.installed_code
    ClaudeWCT.W9.Machine.Sign.SharedTopLeafP.installed_continuation_leaf leaf hl ds u up hb hr h18 h25 hd ud
  exact H.mono (le_refl _) (by
    intro top t ht
    rcases ht with ⟨tp,tv,ta,tf,tm⟩
    exact ⟨tp,tv,ta,tf,tm _ (Or.inl rfl),tm _ (Or.inr rfl)⟩)

theorem installed_searchPreparedLayers_good {sk : SecretKey} {cache : Bytes 131072}
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (LayersPost Images.signImage index p) :=
  searchPreparedLayers_good (installed_topCalls sk cache) (installed_searchCalls sk)
    installed_topSetup installed_topTail installed_lowerSetup installed_lowerTail installed_finish
    index hi p forest s hp hstable hbase hh hc32

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem base_stateBase {sk : SecretKey} {cache : Bytes 131072} {s : MachineState} {flag : Nat}
    (h : Base (cfFlag:=flag) sk cache s) : SharedTopPath.StateBase sk cache s :=
  ⟨h.x5,h.p0,h.p8,h.p32,h.p40,h.p48,h.p56,h.region,fun A hA hn _ _ => h.zero A hA hn⟩

theorem base_tables {sk : SecretKey} {cache : Bytes 131072} {s : MachineState}
    (h : Base (cfFlag:=0) sk cache s) : Tables s :=
  ⟨h.x5,h.zero _ (by decide) (by unfold NeverW;tauto),h.table,h.cf,h.reward,h.zt⟩

theorem built_stable {sk : SecretKey} {cache : Bytes 131072} {index : Nat} {forest : Digest×Digest}
    {s t : MachineState} {p : PreparedRoots}
    (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t) : Stable index p forest t :=
  ⟨base_tables h.base,h.indexMem,h.one,h.two,h.three,h.forestL,h.forestR⟩

theorem from_built_good {sk : SecretKey} {cache : Bytes 131072}
    {index : Nat} (hi : index<2^31) {p : PreparedRoots} {forest : Digest×Digest}
    {s t : MachineState} (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk t (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (LayersPost Images.signImage index p) := by
  apply installed_searchPreparedLayers_good index hi p forest t h.pc (built_stable h)
    (base_stateBase h.base) h.hintZero
  obtain ⟨c,hc,hv⟩ := hc32
  exact ⟨c,hc,h.counterMem.trans hv⟩

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def innerCode (c : Nat) : List (BitVec 32) := ((coordCodesW.getD c []).drop 1).take (lI c-cbase c-1)
theorem inner_bounds (c : Fin 9) : cbase c.val+1≤lI c.val ∧ lI c.val-cbase c.val≤(coordCodesW.getD c.val []).length ∧ cbase c.val<2^20 := by
  fin_cases c <;> decide +kernel

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

theorem fetch_of_code {im : Image}
    (hh : CodeAt im (pcOf 11003) headCode)
    (hi : ∀c : Fin 9,CodeAt im (pcOf (cbase c.val+1)) (innerCode c.val))
    (ha : CodeAt im (pcOf 1700) arenaCode) (hs : CodeAt im (pcOf 21200) ftsStub) : Fetch im := by
  constructor
  · intro n w hw
    unfold headLook at hw
    split at hw
    · rename_i hle
      have he:=codeAt_get_word (by decide : 11003<2^30) hh hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
  · intro c hc n w hw
    have hb:=inner_bounds ⟨c,hc⟩
    dsimp only at hb
    unfold coordLook at hw
    split at hw
    · rename_i hn
      unfold coordLookW at hw
      have hw' : (innerCode c)[n-(cbase c+1)]?=some w := by
        unfold innerCode
        rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop]
        rwa [show 1+(n-(cbase c+1))=n-cbase c by omega]
      have hf:=codeAt_get_word (by omega : cbase c+1<2^30) (hi ⟨c,hc⟩) hw'
      simpa [show cbase c+1+(n-(cbase c+1))=n by omega] using hf
    · split at hw
      · rename_i hn2
        have he := codeAt_get_word (by decide : 21200 < 2^30) hs hw
        simpa [show 21200 + (n - 21200) = n by omega] using he
      · unfold arenaLook at hw
        split at hw
        · rename_i hle
          have he := codeAt_get_word (by decide : 1700 < 2^30) ha hw
          simpa [Nat.add_sub_cancel' hle] using he
        · cases hw
#print axioms fetch_of_code
end ClaudeWCT.W9.Machine.Sign.SharedReuse


namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_fetch : Fetch Images.signImage := by
  apply fetch_of_code
  · apply codeAt_sign_current_slice <;> decide +kernel
  · intro c
    fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
#print axioms installed_fetch
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_c4Stub : CodeAt Images.signImage (pcOf c4StubPc) c4Stub := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hstub
      have he := SharedReuse.codeAt_get_word (by decide : c4StubPc < 2^30) installed_c4Stub hw
      simpa [Nat.add_sub_cancel' hstub.2] using he
    · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_c4Stub : CodeAt Images.signImage (pcOf c4StubPc) c4Stub := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hstub
      have he := SharedReuse.codeAt_get_word (by decide : c4StubPc < 2^30) installed_c4Stub hw
      simpa [Nat.add_sub_cancel' hstub.2] using he
    · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
/-- C1: the stub words in the former nop gaps of `signCode_85`. -/
theorem installed_stub (c : Fin 9) : CodeAt Images.signImage (pcOf (stubPc c.val)) (stubWords c.val) := by
  fin_cases c <;> apply codeAt_sign_last <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hle
      have hb : stubPc c<2^30 := by
        have h : ∀ c : Fin 9,stubPc c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he := SharedReuse.codeAt_get_word hb (installed_stub ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
#print axioms installed_code
#print axioms installed_stub
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
/-- C1: the stub words in the former nop gaps of `signCode_85`. -/
theorem installed_stub (c : Fin 9) : CodeAt Images.signImage (pcOf (stubPc c.val)) (stubWords c.val) := by
  fin_cases c <;> apply codeAt_sign_last <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hle
      have hb : stubPc c<2^30 := by
        have h : ∀ c : Fin 9,stubPc c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he := SharedReuse.codeAt_get_word hb (installed_stub ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
#print axioms installed_code
#print axioms installed_stub
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_hookCode (c : Fin 9) : CodeAt Images.signImage (pcOf (lI c.val)) [hookWords.getD c.val 0] := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_hookLook (c : Nat) (hc : c<9) : LookOK Images.signImage (hookLook c) := by
  intro n w hw
  unfold hookLook at hw
  split at hw
  · rename_i he
    have hh : hookWords.getD c 0=w := Option.some.inj hw
    have hb : lI c<2^30 := by
      have h : ∀ c : Fin 9,lI c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have hx := SharedReuse.codeAt_get_word (i:=0) hb (installed_hookCode ⟨c,hc⟩) (by simpa [hh])
    simpa [he] using hx
  · cases hw
#print axioms installed_hookCode
#print axioms installed_hookLook
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (basePc c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : basePc c<2^30 := by
      have h : ∀ c : Fin 9,basePc c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_hookCode (c : Fin 9) : CodeAt Images.signImage (pcOf (cbase c.val)) [hookWord c.val] := by
  fin_cases c <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i he
    have hh : hookWord c=w := Option.some.inj hw
    have hb : cbase c<2^30 := by
      have h : ∀ c : Fin 9,cbase c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have hx:=SharedReuse.codeAt_get_word (i:=0) (w:=w) hb (installed_hookCode ⟨c,hc⟩) (by simpa [hh])
    simpa [he] using hx
  · split at hw
    · rename_i hle
      have hb : entry c<2^30 := by
        have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he:=SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
#print axioms installed_code
#print axioms installed_hookCode
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open SigGolfCandidate.T3M
theorem installed_Code (c : Nat) (hc : c<9) : Code Images.signImage c :=
  ⟨SharedField.installed_look c hc, SharedLeaf.installed_look c hc,
   SharedLeaf.installed_hookLook c hc, SharedNext.installed_look c hc,
   SharedNode.installed_look c hc, SharedTail.installed_look c hc,
   SharedFinish.installed_look c hc, SharedPath.installed_look c hc,
   SharedEnd.installed_look c hc⟩
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_forTail : CodeAt Images.signImage (pcOf 20715) (tailCode.take 28) := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_forTramp : CodeAt Images.signImage (pcOf 21450) signTramp := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_forLook : LookOK Images.signImage forLook := by
  intro n w hw
  unfold forLook at hw
  split at hw
  · rename_i hn
    have he:(tailCode.take 28)[n-20715]?=some w := by
      rw [List.getElem?_take,if_pos (by omega)];exact hw
    have hh:=SharedReuse.codeAt_get_word (by decide:20715<2^30) installed_forTail he
    simpa only[Nat.add_sub_cancel' hn.1]using hh
  · unfold trampLook at hw
    split at hw
    · rename_i hn
      have hh:=SharedReuse.codeAt_get_word (by decide:21450<2^30) installed_forTramp hw
      simpa only[Nat.add_sub_cancel' hn]using hh
    · cases hw
#print axioms installed_forLook
end ClaudeWCT.W9.Machine.Sign.SharedBoundary

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_sign_code : CodeAt Images.signImage (pcOf (base false)) (words false) := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_sign_look : LookOK Images.signImage (look false) := look_of_code false installed_sign_code
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_sign_success : CodeAt Images.signImage (pcOf 22754) signCode := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
theorem installed_sign_failure_jump : CodeAt Images.signImage (pcOf 22764) [0xcccea06f] := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
theorem installed_sign_failure : CodeAt Images.signImage (failPC false) failureCode := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
theorem installed_sign_failure_ecall : CodeAt Images.signImage (pcOf 545) [0x73] := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open Packed.Boundary
open Packed (L0W)
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def FramedLayersPost (im : Image) (index : Nat) (p : PreparedRoots) (s : MachineState) :
    Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => LayersPost im index p (some layers) t ∧ Frame s t (fun A=>WorkWrites A ∨ L0W A)

theorem searchPreparedLayers_framed {im : Image} {sk : SecretKey} {cache : Bytes 131072}
    (hc : TopCalls im sk cache) (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (FramedLayersPost im index p s) := by
  rw [searchPreparedLayers_prefix]
  refine TBSim.bind (prefix_good hs htop htail hlower hltail hfinish index hi p forest s hp hstable hh hc32)
    (W₂:=335006) (Q₂:=FramedLayersPost im index p s) ?_
  intro a u hu
  cases a with
  | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=FramedLayersPost im index p s) hu).mono (by omega) (fun _ _ h=>h)
  | some a =>
    change PrefixReady index p forest a s u at hu
    have hb := stateBase_frame hbase hu.frame hu.stable.tables.x5
    have hleaf : index/2^19<4096 := by omega
    have hregs : TopRegs (index/2^19) u :=
      ⟨hu.layer,hu.tree,hu.selected.trans hu.leaf,hu.chains,hu.n4⟩
    have hd7 : ∀ i<54,a.d0.getD i 0≤T3.maxDigit 0 i := by
      obtain ⟨v,hv⟩ := hu.decoded
      change T3.decode 0 v=some a.d0 at hv
      intro i hi
      exact T3.decode_digit_max hv i hi
    have H := hc.call (index/2^19) hleaf a.d0 u hu.pc hb hregs hu.leaf hu.sum hd7 hu.digits
    unfold finishSource
    have hr : (route index 0).1=index/2^19 := by
      change index/2^19%2^12=index/2^19
      exact Nat.mod_eq_of_lt hleaf
    rw [hr]
    refine (TBSim.bind H (W₂:=0) (Q₂:=FramedLayersPost im index p s) ?_).mono (by omega) (fun _ _ h=>h)
    intro top t ht
    rcases ht with ⟨htpc,htv,htp,htf,hth,htr⟩
    refine TBSim.pure (a:=some (layersValue index p a top)) (s:=t) (Q:=FramedLayersPost im index p s) ?_
    refine ⟨⟨a,top,rfl,htpc,htv,htp,?_,?_,?_,hth.trans hu.hints,htr.trans hu.residual,hu.credit⟩,hu.frame.trans htf⟩
    · exact hu.one.frame_top (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 htf
    · exact hu.two.frame_top (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 htf
    · exact hu.three.frame_top (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 htf

#print axioms searchPreparedLayers_framed
end SigGolfCandidate.T3M.Sign.SharedSearches
namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def LowFrame (s t : MachineState) : Prop := Frame s t (fun A => ¬(SIG≤A ∧ A<SIG+2192))

theorem LowFrame.trans {s t u : MachineState} (h : LowFrame s t) (h' : LowFrame t u) : LowFrame s u :=
  (Frame.trans h h').mono (by intro A hA h;exact h.elim id id)

theorem OnePost.lowFrame {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower}
    (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) : LowFrame s t := by
  apply h.frame.mono
  intro A hA hw hsig
  unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr at hw
  fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT,SIG] <;> omega

theorem prepareRoots_framed {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=1) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (3*(btCost+47)) (prepareRoots index) (fun p t => RootsPost (cfFlag := cfFlag) sk cache index s p t ∧ LowFrame s t) := by
  have r1 := one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    (lay := 1) (by decide) hi s hpc h8 hidx hb hz
  unfold prepareRoots
  refine TBSim.mono (TBSim.bind r1 (fun p1 t1 h1 =>
    TBSim.bind (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
      (lay := 2) (by decide) hi t1 (by simpa using h1.pc) h1.layer h1.indexMem h1.base h1.zero)
      (fun p2 t2 h2 => TBSim.bind
        (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
          (lay := 3) (by decide) hi t2 (by simpa using h2.pc) h2.layer h2.indexMem h2.base h2.zero)
        (fun p3 t3 h3 => TBSim.pure ?_)))) (by omega) (fun _ _ h => h)
  refine ⟨?_, ((h1.lowFrame (by decide)).trans (h2.lowFrame (by decide))).trans (h3.lowFrame (by decide))⟩
  refine ⟨by simpa using h3.pc,by simpa using h3.layer,h3.base,h3.indexMem,?_,?_,h3.stored,?_,?_⟩
  · exact (h1.stored.after (by decide) (by decide) (by decide) h2).after
      (by decide) (by decide) (by decide) h3
  · exact h2.stored.after (by decide) (by decide) (by decide) h3
  · exact (((h1.rootsFrame (by decide)).trans (h2.rootsFrame (by decide))).trans
      (h3.rootsFrame (by decide))).mono (by intro A hA h; rcases h with (h|h)|h <;> exact h)
  · exact (h3.counterMem (by decide)).trans ((h2.counterMem (by decide)).trans (h1.counterMem (by decide)))

theorem entry_roots_framed {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat} (hi : index<2^31)
    (forest : Digest×Digest) (s : MachineState) (hpc : s.pc=pcOf 22100)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hl : DigAt s ENC forest.1) (hr : DigAt s (ENC+48) forest.2) :
    TBSim im sk s (28+3*(btCost+47)) (prepareRoots index) (fun p t => BuiltPost (cfFlag := cfFlag) sk cache index forest s p t ∧ LowFrame s t) := by
  obtain ⟨a,sa,ap,a8,al,ar,az,ad,ars,af⟩ := entry_steps he s hpc forest.1 forest.2 hl hr
  have af' : Frame s a EntryWrites := af.mono (by unfold EntryWrites; intros A hA h; exact h)
  have abase : Base (cfFlag := cfFlag) sk cache a := hb.frame af' ars (by decide) (by
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold EntryWrites at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA,DIGITS] at hbase hw
    omega)
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (af'.get (A := 0x20550) (by decide) (by unfold EntryWrites DIGITS; omega)).trans hidx
  refine (TBSim.steps sa (prepareRoots_framed hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    hi a ap a8 aidx abase ad)).mono (le_refl _) ?_
  intro p t hpair
  rcases hpair with ⟨ht,hlo⟩
  refine ⟨?_, ?_⟩
  · refine ⟨ht.pc,ht.layer,ht.base,ht.indexMem,ht.one,ht.two,ht.three,?_,?_,?_,af'.trans ht.frame,?_⟩
    · exact (ht.frame.get (A := 0x66000) (by decide) (by unfold RootsWrites; decide)).trans az
    · exact al.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
    · exact ar.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
    · exact ht.counterMem.trans (af'.get (A := ENC+32) (by unfold ENC; decide) (by unfold EntryWrites ENC DIGITS; decide))
  · exact (show LowFrame s a from af'.mono (by unfold EntryWrites SIG DIGITS; intros A hA hw hsig; omega)).trans hlo

#print axioms entry_roots_framed
end SigGolfCandidate.T3M.Sign.SharedRootControl
namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
theorem installed_searchPreparedLayers_framed {sk : SecretKey} {cache : Bytes 131072}
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (FramedLayersPost Images.signImage index p s) :=
  searchPreparedLayers_framed (installed_topCalls sk cache) (installed_searchCalls sk)
    installed_topSetup installed_topTail installed_lowerSetup installed_lowerTail installed_finish
    index hi p forest s hp hstable hbase hh hc32


theorem from_built_framed {sk : SecretKey} {cache : Bytes 131072}
    {index : Nat} (hi : index<2^31) {p : PreparedRoots} {forest : Digest×Digest}
    {s t : MachineState} (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk t (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (FramedLayersPost Images.signImage index p t) := by
  apply installed_searchPreparedLayers_framed index hi p forest t h.pc (built_stable h)
    (base_stateBase h.base) h.hintZero
  obtain ⟨c,hc,hv⟩ := hc32
  exact ⟨c,hc,h.counterMem.trans hv⟩

end SigGolfCandidate.T3M.Sign.SharedSearches
namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open Packed.Boundary
open Packed (L0W)

theorem layers_lowFrame {s t : MachineState} (h : Frame s t (fun A=>WorkWrites A ∨ L0W A)) :
    Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)) := by
  apply h.mono
  intro A hA hw hlo
  rcases hw with hw|hw
  · rcases hw with hw|hw|hw|hw|hw|hw|⟨lay,hl,hu,ha,hb⟩
    all_goals first | (simp only [ENC,EOUT,DIGITS,SIG] at *;omega) | skip
    unfold SharedRootControl.sigBase at ha hb
    simp only [SIG] at hlo
    split_ifs at ha hb <;>omega
  · exact hw.1 hlo

#print axioms layers_lowFrame
end SigGolfCandidate.T3M.Sign.SharedSearches
