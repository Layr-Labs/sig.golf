import SigGolfCandidate.OuterSigning
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace OuterSignSearchSource
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate SigGolfCandidate.T3M SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Sign.Packed
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
def topArgs (index : Nat) (pair : Digest×Digest) : Canonical.CsArgs :=
  ⟨0,(route index 0).2,(route index 0).1,.pair pair.1 pair.2,22208,ClaudeWCT.WCT9.Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)⟩

#check topArgs

theorem top_pre (index : Nat) (hi : index<2^31) (pair : Digest×Digest)
    (s t : MachineState) (h : SharedTopSetup.Post index pair.1 pair.2 s t)
    (ht : Tables t) (hc : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c) :
    Canonical.CsPre 543 (topArgs index pair) t := by
  have hr : (route index 0).2=0 := T3.route_top_tree index hi
  have hl : (route index 0).1=index/2^19 := by
    change index/2^19%2^12=index/2^19
    exact Nat.mod_eq_of_lt (by omega)
  have hf : ClaudeWCT.WCT9.Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index) < 24 := by
    rw [ClaudeWCT.WCT9.Policy75Safe23.threshold_top]
    have hb := OuterSigning.requiredCredit_bounds index
    omega
  refine ⟨h.pc,h.ret,ht.x5,h.x8,?_,?_,h.x17,h.x26,h.x27,?_,?_,?_,Or.inl hr,
    h.left.1,h.left.2,hc,ht.z40,h.right.1,h.right.2,ht.table,ht.cf,ht.reward,ht.zt,
    hf,(by intro;dsimp only [topArgs];rw [Policy75Safe23.threshold_top,LocalRouteMachineHelpers.rootFloor_eq];have hb:=OuterSigning.requiredCredit_bounds index;omega),?_,fun _ => ht.t51⟩
  · simpa [topArgs,hr] using h.x9
  · simpa only [topArgs,hl] using h.x18
  · change (route index 0).2<2^32;rw [hr];decide
  · change (route index 0).1<2^32;rw [hl];omega
  · change (route index 0).2*2^12+(route index 0).1<2^12;rw [hr,hl];omega
  · intro hn;exact (hn rfl).elim

#check top_pre

structure TopTailSteps (im : Image) : Prop where
  save : ∀ s : MachineState, s.pc=pcOf 22208 →
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22226 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.DIGITS+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => 0x66100≤A ∧ A<0x66100+56)
  init : ∀ s : MachineState, s.pc=pcOf 22226 → ∀ leaf : Nat, leaf<4096 →
    s.getReg .x18=BitVec.ofNat 64 leaf →
    ∃ t,Steps im s 12 12 t ∧ t.pc=pcOf 22230 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (OuterSigning.rootPool leaf) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008)
  residual : ∀ s : MachineState, s.pc=pcOf 22230 → ∀ index r c : Nat, index<2^64 → r<2^32 → c<2^32 →
    s.getMem (0x20550#64)=BitVec.ofNat 64 index →
    s.getMem (0x66008#64)=BitVec.ofNat 64 r → s.getMem (0x66018#64)=BitVec.ofNat 64 c →
    ∃ t k,Steps im s k k t ∧ k≤21 ∧ t.pc=pcOf 22239 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c-LocalRoute.ownSave index 1) ∧
      RegsExcept s t [.x3,.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008)
  first : ∀ s : MachineState, s.pc=pcOf 22239 →
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22240 ∧ t.getReg .x8=1 ∧
      RegsExcept s t [.x8] ∧ Frame s t (fun _ => False)

#check TopTailSteps

structure TopTailPost (index : Nat) (low : Bool) (ds : List Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (routeResidual index (OuterSigning.requiredCredit index) 0 low ds)
  saved : ∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.DIGITS+8*i))
  regs : RegsExcept s t [.x3,.x6,.x7,.x8,.x28,.x29]
  frame : Frame s t TopTailWrites

#check TopTailPost

theorem top_tail {im : Image} (hc : TopTailSteps im)
    (index : Nat) (hi : index<2^64) (s : MachineState) (hp : s.pc=pcOf 22208)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (h18 : s.getReg .x18=BitVec.ofNat 64 (route index 0).1) (low : Bool) (ds : List Nat)
    (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds)) :
    ∃ t k,Steps im s k k t ∧ k≤52 ∧ TopTailPost index low ds s t := by
  obtain ⟨a,sa,ap,asaved,ar,af⟩ := hc.save s hp
  have hleaf : (route index 0).1 < 4096 := by
    change index/2^19%4096<4096
    exact Nat.mod_lt _ (by decide)
  obtain ⟨b,ab,bp,brm,br,bf⟩ := hc.init a ap (route index 0).1 hleaf ((ar.get (by decide)).trans h18)
  change b.getMem (0x66008#64)=BitVec.ofNat 64 (OuterSigning.requiredCredit index) at brm
  have hpool := OuterSigning.requiredCredit_bounds index
  have bcm : b.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds) :=
    (bf.get (by decide) (by decide)).trans ((af.get (by decide) (by omega)).trans hcm)
  obtain ⟨c,k,bc,hk,cp,crm,cr,cf⟩ := hc.residual b bp index (OuterSigning.requiredCredit index) (CanonicalPolicy.credit 0 low ds) hi (by omega) (credit_small _ _ _)
    ((bf.get (by decide) (by simp)).trans ((af.get (by decide) (by omega)).trans hidx)) brm bcm
  obtain ⟨t,ct,tp,t8,tr,tf⟩ := hc.first c cp
  refine ⟨t,18+12+k+1,((sa.trans ab).trans bc).trans ct,by omega,?_,t8,?_,?_,?_,?_⟩
  · exact tp
  · exact (tf.get (by decide) (by simp)).trans crm
  · intro i hi
    exact (tf.get (by omega) (by simp)).trans ((cf.get (by omega) (by omega)).trans
      ((bf.get (by omega) (by omega)).trans (asaved i hi)))
  · exact (((ar.trans br).trans cr).trans tr).mono (by simp)
  · exact (((af.trans bf).trans cf).trans tf).mono (by
      intro A hA h;rcases h with ((h|h)|h)|h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
      · exact h.elim)

#check top_tail

theorem top_residual_small (index : Nat) {low : Bool} {ds : List Nat}
    (h : ClaudeWCT.WCT9.Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index) ≤ CanonicalPolicy.credit 0 low ds) :
    routeResidual index (OuterSigning.requiredCredit index) 0 low ds<58 := by
  rw [ClaudeWCT.WCT9.Policy75Safe23.threshold_top] at h
  unfold routeResidual CanonicalPolicy.nextResidual
  omega

#check top_residual_small

structure TopReady (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (low : Bool) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (routeResidual index (OuterSigning.requiredCredit index) 0 low ds)
  small : routeResidual index (OuterSigning.requiredCredit index) 0 low ds<58
  hints : t.getMem (0x66000#64)=0
  c32 : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some ds
  length : ds.length=51
  saved : SavedTop ds t
  frame : Frame s t WorkWrites

#check TopReady

def TopStagePost (im : Image) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option (BitVec 32×List Nat×Bool)→MachineState→Prop
  | none,t => SearchError im t
  | some (_,ds,low),t => TopReady index p forest low ds s t

#check TopStagePost

theorem top_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : TopSetupSteps im) (htailSteps : TopTailSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost 0+78)
      (CanonicalPolicy.layerCounterSearchAt 0 (ClaudeWCT.WCT9.Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)) (route index 0).2 (route index 0).1
        (.pair (ClaudeWCT.WCT9.topPair 1 p.one.levels).1 (ClaudeWCT.WCT9.topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im index p forest s) := by
  obtain ⟨a,sa,ha⟩ := ht.setup s hp index hi hstable.indexMem _ _ hstable.one.left hstable.one.right
  have haf : Frame s a WorkWrites := ha.frame.mono (fun _ _=>topSetupWrites_subset)
  have hsta : Stable index p forest a := hstable.frame haf ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold SigGolfCandidate.T3M.Sign.ENC;omega) (by unfold SigGolfCandidate.T3M.Sign.ENC;omega)).trans hcv⟩
  have H := hs.call (topArgs index (ClaudeWCT.WCT9.topPair 1 p.one.levels)) a (top_pre index hi _ s a ha hsta.tables hac)
  have Htail : TBSim im sk a (Canonical.csCost 0+52)
      (CanonicalPolicy.layerCounterSearchAt 0 (ClaudeWCT.WCT9.Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)) (route index 0).2 (route index 0).1
        (.pair (ClaudeWCT.WCT9.topPair 1 p.one.levels).1 (ClaudeWCT.WCT9.topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im index p forest s) := by
    have hb := TBSim.bind H (f:=fun r=>pure r) (W₂:=52) (Q₂:=TopStagePost im index p forest s) (by
      intro r u hu
      cases r with
      | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=TopStagePost im index p forest s) hu).mono (by omega) (fun _ _ h=>h)
      | some pair =>
        obtain ⟨c,ds,low⟩ := pair
        rcases hu with ⟨up,hc,uc19,uc32,hdec,hlen,hdigs,ur,uf,usum,ucredit,hfloor⟩
        have huf : Frame a u WorkWrites := uf.mono (fun _ _=>csWrites_subset)
        have hstu : Stable index p forest u := hsta.frame huf ur (by decide)
        have hleafEq : (route index 0).1 = index/2^19 := by
          change index/2^19%2^12=index/2^19
          apply Nat.mod_eq_of_lt
          omega
        have h18u : u.getReg .x18=BitVec.ofNat 64 (route index 0).1 := by
          rw [ur.get (by decide),ha.x18,hleafEq]
        obtain ⟨t,k,ut,hk,htail⟩ := top_tail htailSteps index (by omega) u up hstu.indexMem h18u low ds ucredit
        have htf : Frame u t WorkWrites := htail.frame.mono (fun _ _=>topTail_subset)
        have hstt : Stable index p forest t := hstu.frame htf htail.regs (by decide)
        refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
        refine ⟨htail.pc,htail.layer,htail.residual,top_residual_small index hfloor,?_,?_,hstt,hdec,hlen,⟨u,hdigs,htail.saved⟩,?_⟩
        · exact (htail.frame.get (by decide) (by unfold TopTailWrites;omega)).trans
            ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans
              ((ha.frame.get (by decide) (by unfold SigGolfCandidate.T3M.Sign.ENC;omega)).trans hh))
        · exact ⟨c.toNat,by omega,
            (htail.frame.get (by unfold SigGolfCandidate.T3M.Sign.ENC;omega) (by unfold TopTailWrites SigGolfCandidate.T3M.Sign.ENC;omega)).trans uc32⟩
        · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
    simpa only [bind_pure,topArgs,lowerArgs] using hb
  exact (TBSim.steps sa Htail).mono (by omega) (fun _ _ h=>h)

#check top_stage

theorem lower_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : LowerSetupSteps im) (htail : LowerTailSteps im)
    (lay : Layer) (hl : lay≠0) (index residual hints : Nat) (hi : index<2^31) (hr : residual<stageBound lay)
    (p : PreparedRoots) (forest : Digest×Digest) (s : MachineState) (hp : s.pc=pcOf 22240)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hstable : Stable index p forest s)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual) (hhm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost lay+723)
      (CanonicalPolicy.layerCounterSearchAt lay (ClaudeWCT.WCT9.Policy75Safe23.threshold lay.val residual)
        (route index lay).2 (route index lay).1 (.pair (messageAt p forest lay).1 (messageAt p forest lay).2) 0 (searchLimit lay))
      (LowerStagePost im lay index residual hints p forest s) := by
  have hln : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt;have : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  obtain ⟨a,ka,ca,sa,hca,ha⟩ := ht.setup s hp lay.val index residual hints hln hi hr h8 hstable.indexMem hrm hhm
  have haf : Frame s a (LowerWrites lay) := ha.frame.mono (fun _ _=>lowerSetupWrites_subset lay)
  have hsta : Stable index p forest a := hstable.frame (haf.mono (fun _ _=>lowerWrites_subset lay hl)) ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold SigGolfCandidate.T3M.Sign.ENC;omega) (by unfold SigGolfCandidate.T3M.Sign.ENC;omega)).trans hcv⟩
  obtain ⟨hp0,hp1⟩ := hstable.message lay hl
  have H := hs.call (lowerArgs lay index (ClaudeWCT.WCT9.Policy75Safe23.threshold lay.val residual) (messageAt p forest lay)) a
    (lower_pre lay hl index residual hints hi _ s a ha hsta.tables hac hp0 hp1 (floor_small lay hl residual hr).1)
  have HB := TBSim.bind H (f:=fun r=>pure r) (W₂:=603) (Q₂:=LowerStagePost im lay index residual hints p forest s) (by
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
          ((ha.frame.get (by decide) (by unfold SigGolfCandidate.T3M.Sign.ENC;omega)).trans hrm)
      have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
      obtain ⟨t,k,ut,hk,ht⟩ := lower_tail htail lay hl index (by omega) (route index lay).1 residual (preparedAt p lay) low ds
        (lower_decode_digits lay hl hdec) u up uh8 hstu.indexMem (by simpa only [lowerArgs,hcc,Search.DIGITS,SigGolfCandidate.T3M.Sign.DIGITS] using hdigs)
        (fun j hj d hd=>hsp.saved j hj d (by omega)) hsp.path (by unfold stageBound at hr;split_ifs at hr <;> omega) uhrm ucredit
      have htf : Frame u t (LowerWrites lay) := ht.frame.mono (by intro A hA h;unfold LowerWrites;rcases h with h|rfl;tauto;omega)
      have hstt : Stable index p forest t := hstu.frame (htf.mono (fun _ _=>lowerWrites_subset lay hl)) ht.regs (by decide)
      refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
      refine ⟨ht.pc,ht.layer,ht.residual,?_,?_,hstt,ht.values,ht.path,hfloor,?_,?_⟩
      · exact (ht.frame.get (by decide) (by unfold LowerTailWrites SharedRootControl.sigBase;split_ifs <;> omega)).trans
          ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans ha.hints)
      · exact ⟨c.toNat,by omega,(ht.frame.get (by unfold SigGolfCandidate.T3M.Sign.ENC;omega)
          (by unfold LowerTailWrites SharedRootControl.sigBase SigGolfCandidate.T3M.Sign.ENC;split_ifs <;> omega)).trans uc32⟩
      · rw [ht.regs.get (by decide)]
        simpa [lowerArgs,CanonicalPolicy.normalLayer,hl,T3.target] using usum
      · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
  have HC := TBSim.steps sa HB
  simpa only [bind_pure,topArgs,lowerArgs] using HC.mono (by change ca+(Canonical.csCost lay+603)≤Canonical.csCost lay+723;omega) (fun _ _ h=>h)

#check lower_stage

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

#check Choices

def Choices.r1 (a : Choices) (index : Nat) := routeResidual index (OuterSigning.requiredCredit index) 0 a.l0 a.d0

#check Choices.r1

def Choices.r2 (a : Choices) (index : Nat) := routeResidual index (a.r1 index) 1 a.l1 a.d1

#check Choices.r2

def Choices.r3 (a : Choices) (index : Nat) := routeResidual index (a.r2 index) 2 a.l2 a.d2

#check Choices.r3

def Choices.hints (a : Choices) (index : Nat) := 576*ClaudeWCT.WCT9.Policy75Safe23.threshold 1 (a.r1 index) +
  24*ClaudeWCT.WCT9.Policy75Safe23.threshold 2 (a.r2 index) + ClaudeWCT.WCT9.Policy75Safe23.threshold 3 (a.r3 index)

#check Choices.hints

def prefixSearch (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) : T3.M (Option Choices) := do
  let some (c0,d0,l0) ← CanonicalPolicy.layerCounterSearchAt 0 (ClaudeWCT.WCT9.Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)) (route index 0).2 (route index 0).1
    (.pair (ClaudeWCT.WCT9.topPair 1 p.one.levels).1 (ClaudeWCT.WCT9.topPair 1 p.one.levels).2) 0 (searchLimit 0) | pure none
  let r1 := routeResidual index (OuterSigning.requiredCredit index) 0 l0 d0
  let f1 := ClaudeWCT.WCT9.Policy75Safe23.threshold 1 r1
  if f1≥17 then return none
  let some (c1,d1,l1) ← CanonicalPolicy.layerCounterSearchAt 1 f1 (route index 1).2 (route index 1).1
    (.pair (ClaudeWCT.WCT9.topPair 2 p.two.levels).1 (ClaudeWCT.WCT9.topPair 2 p.two.levels).2) 0 (searchLimit 1) | pure none
  let r2 := routeResidual index r1 1 l1 d1
  let f2 := ClaudeWCT.WCT9.Policy75Safe23.threshold 2 r2
  if f2≥24 then return none
  let some (c2,d2,l2) ← CanonicalPolicy.layerCounterSearchAt 2 f2 (route index 2).2 (route index 2).1
    (.pair (ClaudeWCT.WCT9.topPair 3 p.three.levels).1 (ClaudeWCT.WCT9.topPair 3 p.three.levels).2) 0 (searchLimit 2) | pure none
  let r3 := routeResidual index r2 2 l2 d2
  let f3 := ClaudeWCT.WCT9.Policy75Safe23.threshold 3 r3
  if f3≥24 then return none
  let some (c3,d3,l3) ← CanonicalPolicy.layerCounterSearchAt 3 f3 (route index 3).2 (route index 3).1
    (.pair forest.1 forest.2) 0 (searchLimit 3) | pure none
  pure (some ⟨c0,c1,c2,c3,d0,d1,d2,d3,l0,l1,l2,l3⟩)

#check prefixSearch

structure PrefixReady (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (a : Choices)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=51
  n4 : t.getReg .x27=51
  target : t.getReg .x17=152
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some a.d0
  digits : ∀ j,j<51 → t.getByte (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.DIGITS+j))=BitVec.ofNat 8 (a.d0.getD j 0)
  sum : (t.getReg .x25).toNat≤201
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (a.hints index)
  residual : t.getMem (0x66008#64)=0
  credit : routeResidual index (a.r3 index) 3 a.l3 a.d3=0
  frame : Frame s t WorkWrites
  /-- N7g: the hint digits are in range (`f1 < 16`, `f2, f3 < 24`), so the hint is `< 12288` (mod-R pack). -/
  hintsLt : (a.hints index)<12288
  hintsOK : ClaudeWCT.W9.T3M.SharedCodec.HintOK (a.hints index)

#check PrefixReady

def PrefixPost (im : Image) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option Choices→MachineState→Prop
  | none,t => SearchError im t
  | some a,t => PrefixReady index p forest a s t

#check PrefixPost

theorem prefix_good {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s prefixCost (prefixSearch index p forest) (PrefixPost im index p forest s) := by
  unfold prefixSearch
  have H0 := top_stage hs htop htail index hi p forest s hp hstable hh hc32
  refine (TBSim.bind H0 (W₂:=(Canonical.csCost 1+723)+((Canonical.csCost 2+723)+((Canonical.csCost 3+723)+30))) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=prefixCost) (by unfold prefixCost;omega) (fun _ _ h=>h)
  intro r0 t0 h0
  cases r0 with
  | none => exact (TBSim.pure (a:=none) (s:=t0) (Q:=PrefixPost im index p forest s) h0).mono (by omega) (fun _ _ h=>h)
  | some a0 =>
    obtain ⟨c0,d0,l0⟩ := a0
    change TopReady index p forest l0 d0 s t0 at h0
    let r1 := routeResidual index (OuterSigning.requiredCredit index) 0 l0 d0
    let f1 := ClaudeWCT.WCT9.Policy75Safe23.threshold 1 r1
    have hf1 : f1<17 := (floor_small 1 (by decide) r1 h0.small).2 rfl
    dsimp only [f1,r1] at hf1
    simp only [if_neg (Nat.not_le.mpr hf1)]
    have H1 := lower_stage hs hlower hltail 1 (by decide) index r1 0 hi h0.small p forest t0
      h0.pc h0.layer h0.stable h0.residual h0.hints h0.c32
    refine (TBSim.bind H1 (W₂:=(Canonical.csCost 2+723)+((Canonical.csCost 3+723)+30)) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 1+723)+((Canonical.csCost 2+723)+((Canonical.csCost 3+723)+30))) (by omega) (fun _ _ h=>h)
    intro r1out t1 h1
    cases r1out with
    | none => exact (TBSim.pure (a:=none) (s:=t1) (Q:=PrefixPost im index p forest s) h1).mono (by omega) (fun _ _ h=>h)
    | some a1 =>
      obtain ⟨c1,d1,l1⟩ := a1
      change LowerReady 1 index r1 0 p forest l1 d1 t0 t1 at h1
      let r2 := routeResidual index r1 1 l1 d1
      let f2 := ClaudeWCT.WCT9.Policy75Safe23.threshold 2 r2
      have hr2 : r2<42 := (next_stage_bound index 1 (by decide) r1 h0.small l1 d1 h1.floor).1 (by decide)
      have hf2 : f2<24 := (floor_small 2 (by decide) r2 hr2).1
      have hints1 : t1.getMem (0x66000#64)=BitVec.ofNat 64 (576*f1) := by simpa [SharedHints.hintWeight] using h1.hints
      have saved1 : SavedTop d0 t1 := h0.saved.frame h1.frame (lowerWrites_saved 1)
      dsimp only [f2,r2,r1] at hf2
      simp only [if_neg (Nat.not_le.mpr hf2)]
      have H2 := lower_stage hs hlower hltail 2 (by decide) index r2 (576*f1) hi hr2 p forest t1
        h1.pc h1.layer h1.stable h1.residualMem hints1 h1.c32
      refine (TBSim.bind H2 (W₂:=(Canonical.csCost 3+723)+30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 2+723)+((Canonical.csCost 3+723)+30)) (by omega) (fun _ _ h=>h)
      intro r2out t2 h2
      cases r2out with
      | none => exact (TBSim.pure (a:=none) (s:=t2) (Q:=PrefixPost im index p forest s) h2).mono (by omega) (fun _ _ h=>h)
      | some a2 =>
        obtain ⟨c2,d2,l2⟩ := a2
        change LowerReady 2 index r2 (576*f1) p forest l2 d2 t1 t2 at h2
        let r3 := routeResidual index r2 2 l2 d2
        let f3 := ClaudeWCT.WCT9.Policy75Safe23.threshold 3 r3
        have hr3 : r3<24 := (next_stage_bound index 2 (by decide) r2 hr2 l2 d2 h2.floor).1 (by decide)
        have hf3 : f3<24 := (floor_small 3 (by decide) r3 hr3).1
        have hints2 : t2.getMem (0x66000#64)=BitVec.ofNat 64 (576*f1+24*f2) := by simpa [SharedHints.hintWeight] using h2.hints
        have saved2 : SavedTop d0 t2 := saved1.frame h2.frame (lowerWrites_saved 2)
        have one1 : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one d1) t1 := ⟨h1.values,h1.path⟩
        have one2 := one1.frame_lower (current:=2) (by decide) (by decide) (by decide)
          (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 h2.frame
        dsimp only [f3,r3,r2,r1] at hf3
        simp only [if_neg (Nat.not_le.mpr hf3)]
        have H3 := lower_stage hs hlower hltail 3 (by decide) index r3 (576*f1+24*f2) hi hr3 p forest t2
          h2.pc h2.layer h2.stable h2.residualMem hints2 h2.c32
        refine (TBSim.bind H3 (W₂:=30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 3+723)+30) (by omega) (fun _ _ h=>h)
        intro r3out t3 h3
        cases r3out with
        | none => exact (TBSim.pure (a:=none) (s:=t3) (Q:=PrefixPost im index p forest s) h3).mono (by omega) (fun _ _ h=>h)
        | some a3 =>
          obtain ⟨c3,d3,l3⟩ := a3
          change LowerReady 3 index r3 (576*f1+24*f2) p forest l3 d3 t2 t3 at h3
          have hz : routeResidual index r3 3 l3 d3=0 :=
            (next_stage_bound index 3 (by decide) r3 hr3 l3 d3 h3.floor).2 rfl
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
            h0.decoded,ht.digits,ht.sum,?_,?_,?_,?_,?_,hz,?_,?_,?_⟩
          · exact one3.frame_finish (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 ht.frame
          · exact two3.frame_finish (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 ht.frame
          · exact three3.frame_finish (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 ht.frame
          · have hm := (ht.frame.get (A:=0x66000) (by decide) (by unfold SigGolfCandidate.T3M.Sign.DIGITS;omega)).trans h3.hints
            change t.getMem (0x66000#64)=BitVec.ofNat 64 (576*f1+24*f2+f3)
            simpa [SharedHints.hintWeight] using hm
          · have hm := (ht.frame.get (A:=0x66008) (by decide) (by unfold SigGolfCandidate.T3M.Sign.DIGITS;omega)).trans h3.residualMem
            change t.getMem (0x66008#64)=BitVec.ofNat 64 0
            simpa only [hz] using hm
          · have F1 := h1.frame.mono (fun _ _=>lowerWrites_subset 1 (by decide))
            have F2 := h2.frame.mono (fun _ _=>lowerWrites_subset 2 (by decide))
            have F3 := h3.frame.mono (fun _ _=>lowerWrites_subset 3 (by decide))
            have F4 : Frame t3 t WorkWrites := ht.frame.mono (by intro A hA h;unfold WorkWrites;omega)
            exact ((((h0.frame.trans F1).trans F2).trans F3).trans F4).mono (by
              intro A hA h;rcases h with (((h|h)|h)|h)|h <;> exact h)
          · simp only [Choices.hints,Choices.r1,Choices.r2,Choices.r3]
            omega
          · exact ClaudeWCT.W9.T3M.SharedCodec.hints_ok_table ⟨r1,h0.small⟩ ⟨r2,hr2⟩ ⟨r3,hr3⟩

#check prefix_good

def finishSource (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots)
    (a : Choices) : T3.M (Option CanonicalLayers) := do
  let top ← T3.signTop cache (route index 0).1 a.d0
  pure (some ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],routeResidual index (a.r3 index) 3 a.l3 a.d3,
    BitVec.ofNat 16 (a.hints index)⟩)

#check finishSource

theorem searchPreparedLayers_prefix (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) :
    OuterSigning.searchPreparedLayers cache index p forest =
      prefixSearch index p forest >>= fun
        | none => pure none
        | some a => finishSource cache index p a := by
  unfold OuterSigning.searchPreparedLayers prefixSearch
  simp only [CanonicalPolicy.totalCredit,ClaudeWCT.WCT9.Policy75Safe23.threshold_top]
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
                have hlast : ∀ r low ds, routeResidual index r 3 low ds=CanonicalPolicy.nextResidual r 3 low ds := by
                  intro r low ds
                  simp [routeResidual,LocalRoute.ownSave,CanonicalPolicy.lowerPathSave]
                simp only [pure_bind,finishSource,Choices.r1,Choices.r2,Choices.r3,Choices.hints,hlast]

#check searchPreparedLayers_prefix

def layersValue (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces) : CanonicalLayers :=
  ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],routeResidual index (a.r3 index) 3 a.l3 a.d3,
    BitVec.ofNat 16 (a.hints index)⟩

#check layersValue

structure Completed (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces)
    (t : MachineState) : Prop where
  pc : t.pc=pcOf 540
  topValues : ∀ i<51,DigAt t (SigGolfCandidate.T3M.Sign.SIG+2240+16*i) (top.1.getD i 0)
  topPath : ∀ j<12,DigAt t (SigGolfCandidate.T3M.Sign.SIG+3056+16*j) (top.2.getD j 0)
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (a.hints index)
  residual : t.getMem (0x66008#64)=0
  credit : routeResidual index (a.r3 index) 3 a.l3 a.d3=0
  hintsLt : (a.hints index)<12288
  hintsOK : ClaudeWCT.W9.T3M.SharedCodec.HintOK (a.hints index)

#check Completed

def LayersPost (im : Image) (index : Nat) (p : PreparedRoots) : Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => ∃ a top,layers=layersValue index p a top ∧ Completed index p a top t

#check LayersPost

def FramedLayersPost (im : Image) (index : Nat) (p : PreparedRoots) (s : MachineState) :
    Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => LayersPost im index p (some layers) t ∧ Frame s t (fun A=>WorkWrites A ∨ L0W A)

#check FramedLayersPost

theorem searchPreparedLayers_framed {im : Image} {sk : SecretKey} {cache : Bytes 131072}
    (hc : TopCalls im sk cache) (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (prefixCost+335006) (OuterSigning.searchPreparedLayers (cacheDec cache) index p forest)
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
    have hregs : SigGolfCandidate.T3M.Sign.Packed.Boundary.TopRegs (index/2^19) u :=
      ⟨hu.layer,hu.tree,hu.selected.trans hu.leaf,hu.chains,hu.n4⟩
    have hd7 : ∀ i<51,a.d0.getD i 0≤T3.maxDigit 0 i := by
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
    refine ⟨⟨a,top,rfl,htpc,htv,htp,?_,?_,?_,hth.trans hu.hints,htr.trans hu.residual,hu.credit,hu.hintsLt,hu.hintsOK⟩,hu.frame.trans htf⟩
    · exact hu.one.frame_top (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 htf
    · exact hu.two.frame_top (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 htf
    · exact hu.three.frame_top (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 htf
#print axioms prefix_good
#print axioms searchPreparedLayers_framed
end OuterSignSearchSource
