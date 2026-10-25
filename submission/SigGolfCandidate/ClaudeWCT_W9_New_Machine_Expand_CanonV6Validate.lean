import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Routine

/-! # img-v6 expand final policy check (canon-v6 porter)

Machine proof of the expand policy check at 46929..46979 for the img-v6 image: credit pool 69, policy hints in
the mixed radix `484·f1 + 22·f2 + f3`, L1 floors by residual `< 56`, L2 `< 41`, L3 floor = residual `< 22`.
Adapted from `SharedValidate` in `Expand/H2Front.lean` (e7b: pool 72, radix 20); new namespace
`SharedValidateV6`, result `validate_source_steps` against `SharedForest.policyHintsValid` (bound 7744). -/

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def first0Code : List (BitVec 32) := [0x66e37,0xe0e13,0x40e3303,0x1536663]
sym_block first0Run := symRun {noAlias:=true} first0Code (pcOf 46933) 20
def zero0Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero0Run := symRun {noAlias:=true} zero0Code (pcOf 46937) 20
def sub0Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub0Run := symRun {noAlias:=true} sub0Code (pcOf 46939) 20
theorem first0_steps {im : Image} (hc : CodeAt im (pcOf 46933) first0Code)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46939 else pcOf 46937) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417856#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first0Run hc s hp (by simp [first0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first0Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first0Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero0_steps {im : Image} (hc : CodeAt im (pcOf 46937) zero0Code)
    (s : MachineState) (hp : s.pc=pcOf 46937) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero0Run hc s hp (by simp [zero0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub0_steps {im : Image} (hc : CodeAt im (pcOf 46939) sub0Code)
    (s : MachineState) (hp : s.pc=pcOf 46939) (R C : Nat) (hR : R≤69) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub0Run hc s hp (by simp [sub0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub0Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual0Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46933) first0Code
  zero : CodeAt im (pcOf 46937) zero0Code
  sub : CodeAt im (pcOf 46939) sub0Code

theorem residual0_steps {im : Image} [hc : Residual0Code im]
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first0_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub0_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero0_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
def first1Code : List (BitVec 32) := [0x66e37,0xe0e13,0x48e3303,0x1536663]
sym_block first1Run := symRun {noAlias:=true} first1Code (pcOf 46949) 20
def zero1Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero1Run := symRun {noAlias:=true} zero1Code (pcOf 46953) 20
def sub1Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub1Run := symRun {noAlias:=true} sub1Code (pcOf 46955) 20
theorem first1_steps {im : Image} (hc : CodeAt im (pcOf 46949) first1Code)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46955 else pcOf 46953) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417864#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first1Run hc s hp (by simp [first1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first1Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first1Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero1_steps {im : Image} (hc : CodeAt im (pcOf 46953) zero1Code)
    (s : MachineState) (hp : s.pc=pcOf 46953) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero1Run hc s hp (by simp [zero1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub1_steps {im : Image} (hc : CodeAt im (pcOf 46955) sub1Code)
    (s : MachineState) (hp : s.pc=pcOf 46955) (R C : Nat) (hR : R≤69) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub1Run hc s hp (by simp [sub1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub1Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual1Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46949) first1Code
  zero : CodeAt im (pcOf 46953) zero1Code
  sub : CodeAt im (pcOf 46955) sub1Code

theorem residual1_steps {im : Image} [hc : Residual1Code im]
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first1_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub1_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero1_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
def first2Code : List (BitVec 32) := [0x66e37,0xe0e13,0x50e3303,0x1536663]
sym_block first2Run := symRun {noAlias:=true} first2Code (pcOf 46966) 20
def zero2Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero2Run := symRun {noAlias:=true} zero2Code (pcOf 46970) 20
def sub2Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub2Run := symRun {noAlias:=true} sub2Code (pcOf 46972) 20
theorem first2_steps {im : Image} (hc : CodeAt im (pcOf 46966) first2Code)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46972 else pcOf 46970) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417872#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first2Run hc s hp (by simp [first2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first2Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first2Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero2_steps {im : Image} (hc : CodeAt im (pcOf 46970) zero2Code)
    (s : MachineState) (hp : s.pc=pcOf 46970) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero2Run hc s hp (by simp [zero2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub2_steps {im : Image} (hc : CodeAt im (pcOf 46972) sub2Code)
    (s : MachineState) (hp : s.pc=pcOf 46972) (R C : Nat) (hR : R≤69) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub2Run hc s hp (by simp [sub2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub2Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual2Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46966) first2Code
  zero : CodeAt im (pcOf 46970) zero2Code
  sub : CodeAt im (pcOf 46972) sub2Code

theorem residual2_steps {im : Image} [hc : Residual2Code im]
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first2_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub2_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero2_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def initCode : List (BitVec 32) := [0x66e37,0xe0e13,0xe3a03,0x4500a93]
sym_block initRun := symRun {noAlias:=true} initCode (pcOf 46929) 100
def range1Code : List (BitVec 32) := [0x3800393,0x87afc63]
sym_block range1Run := symRun {noAlias:=true} range1Code (pcOf 46940) 100
def range2Code : List (BitVec 32) := [0x2900393,0x47afc63]
sym_block range2Run := symRun {noAlias:=true} range2Code (pcOf 46956) 100
def range3Code : List (BitVec 32) := [0x1600393,0x7afa63]
sym_block range3Run := symRun {noAlias:=true} range3Code (pcOf 46973) 100
def lastCode : List (BitVec 32) := [0x1600393,0x27a7eb3,0x1da9463]
sym_block lastRun := symRun {noAlias:=true} lastCode (pcOf 46975) 100
def goodCode : List (BitVec 32) := [0xea5fb06f]
sym_block goodRun := symRun {noAlias:=true} goodCode (pcOf 46978) 100
def badCode : List (BitVec 32) := [0xf7cd206f]
sym_block badRun := symRun {noAlias:=true} badCode (pcOf 46979) 100
theorem range1_steps {im : Image} (hc : CodeAt im (pcOf 46940) range1Code)
    (s : MachineState) (hp : s.pc=pcOf 46940) (R : Nat) (hR : R≤69)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<56 then pcOf 46942 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range1Run hc s hp (by simp [range1Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range1Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<56 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
theorem range2_steps {im : Image} (hc : CodeAt im (pcOf 46956) range2Code)
    (s : MachineState) (hp : s.pc=pcOf 46956) (R : Nat) (hR : R≤69)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<41 then pcOf 46958 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range2Run hc s hp (by simp [range2Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range2Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<41 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
theorem range3_steps {im : Image} (hc : CodeAt im (pcOf 46973) range3Code)
    (s : MachineState) (hp : s.pc=pcOf 46973) (R : Nat) (hR : R≤69)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<22 then pcOf 46975 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range3Run hc s hp (by simp [range3Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range3Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<22 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
theorem init_steps {im : Image} (hc : CodeAt im (pcOf 46929) initCode)
    (s : MachineState) (hp : s.pc=pcOf 46929) (hints : Nat)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 46933 ∧ t.getReg .x20=BitVec.ofNat 64 hints ∧
      t.getReg .x21=69 ∧ RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound initRun hc s hp (by simp [initRun.res,rv_simp]),rfl,?_,rfl,?_,?_⟩
  · simp [initRun.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open RiscvZkvm.Rv64
theorem rem22 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n%22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%22<2^64 by omega)]
  omega
theorem div22 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n/22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/22<2^64 by omega)]
  omega
theorem div484 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 484#64=BitVec.ofNat 64 (n/484) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/484<2^64 by omega)]
  omega
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def lookup1PreCode : List (BitVec 32) := [0xff9e37,0x390e0e13,0x15e0e33]
sym_block lookup1PreRun := symRun {noAlias:=true} lookup1PreCode (pcOf 46942) 100
def lookup1LoadCode : List (BitVec 32) := [0xe4303]
def lookup1PostCode : List (BitVec 32) := [0x1e400393,0x27a5eb3,0x7d31e63]
sym_block lookup1PostRun := symRun {noAlias:=true} lookup1PostCode (pcOf 46946) 100
theorem lookup1_pre {im : Image} (hc : CodeAt im (pcOf 46942) lookup1PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46945 ∧ t.getReg .x28=BitVec.ofNat 64 (16749456+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PreRun hc s hp (by simp [lookup1PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup1PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup1_load {im : Image} (hc : CodeAt im (pcOf 46945) lookup1LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46945) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46946 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46946;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup1_post {im : Image} (hc : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46946) (H F : Nat) (hH : H<8000) (hF : F<22)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if F=H/484 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PostRun hc s hp (by simp [lookup1PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup1PostRun.res]
    t3n [h6,h20]
    simp only [div484 H (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H/484)) ↔ F=H/484 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H/484 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
def lookup2PreCode : List (BitVec 32) := [0xff9e37,0x3d0e0e13,0x15e0e33]
sym_block lookup2PreRun := symRun {noAlias:=true} lookup2PreCode (pcOf 46958) 100
def lookup2LoadCode : List (BitVec 32) := [0xe4303]
def lookup2PostCode : List (BitVec 32) := [0x1600393,0x27a5eb3,0x27efeb3,0x3d31c63]
sym_block lookup2PostRun := symRun {noAlias:=true} lookup2PostCode (pcOf 46962) 100
theorem lookup2_pre {im : Image} (hc : CodeAt im (pcOf 46958) lookup2PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46961 ∧ t.getReg .x28=BitVec.ofNat 64 (16749520+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PreRun hc s hp (by simp [lookup2PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup2PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup2_load {im : Image} (hc : CodeAt im (pcOf 46961) lookup2LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46961) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46962 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46962;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup2_post {im : Image} (hc : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46962) (H F : Nat) (hH : H<8000) (hF : F<22)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 4 10 t ∧ t.pc=(if F=H/22%22 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PostRun hc s hp (by simp [lookup2PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup2PostRun.res]
    t3n [h6,h20]
    simp only [div22 H (by omega),rem22 (H/22) (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H/22%22)) ↔ F=H/22%22 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H/22%22 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
theorem lookup1_steps {im : Image}
    (hpre : CodeAt im (pcOf 46942) lookup1PreCode)
    (hload : CodeAt im (pcOf 46945) lookup1LoadCode)
    (hpost : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R H F : Nat) (hR : R<56) (hH : H<8000) (hF : F<22)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749456+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 7 10 t ∧ t.pc=(if F=H/484 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup1_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup1_load hload u pu (16749456+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup1_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
theorem lookup2_steps {im : Image}
    (hpre : CodeAt im (pcOf 46958) lookup2PreCode)
    (hload : CodeAt im (pcOf 46961) lookup2LoadCode)
    (hpost : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R H F : Nat) (hR : R<41) (hH : H<8000) (hF : F<22)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749520+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 8 14 t ∧ t.pc=(if F=H/22%22 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup2_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup2_load hload u pu (16749520+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup2_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
theorem last_steps {im : Image} (hc : CodeAt im (pcOf 46975) lastCode)
    (s : MachineState) (hp : s.pc=pcOf 46975) (R H : Nat) (hR : R≤69) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if H%22=R then pcOf 46978 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lastRun hc s hp (by simp [lastRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lastRun.res]
    t3n [h21,h20]
    rw [rem22 H (by omega)]
    have he : (BitVec.ofNat 64 R=BitVec.ofNat 64 (H%22)) ↔ H%22=R := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : H%22=R <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem good_steps {im : Image} (hc : CodeAt im (pcOf 46978) goodCode) (s : MachineState) (hp : s.pc=pcOf 46978) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 42795 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound goodRun hc s hp (by simp [goodRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
theorem bad_steps {im : Image} (hc : CodeAt im (pcOf 46979) badCode) (s : MachineState) (hp : s.pc=pcOf 46979) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 354 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound badRun hc s hp (by simp [badRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
structure Code (im : Image) : Prop where
  init : CodeAt im (pcOf 46929) initCode
  r0 : Residual0Code im
  r1 : Residual1Code im
  r2 : Residual2Code im
  range1 : CodeAt im (pcOf 46940) range1Code
  range2 : CodeAt im (pcOf 46956) range2Code
  range3 : CodeAt im (pcOf 46973) range3Code
  lookup1Pre : CodeAt im (pcOf 46942) lookup1PreCode
  lookup1Load : CodeAt im (pcOf 46945) lookup1LoadCode
  lookup1Post : CodeAt im (pcOf 46946) lookup1PostCode
  lookup2Pre : CodeAt im (pcOf 46958) lookup2PreCode
  lookup2Load : CodeAt im (pcOf 46961) lookup2LoadCode
  lookup2Post : CodeAt im (pcOf 46962) lookup2PostCode
  last : CodeAt im (pcOf 46975) lastCode
  good : CodeAt im (pcOf 46978) goodCode
  bad : CodeAt im (pcOf 46979) badCode

def regs : List Reg := [.x6,.x7,.x21,.x28,.x29]
theorem phase1_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C H : Nat) (hR : R≤69) (hC : C<2^64) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417856#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<56 → T r<22)
    (hbytes : ∀ r,r<56 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤15 ∧ c≤18 ∧ Steps im s n c t ∧
      t.pc=(if R-C<56 ∧ H/484=T (R-C) then pcOf 46949 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r0
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual0_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range1_steps hc.range1 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<56
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup1_steps hc.lookup1Pre hc.lookup1Load hc.lookup1Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+7,n+2+10,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
theorem phase2_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C H : Nat) (hR : R≤69) (hC : C<2^64) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417864#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<41 → T r<22)
    (hbytes : ∀ r,r<41 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤16 ∧ c≤22 ∧ Steps im s n c t ∧
      t.pc=(if R-C<41 ∧ H/22%22=T (R-C) then pcOf 46966 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r1
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual1_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range2_steps hc.range2 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<41
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup2_steps hc.lookup2Pre hc.lookup2Load hc.lookup2Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+8,n+2+14,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
theorem phase3_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C H : Nat) (hR : R≤69) (hC : C<2^64) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417872#64)=BitVec.ofNat 64 C) :
    ∃t n c,n≤11 ∧ c≤14 ∧ Steps im s n c t ∧
      t.pc=(if R-C<22 ∧ H%22=R-C then pcOf 46978 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r2
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual2_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range3_steps hc.range3 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<22
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=last_steps hc.last v pv (R-C) H (by omega) hH
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
    refine ⟨t,n+2+3,n+2+6,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

abbrev Condition (H C0 C1 C2 : Nat) (T1 T2 : Nat→Nat) : Prop :=
  let R1:=69-C0
  let R2:=R1-C1
  let R3:=R2-C2
  R1<56 ∧ R2<41 ∧ R3<22 ∧ H/484=T1 R1 ∧ H/22%22=T2 R2 ∧ H%22=R3

theorem validate_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (H C0 C1 C2 : Nat)
    (hH : H<8000) (hC0 : C0<2^64) (hC1 : C1<2^64) (hC2 : C2<2^64)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 H)
    (hm0 : s.getMem (417856#64)=BitVec.ofNat 64 C0)
    (hm1 : s.getMem (417864#64)=BitVec.ofNat 64 C1)
    (hm2 : s.getMem (417872#64)=BitVec.ofNat 64 C2)
    (T1 T2 : Nat→Nat) (ht1 : ∀r,r<56→T1 r<22) (ht2 : ∀r,r<41→T2 r<22)
    (hb1 : ∀r,r<56→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T1 r))
    (hb2 : ∀r,r<41→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T2 r)) :
    ∃t n c,n≤47 ∧ c≤59 ∧ Steps im s n c t ∧
      t.pc=(if Condition H C0 C1 C2 T1 T2 then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u20,u21,ru,fu⟩:=init_steps hc.init s hp H hm
  obtain ⟨v,n1,c1,hn1,hc1,sv,pv,v21,rv,fv⟩:=phase1_steps hc u pu 69 C0 H (by omega) hC0 hH u21 u20
    (by rw [fu.get (by decide) (by simp)];exact hm0) T1 ht1
    (fun r hr=>by rw [fu.getByte (by omega) (by simp)];exact hb1 r hr)
  by_cases h1 : 69-C0<56 ∧ H/484=T1 (69-C0)
  · rw [if_pos h1] at pv
    obtain ⟨w,n2,c2,hn2,hc2,sw,pw,w21,rw_,fw⟩:=phase2_steps hc v pv (69-C0) C1 H (by omega) hC1 hH v21
      (by rw [rv.get (by decide)];exact u20)
      (by rw [fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm1) T2 ht2
      (fun r hr=>by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hb2 r hr)
    by_cases h2 : 69-C0-C1<41 ∧ H/22%22=T2 (69-C0-C1)
    · rw [if_pos h2] at pw
      obtain ⟨x,n3,c3,hn3,hc3,sx,px,x21,rx,fx⟩:=phase3_steps hc w pw (69-C0-C1) C2 H (by omega) hC2 hH w21
        (by rw [rw_.get (by decide),rv.get (by decide)];exact u20)
        (by rw [fw.get (by decide) (by simp),fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm2)
      by_cases h3 : 69-C0-C1-C2<22 ∧ H%22=69-C0-C1-C2
      · rw [if_pos h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=good_steps hc.good x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : Condition H C0 C1 C2 T1 T2 := by exact ⟨h1.1,h2.1,h3.1,h1.2,h2.2,h3.2⟩
          simpa only [if_pos hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
      · rw [if_neg h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h3 ⟨h.2.2.1,h.2.2.2.2.2⟩
          simpa [hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
    · rw [if_neg h2] at pw
      obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad w pw
      refine ⟨t,4+n1+n2+1,4+c1+c2+1,by omega,by omega,((su.trans sv).trans sw).trans st,?_,?_,?_⟩
      · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h2 ⟨h.2.1,h.2.2.2.2.1⟩
        simpa [hcond] using pt
      · exact (((ru.trans rv).trans rw_).trans rt).mono (by decide)
      · exact (((fu.trans fv).trans fw).trans ft).mono (by simp)
  · rw [if_neg h1] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad v pv
    refine ⟨t,4+n1+1,4+c1+1,by omega,by omega,(su.trans sv).trans st,?_,?_,?_⟩
    · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h1 ⟨h.1,h.2.2.2.1⟩
      simpa [hcond] using pt
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : Code im := by
  constructor
  · exact SharedCounterHooks.code_slice (off:=1873) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1877) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1881) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1883) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1893) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1897) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1899) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1910) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1914) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1916) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1884) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1900) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1917) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1886) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1889) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1890) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1902) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1905) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1906) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1919) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1922) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1923) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : Code Images.expandImage := code_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9 SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem credit_lt (lay : SigGolfCandidate.T3.Layer) (low : Bool) (digits : List Nat) :
    CanonicalPolicy.credit lay low digits<2^64 := by
  have hw : wordCredit lay digits≤SigGolfCandidate.T3.chainCount lay := by
    unfold wordCredit
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  have hs : savedCopies lay digits≤SigGolfCandidate.T3.chainCount lay := by
    unfold savedCopies
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  have hc : SigGolfCandidate.T3.chainCount lay≤54 := by fin_cases lay <;> decide +kernel
  have hb := CanonicalPolicy.pathBonus_le lay low
  unfold CanonicalPolicy.credit CanonicalPolicy.pathReward CanonicalPolicy.reward
  omega

theorem validate_source_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hH : hints.toNat<8000) (hlen : digits.length=4)
    (hfloor : ∀lay:SigGolfCandidate.T3.Layer, SharedForest.hintFloor hints lay≤
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val []))
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat)
    (hcredits : ∀lay:SigGolfCandidate.T3.Layer,s.getMem (BitVec.ofNat 64 (417856+8*lay.val))=
      BitVec.ofNat 64 (CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])))
    (ht1 : ∀r,r<56→CanonicalPolicy.threshold 1 r<22)
    (ht2 : ∀r,r<41→CanonicalPolicy.threshold 2 r<22)
    (hb1 : ∀r,r<56→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 1 r))
    (hb2 : ∀r,r<41→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 2 r)) :
    ∃t n c,n≤47 ∧ c≤59 ∧ Steps im s n c t ∧
      t.pc=(if SharedForest.policyHintsValid hints digits lows then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t,n,c,hn,hc',st,pt,rt,ft⟩:=validate_steps hc s hp hints.toNat
    (CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])) hH (credit_lt _ _ _) (credit_lt _ _ _)
    (credit_lt _ _ _) hm
    (hcredits 0) (hcredits 1) (hcredits 2)
    (CanonicalPolicy.threshold 1) (CanonicalPolicy.threshold 2) ht1 ht2 hb1 hb2
  refine ⟨t,n,c,hn,hc',st,?_,rt,ft⟩
  have hh:=SharedValidate.policyCondition_iff hints digits lows hH hlen (by simpa [SharedForest.hintFloor,CanonicalPolicy.topFloor] using hfloor 0)
    (hfloor 1) (hfloor 2)
  change (Condition hints.toNat (CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 []))
    (CanonicalPolicy.threshold 1) (CanonicalPolicy.threshold 2) ↔ SharedForest.policyHintsValid hints digits lows=true) at hh
  simpa only [hh] using pt
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6
