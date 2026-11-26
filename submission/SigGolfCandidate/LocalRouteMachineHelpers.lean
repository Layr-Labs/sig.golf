import SigGolfCandidate.Route16Machine
import SigGolfCandidate.Merge055
import SigGolfCandidate.LocalRouteAddress
set_option debug.skipKernelTC false
set_option linter.all false
namespace LocalRouteMachineHelpers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option Elab.async false
def poolForLeaf (leaf : Nat) : Nat  := 74-ClaudeWCT.WCT9.CanonicalPolicy.topPathSave leaf
def rootFloor (leaf : Nat) : Nat := max 16 (poolForLeaf leaf-57)
theorem rootFloor_eq (leaf : Nat) : rootFloor leaf = SigGolfCandidate.Route16Guard.floor leaf := by
  rw [SigGolfCandidate.Route16Guard.floor_eq_threshold]
  rfl
abbrev guardCode := SigGolfCandidate.Route16Machine.guardCode
abbrev expandRootCode := SigGolfCandidate.Route16Machine.expandCode
theorem guard_steps {im : Image} (hc : CodeAt im (pcOf 26008) guardCode)
    (s : MachineState) (hp : s.pc=pcOf 26008) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66018=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 1959 ∧
      t.getReg .x29=BitVec.ofNat 64 (rootFloor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  simpa only [rootFloor_eq] using SigGolfCandidate.Route16Machine.guard_steps hc s hp leaf credit hl h18 hm
theorem expandRoot_steps {im : Image} (hc : CodeAt im (pcOf 88095) expandRootCode)
    (s : MachineState) (hp : s.pc=pcOf 88095) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66040=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 54317 ∧
      t.getReg .x29=BitVec.ofNat 64 (rootFloor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  simpa only [rootFloor_eq] using SigGolfCandidate.Route16Machine.expand_steps hc s hp leaf credit hl h18 hm
def expand1JumpCode : List (BitVec 32) := [0xb80006f]
sym_block expand1Jump := symRun {noAlias:=true} expand1JumpCode (pcOf 88060) 4
def expand1Code : List (BitVec 32) := [0x40e3303,0x203b7,0x5503b383,0xc3d393,0x13de13,0x1c3c3b3,0x3f3f393,0x43be13,0x1e4e13,0x7e7e33,0x7033b3,0x1c383b3,0x1533e33,0x41c00e33,0x1c3f3b3,0x730333,0xc79d706f]
sym_block expand1 := symRun {noAlias:=true} expand1Code (pcOf 88106) 30
theorem expand1_counts : expand1.res.steps=17 ∧ expand1.res.cycles=17 := by decide +kernel
def expand2Code : List (BitVec 32) := [0x48e3303,0x20e37,0x550e3383,0x63d393,0x33f393,0x13de13,0x1c3c3b3,0x13f393,0x1533e33,0x1c3f3b3,0x730333,0xd55d706f]
sym_block expand2 := symRun {noAlias:=true} expand2Code (pcOf 88072) 30
theorem expand2_counts : expand2.res.steps=12 ∧ expand2.res.cycles=12 := by decide +kernel
def expand3Code : List (BitVec 32) := [0x50e3303,0x20e37,0x550e3383,0x33f393,0x13de13,0x1c3c3b3,0x13f393,0x1533e33,0x1c3f3b3,0x730333,0xd6dd706f]
sym_block expand3 := symRun {noAlias:=true} expand3Code (pcOf 88084) 30
theorem expand3_counts : expand3.res.steps=11 ∧ expand3.res.cycles=11 := by decide +kernel
def signTopJumpCode : List (BitVec 32) := [0x869e806f]
sym_block signTopJump := symRun {noAlias:=true} signTopJumpCode (pcOf 26019) 4
def signTopCode : List (BitVec 32) := [0x18e3383,0x20e37,0x550e3e03,0xce5e13,0x1e5193,0x3e4e33,0x3fe7e13,0x4e3193,0x11c193,0x1c1f1b3,0x1c03e33,0x3e0e33,0x63b1b3,0x403001b3,0x3e7e33,0x1c383b3,0x66e37,0x4311306f]
sym_block signTop := symRun {noAlias:=true} signTopCode (pcOf 1981) 30
def signTwoCode : List (BitVec 32) := [0x20e37,0x550e3e03,0x6e5e13,0x3e7e13,0x1e5193,0x3e4e33,0x1e7e13,0x63b1b3,0x3e7e33,0x1c383b3,0x66e37,0xfccfc06f]
sym_block signTwo := symRun {noAlias:=true} signTwoCode (pcOf 26038) 30
def signThreeCode : List (BitVec 32) := [0x20e37,0x550e3e03,0x3e7e13,0x1e5193,0x3e4e33,0x1e7e13,0x63b1b3,0x3e7e33,0x1c383b3,0x66e37,0xfa0fc06f]
sym_block signThree := symRun {noAlias:=true} signThreeCode (pcOf 26050) 30
open ClaudeWCT.WCT9.CanonicalPolicy
theorem extract_word (n k bits : Nat) (hn : n<2^64) (hb : bits<64) :
    (BitVec.ofNat 64 n >>> k) &&& BitVec.ofNat 64 (2^bits-1) =
      BitVec.ofNat 64 ((n/2^k)%2^bits) := by
  apply BitVec.eq_of_toNat_eq
  have hp : 2^bits<2^64 := Nat.pow_lt_pow_right (by decide) hb
  have hm : 2^bits-1<2^64 := by omega
  have hresult : (n/2^k)%2^bits<2^64 := (Nat.mod_lt _ (by positivity)).trans hp
  simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hm,Nat.mod_eq_of_lt hresult,
    Nat.shiftRight_eq_div_pow,Nat.and_two_pow_sub_one_eq_mod]

def lowerWord (lay : Nat) (w : Word) : Word :=
  if lay=1 then (46#64 >>> (((w >>> 12) &&& 7#64).toNat%64)) &&& 1#64
  else let v := (w >>> (if lay=2 then 6 else 0)) &&& 3#64
       (v ^^^ (v >>> 1)) &&& 1#64

theorem lower_word (lay n : Nat) (hl : 2≤lay ∧ lay≤3) (hn : n<2^64) :
    lowerWord lay (BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (lowerPathSave lay (n/2^(if lay=1 then 12 else if lay=2 then 6 else 0))) := by
  have h7 := extract_word n 12 3 hn (by decide)
  have h3a := extract_word n 6 2 hn (by decide)
  have h3b := extract_word n 0 2 hn (by decide)
  have hcases : lay=2 ∨ lay=3 := by omega
  rcases hcases with rfl | rfl
  · simp only [lowerWord,show ¬(2=1) from by decide,ite_false,ite_true,
      show (2:Nat)^2-1=3 from rfl] at h3a ⊢
    rw [h3a]
    generalize hx : n/2^6%4=x
    have hxlt : x<4 := by rw [←hx];omega
    interval_cases x <;> simp_all [lowerPathSave] <;> decide
  · simp only [lowerWord,show ¬(3=1) from by decide,show ¬(3=2) from by decide,ite_false,
      show (2:Nat)^2-1=3 from rfl] at h3b ⊢
    rw [h3b]
    generalize hx : n/2^0%4=x
    have hxlt : x<4 := by rw [←hx];omega
    interval_cases x <;> simp_all [lowerPathSave] <;> decide
#print axioms lower_word
theorem gated_word (r c saved : Nat) (hr : r<2^64) (hc : c<2^64) (hs : saved≤1) :
    BitVec.ofNat 64 c + (BitVec.ofNat 64 saved &&&
      (if (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 r) then 1#64 else 0#64)) =
    BitVec.ofNat 64 (guardedCredit r c saved) := by
  have hu : (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 r) = decide (c<r) := by
    simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hr]
  rw [hu]
  have hcS : saved=0 ∨ saved=1 := by omega
  rcases hcS with rfl | rfl <;> by_cases h : c<r <;>
    simp [h,guardedCredit,BitVec.ofNat_add]
#print axioms gated_word
/-- Layer-1 save selector of the relocated credit blocks: `[d≠0] + [d≥4 ∧ d odd]` on `d = l1Diff`. -/
def l1Sel (d : Word) : Word :=
  (if (0#64).ult d = true then 1#64 else 0#64) + (((if d.ult 4#64 = true then 1#64 else 0#64) ^^^ 1#64) &&& d)
def l1Nat (m : Nat) : Nat := (if m = 0 then 0 else 1) + (if m % 2 = 1 ∧ 4 ≤ m then 1 else 0)
theorem l1Sel_table : ∀ m : Fin 64, l1Sel (BitVec.ofNat 64 m.val) = BitVec.ofNat 64 (l1Nat m.val) := by decide +kernel
theorem l1Diff_word (n : Nat) (hn : n<2^64) :
    (BitVec.ofNat 64 n >>> 12 ^^^ BitVec.ofNat 64 n >>> 13) &&& 63#64 = BitVec.ofNat 64 (l1Diff (n/2^12)) := by
  apply BitVec.eq_of_toNat_eq
  have hd : l1Diff (n/2^12) < 64 := by unfold l1Diff; omega
  simp only [BitVec.toNat_and,BitVec.toNat_xor,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt (show l1Diff (n/2^12) < 2^64 by omega),Nat.shiftRight_eq_div_pow]
  rw [show (63:Nat) % 2^64 = 2^6-1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  unfold l1Diff
  have h13 : n/2^13 = n/2^12/2 := by rw [Nat.div_div_eq_div_mul]; norm_num
  rw [h13]
  generalize n/2^12 = L
  rw [show (128:Nat)=2^7 from rfl, show (64:Nat)=2^6 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_div_two]
  by_cases hi : i < 6
  · have : i+1 < 7 := by omega
    simp [hi, this, show i < 7 by omega]
  · simp [hi]
theorem l1_word (n : Nat) (hn : n<2^64) :
    l1Sel ((BitVec.ofNat 64 n >>> 12 ^^^ BitVec.ofNat 64 n >>> 13) &&& 63#64) =
      BitVec.ofNat 64 (lowerPathSave 1 (n/2^12)) := by
  rw [l1Diff_word n hn]
  have hd : l1Diff (n/2^12) < 64 := by unfold l1Diff; omega
  have h := l1Sel_table ⟨_, hd⟩
  simpa [l1Nat, lowerPathSave] using h
theorem gated2_word (r c saved : Nat) (hr : r<2^64) (hc : c<2^64) (hs : saved≤2) :
    BitVec.ofNat 64 c + (BitVec.ofNat 64 saved &&&
      -(if (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 r) = true then 1#64 else 0#64)) =
    BitVec.ofNat 64 (guardedCredit r c saved) := by
  have hu : (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 r) = decide (c<r) := by
    simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hr]
  rw [hu]
  have hcS : saved=0 ∨ saved=1 ∨ saved=2 := by omega
  rcases hcS with rfl | rfl | rfl <;> by_cases h : c<r <;>
    simp [h,guardedCredit,BitVec.ofNat_add]
#print axioms l1_word
#print axioms gated2_word
theorem expand1Far_steps {im : Image} (hc : CodeAt im (pcOf 88106) expand1Code)
    (s : MachineState) (hp : s.pc=pcOf 88106) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (h28 : s.getReg .x28=0x66000#64) (hr : s.getReg .x21=BitVec.ofNat 64 residual)
    (hm : s.getMem 417856#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 17 17 t ∧ t.pc=pcOf 46936 ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := expand1.res.toState s
  refine ⟨t,symRun_sound expand1 hc s hp (by simp [expand1.res,rv_simp,h28];decide),rfl,?_,?_,?_⟩
  · have hw := l1_word index hi
    have hg := gated2_word residual credit (lowerPathSave 1 (index/2^12)) hrLt hcLt (lowerPathSave_le_two 1 (index/2^12))
    rw [←hw] at hg
    simp [t,expand1.res,rv_simp,h28,hr]
    rw [hm,hindex]
    simpa [l1Sel] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms expand1Far_steps
theorem expand1_steps {im : Image} (hj : CodeAt im (pcOf 88060) expand1JumpCode)
    (hc : CodeAt im (pcOf 88106) expand1Code)
    (s : MachineState) (hp : s.pc=pcOf 88060) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (h28 : s.getReg .x28=0x66000#64) (hr : s.getReg .x21=BitVec.ofNat 64 residual)
    (hm : s.getMem 417856#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 46936 ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let u := expand1Jump.res.toState s
  have su : Steps im s 1 1 u := symRun_sound expand1Jump hj s hp (by simp [expand1Jump.res,rv_simp])
  have ru : RegsExcept s u [] := by intro q hq;cases q <;> rfl
  have fu : Frame s u (fun _=>False) := by intro A ha hn;rfl
  obtain ⟨t,st,pt,t6,rt,ft⟩ := expand1Far_steps hc u rfl index credit residual hi hcLt hrLt
    (by simpa [u,expand1Jump.res,rv_simp] using h28) (by simpa [u,expand1Jump.res,rv_simp] using hr)
    (by simpa [u,expand1Jump.res,rv_simp] using hm) (by simpa [u,expand1Jump.res,rv_simp] using hindex)
  exact ⟨t,su.trans st,pt,t6,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
#print axioms expand1_steps
theorem expand2_steps {im : Image} (hc : CodeAt im (pcOf 88072) expand2Code)
    (s : MachineState) (hp : s.pc=pcOf 88072) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (h28 : s.getReg .x28=0x66000#64) (hr : s.getReg .x21=BitVec.ofNat 64 residual)
    (hm : s.getMem 417864#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 46952 ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 2 (index/2^6))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := expand2.res.toState s
  refine ⟨t,symRun_sound expand2 hc s hp (by simp [expand2.res,rv_simp,h28];decide),rfl,?_,?_,?_⟩
  · have hw : lowerWord 2 (BitVec.ofNat 64 index) = BitVec.ofNat 64 (lowerPathSave 2 (index/2^6)) := lower_word 2 index (by decide) hi
    have hg := gated_word residual credit (lowerPathSave 2 (index/2^6)) hrLt hcLt (lowerPathSave_le_one_of 2 (index/2^6) (by decide))
    rw [←hw] at hg
    simp [t,expand2.res,rv_simp,h28,hr]
    rw [hm,hindex]
    simpa [lowerWord] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms expand2_steps
theorem expand3_steps {im : Image} (hc : CodeAt im (pcOf 88084) expand3Code)
    (s : MachineState) (hp : s.pc=pcOf 88084) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (h28 : s.getReg .x28=0x66000#64) (hr : s.getReg .x21=BitVec.ofNat 64 residual)
    (hm : s.getMem 417872#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 46969 ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 3 (index/2^0))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := expand3.res.toState s
  refine ⟨t,symRun_sound expand3 hc s hp (by simp [expand3.res,rv_simp,h28];decide),rfl,?_,?_,?_⟩
  · have hw : lowerWord 3 (BitVec.ofNat 64 index) = BitVec.ofNat 64 (lowerPathSave 3 (index/2^0)) := lower_word 3 index (by decide) hi
    have hg := gated_word residual credit (lowerPathSave 3 (index/2^0)) hrLt hcLt (lowerPathSave_le_one_of 3 (index/2^0) (by decide))
    rw [←hw] at hg
    simp [t,expand3.res,rv_simp,h28,hr]
    rw [hm,hindex]
    simpa [lowerWord] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms expand3_steps
theorem signTopFar_steps {im : Image} (hc : CodeAt im (pcOf 1981) signTopCode)
    (s : MachineState) (hp : s.pc=pcOf 1981) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (hr : s.getReg .x6=BitVec.ofNat 64 residual) (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem 0x66018#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22234 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧ t.getReg .x28=0x66000#64 ∧
      RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := signTop.res.toState s
  refine ⟨t,symRun_sound signTop hc s hp (by simp [signTop.res,rv_simp,h28] <;> decide),rfl,?_,rfl,?_,?_⟩
  · have hw := l1_word index hi
    have hg := gated2_word residual credit (lowerPathSave 1 (index/2^12)) hrLt hcLt
      (lowerPathSave_le_two 1 _)
    rw [←hw] at hg
    simp [t,signTop.res,rv_simp,hr,h28]
    rw [hm,hindex]
    simpa [l1Sel] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms signTopFar_steps
theorem signTop_steps {im : Image} (hj : CodeAt im (pcOf 26019) signTopJumpCode)
    (hc : CodeAt im (pcOf 1981) signTopCode)
    (s : MachineState) (hp : s.pc=pcOf 26019) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (hr : s.getReg .x6=BitVec.ofNat 64 residual) (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem 0x66018#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 19 19 t ∧ t.pc=pcOf 22234 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧ t.getReg .x28=0x66000#64 ∧
      RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let u := signTopJump.res.toState s
  have su : Steps im s 1 1 u := symRun_sound signTopJump hj s hp (by simp [signTopJump.res,rv_simp])
  have ru : RegsExcept s u [] := by intro q hq;cases q <;> rfl
  have fu : Frame s u (fun _=>False) := by intro A ha hn;rfl
  obtain ⟨t,st,pt,t7,t28,rt,ft⟩ := signTopFar_steps hc u rfl index credit residual hi hcLt hrLt
    (by simpa [u,signTopJump.res,rv_simp] using hr) (by simpa [u,signTopJump.res,rv_simp] using h28)
    (by simpa [u,signTopJump.res,rv_simp] using hm) (by simpa [u,signTopJump.res,rv_simp] using hindex)
  exact ⟨t,su.trans st,pt,t7,t28,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
#print axioms signTop_steps
theorem signTwo_steps {im : Image} (hc : CodeAt im (pcOf 26038) signTwoCode)
    (s : MachineState) (hp : s.pc=pcOf 26038) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (hr : s.getReg .x6=BitVec.ofNat 64 residual) (h7 : s.getReg .x7=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 22452 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 2 (index/2^6))) ∧ t.getReg .x28=0x66000#64 ∧
      RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := signTwo.res.toState s
  refine ⟨t,symRun_sound signTwo hc s hp (by simp [signTwo.res,rv_simp] <;> decide),rfl,?_,rfl,?_,?_⟩
  · have hw : lowerWord 2 (BitVec.ofNat 64 index)=BitVec.ofNat 64 (lowerPathSave 2 (index/2^6)) :=
      lower_word 2 index (by decide) hi
    have hg := gated_word residual credit (lowerPathSave 2 (index/2^6)) hrLt hcLt
      (lowerPathSave_le_one_of 2 _ (by decide))
    rw [←hw] at hg
    simp [t,signTwo.res,rv_simp,hr,h7]
    rw [hindex]
    simpa [lowerWord] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms signTwo_steps
theorem signThree_steps {im : Image} (hc : CodeAt im (pcOf 26050) signThreeCode)
    (s : MachineState) (hp : s.pc=pcOf 26050) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (hr : s.getReg .x6=BitVec.ofNat 64 residual) (h7 : s.getReg .x7=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 22452 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 3 (index/2^0))) ∧ t.getReg .x28=0x66000#64 ∧
      RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := signThree.res.toState s
  refine ⟨t,symRun_sound signThree hc s hp (by simp [signThree.res,rv_simp] <;> decide),rfl,?_,rfl,?_,?_⟩
  · have hw : lowerWord 3 (BitVec.ofNat 64 index)=BitVec.ofNat 64 (lowerPathSave 3 (index/2^0)) :=
      lower_word 3 index (by decide) hi
    have hg := gated_word residual credit (lowerPathSave 3 (index/2^0)) hrLt hcLt
      (lowerPathSave_le_one_of 3 _ (by decide))
    rw [←hw] at hg
    simp [t,signThree.res,rv_simp,hr,h7]
    rw [hindex]
    simpa [lowerWord] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms signThree_steps
def dispatchOneCode : List (BitVec 32) := [0x18e3383,0x100193,0x340863]
sym_block dispatchOne := symRun {noAlias:=true} dispatchOneCode (pcOf 26032) 10
def dispatchTwoCode : List (BitVec 32) := [0x200193,0x2340c63]
sym_block dispatchTwo := symRun {noAlias:=true} dispatchTwoCode (pcOf 26035) 10
def dispatchDefaultCode : List (BitVec 32) := [0xffcfc06f]
sym_block dispatchDefault := symRun {noAlias:=true} dispatchDefaultCode (pcOf 26037) 10
theorem dispatchOne_steps {im : Image} (hc : CodeAt im (pcOf 26032) dispatchOneCode)
    (s : MachineState) (hp : s.pc=pcOf 26032) (lay credit : Nat) (hl : lay<4)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h28 : s.getReg .x28=0x66000#64)
    (hm : s.getMem 0x66018#64=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 3 3 t ∧ t.pc=pcOf (if lay=1 then 26038 else 26035) ∧
      t.getReg .x7=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x3,.x7] ∧ Frame s t (fun _=>False) := by
  let t := dispatchOne.res.toState s
  refine ⟨t,symRun_sound dispatchOne hc s hp (by simp [dispatchOne.res,rv_simp,h28] <;> decide),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp [t,dispatchOne.res,rv_simp,h8,pcOf] <;> decide
  · simp [t,dispatchOne.res,rv_simp,h28];exact hm
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms dispatchOne_steps

theorem dispatchTwo_steps {im : Image} (hc : CodeAt im (pcOf 26035) dispatchTwoCode)
    (s : MachineState) (hp : s.pc=pcOf 26035) (lay : Nat) (hl : lay<4)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf (if lay=2 then 26050 else 26037) ∧
      RegsExcept s t [.x3] ∧ Frame s t (fun _=>False) := by
  let t := dispatchTwo.res.toState s
  refine ⟨t,symRun_sound dispatchTwo hc s hp (by simp [dispatchTwo.res,rv_simp]),?_,?_,?_⟩
  · interval_cases lay <;> simp [t,dispatchTwo.res,rv_simp,h8,pcOf] <;> decide
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms dispatchTwo_steps

theorem dispatchDefault_steps {im : Image} (hc : CodeAt im (pcOf 26037) dispatchDefaultCode)
    (s : MachineState) (hp : s.pc=pcOf 26037) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22452 ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  let t := dispatchDefault.res.toState s
  refine ⟨t,symRun_sound dispatchDefault hc s hp (by simp [dispatchDefault.res,rv_simp]),rfl,?_,?_⟩
  · intro r hR;cases r <;> rfl
  · intro A ha hn;rfl
#print axioms dispatchDefault_steps
end LocalRouteMachineHelpers
