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
def poolForLeaf (leaf : Nat) : Nat  := 75-ClaudeWCT.WCT9.CanonicalPolicy.topPathSave leaf
def rootFloor (leaf : Nat) : Nat := max 16 (poolForLeaf leaf-57)
theorem rootFloor_eq (leaf : Nat) : rootFloor leaf = SigGolfCandidate.Route16Guard.floor leaf := by
  rw [SigGolfCandidate.Route16Guard.floor_eq_threshold]
  rfl
abbrev guardCode := SigGolfCandidate.Route16Machine.guardCode
abbrev guardTailCode := SigGolfCandidate.Route16Machine.guardTailCode
abbrev expandRootCode := SigGolfCandidate.Route16Machine.expandCode
abbrev expandRootTailCode := SigGolfCandidate.Route16Machine.expandTailCode
/-- C39: the sign top-floor guard: the jump at 26008 and the relocated block at 26461. -/
def GuardAt (im : Image) : Prop := CodeAt im (pcOf 26008) guardCode ∧ CodeAt im (pcOf 26461) guardTailCode
/-- C39: the expand top-floor guard: the jump at 88095 and the relocated block at 88480. -/
def ExpandRootAt (im : Image) : Prop :=
  CodeAt im (pcOf 88095) expandRootCode ∧ CodeAt im (pcOf 88480) expandRootTailCode
theorem guard_steps {im : Image} (hc : GuardAt im)
    (s : MachineState) (hp : s.pc=pcOf 26008) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66018=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 49 49 t ∧ t.pc=pcOf 1959 ∧
      t.getReg .x29=BitVec.ofNat 64 (rootFloor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  simpa only [rootFloor_eq] using SigGolfCandidate.Route16Machine.guard_steps hc.1 hc.2 s hp leaf credit hl h18 hm
theorem expandRoot_steps {im : Image} (hc : ExpandRootAt im)
    (s : MachineState) (hp : s.pc=pcOf 88095) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66040=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 49 49 t ∧ t.pc=pcOf 54317 ∧
      t.getReg .x29=BitVec.ofNat 64 (rootFloor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  simpa only [rootFloor_eq] using SigGolfCandidate.Route16Machine.expand_steps hc.1 hc.2 s hp leaf credit hl h18 hm
/-- C38: the relocated layer-1 credit block (expand 88106): `x = (index >>> 12) & 127`, `d = (x ^ x >>> 1) & 63`,
save `[d ≠ 0] + ([d ≥ 4] & d)` (0, 1 or 2), added to the credit when `credit < residual` (mask `-(c < r)`). -/
def expand1Code : List (BitVec 32) := [0x40e3303,0x20e37,0x550e3383,0xc3d393,0x7f3f393,0x13de13,0x1c3c3b3,0x3f3f393,0x43be13,0x1e4e13,0x7e7e33,0x7033b3,0x1c383b3,0x1533e33,0x41c00e33,0x1c3f3b3,0x730333,0xc75d706f]
sym_block expand1 := symRun {noAlias:=true} expand1Code (pcOf 88106) 40
theorem expand1_counts : expand1.res.steps=18 ∧ expand1.res.cycles=18 := by decide +kernel
def expand2Code : List (BitVec 32) := [0x48e3303,0x20e37,0x550e3383,0x63d393,0x33f393,0x13de13,0x1c3c3b3,0x13f393,0x1533e33,0x1c3f3b3,0x730333,0xd55d706f]
sym_block expand2 := symRun {noAlias:=true} expand2Code (pcOf 88072) 30
theorem expand2_counts : expand2.res.steps=12 ∧ expand2.res.cycles=12 := by decide +kernel
def expand3Code : List (BitVec 32) := [0x50e3303,0x20e37,0x550e3383,0x33f393,0x13de13,0x1c3c3b3,0x13f393,0x1533e33,0x1c3f3b3,0x730333,0xd6dd706f]
sym_block expand3 := symRun {noAlias:=true} expand3Code (pcOf 88084) 30
theorem expand3_counts : expand3.res.steps=11 ∧ expand3.res.cycles=11 := by decide +kernel
/-- C38: the relocated sign layer-1 credit block (sign 1981), the same computation with `gp` as scratch. -/
def signTopCode : List (BitVec 32) := [0x18e3383,0x20e37,0x550e3e03,0xce5e13,0x7fe7e13,0x1e5193,0x3e4e33,0x3fe7e13,0x4e3193,0x11c193,0x1c1f1b3,0x1c03e33,0x3e0e33,0x63b1b3,0x403001b3,0x3e7e33,0x1c383b3,0x66e37,0x42d1306f]
sym_block signTop := symRun {noAlias:=true} signTopCode (pcOf 1981) 40
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
/-- C38: the layer-1 save word computed by the relocated blocks from the masked 7-bit leaf `x`. -/
def l1Tail (x : Word) : Word :=
  let d := (x ^^^ (x >>> 1)) &&& 63#64
  (if (0#64).ult d then 1#64 else 0#64) + (((if d.ult 4#64 then 1#64 else 0#64) ^^^ 1#64) &&& d)
def l1Word (w : Word) : Word := l1Tail ((w >>> 12) &&& 127#64)
theorem l1Tail_checked : ∀ x : Fin 128, l1Tail (BitVec.ofNat 64 x.val) = BitVec.ofNat 64 (lowerPathSave 1 x.val) := by
  decide +kernel
theorem l1_word (n : Nat) (hn : n<2^64) :
    l1Word (BitVec.ofNat 64 n) = BitVec.ofNat 64 (lowerPathSave 1 (n/2^12)) := by
  have h7 := extract_word n 12 7 hn (by decide)
  simp only [show (2:Nat)^7-1=127 from rfl] at h7
  unfold l1Word
  rw [h7, lowerPathSave_mod128 1 (n/2^12) (n/2^12%128) (by omega)]
  exact l1Tail_checked ⟨n/2^12%128, Nat.mod_lt _ (by decide)⟩
#print axioms l1_word
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
/-- C38: the masked gate `c + (saved & -(c < r))` for a save of at most 2. -/
theorem gated_word2 (r c saved : Nat) (hr : r<2^64) (hc : c<2^64) (hs : saved≤2) :
    BitVec.ofNat 64 c + (BitVec.ofNat 64 saved &&&
      (0#64 - (if (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 r) then 1#64 else 0#64))) =
    BitVec.ofNat 64 (guardedCredit r c saved) := by
  have hu : (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 r) = decide (c<r) := by
    simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hr]
  rw [hu]
  have hcS : saved=0 ∨ saved=1 ∨ saved=2 := by omega
  rcases hcS with rfl | rfl | rfl <;> by_cases h : c<r <;>
    simp [h,guardedCredit,BitVec.ofNat_add]
#print axioms gated_word2
theorem expand1_steps {im : Image} (hc : CodeAt im (pcOf 88106) expand1Code)
    (s : MachineState) (hp : s.pc=pcOf 88106) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (h28 : s.getReg .x28=0x66000#64) (hr : s.getReg .x21=BitVec.ofNat 64 residual)
    (hm : s.getMem 417856#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 46936 ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := expand1.res.toState s
  refine ⟨t,symRun_sound expand1 hc s hp (by simp [expand1.res,rv_simp,h28];decide),rfl,?_,?_,?_⟩
  · have hw : l1Word (BitVec.ofNat 64 index) = BitVec.ofNat 64 (lowerPathSave 1 (index/2^12)) := l1_word index hi
    have hg := gated_word2 residual credit (lowerPathSave 1 (index/2^12)) hrLt hcLt (lowerPathSave_le_two 1 (index/2^12))
    rw [←hw] at hg
    simp [t,expand1.res,rv_simp,h28,hr]
    rw [hm,hindex]
    simpa [l1Word,l1Tail] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
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
    have hg := gated_word residual credit (lowerPathSave 2 (index/2^6)) hrLt hcLt (lowerPathSave_le_one 2 (index/2^6))
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
    have hg := gated_word residual credit (lowerPathSave 3 (index/2^0)) hrLt hcLt (lowerPathSave_le_one 3 (index/2^0))
    rw [←hw] at hg
    simp [t,expand3.res,rv_simp,h28,hr]
    rw [hm,hindex]
    simpa [lowerWord] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
#print axioms expand3_steps
theorem signTop_steps {im : Image} (hc : CodeAt im (pcOf 1981) signTopCode)
    (s : MachineState) (hp : s.pc=pcOf 1981) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (hr : s.getReg .x6=BitVec.ofNat 64 residual) (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem 0x66018#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 19 19 t ∧ t.pc=pcOf 22234 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧ t.getReg .x28=0x66000#64 ∧
      RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := signTop.res.toState s
  refine ⟨t,symRun_sound signTop hc s hp (by simp [signTop.res,rv_simp,h28] <;> decide),rfl,?_,rfl,?_,?_⟩
  · have hw : l1Word (BitVec.ofNat 64 index)=BitVec.ofNat 64 (lowerPathSave 1 (index/2^12)) :=
      l1_word index hi
    have hg := gated_word2 residual credit (lowerPathSave 1 (index/2^12)) hrLt hcLt
      (lowerPathSave_le_two 1 _)
    rw [←hw] at hg
    simp [t,signTop.res,rv_simp,hr,h28]
    rw [hm,hindex]
    simpa [l1Word,l1Tail] using hg
  · intro r hR;cases r <;> simp at hR <;> rfl
  · intro A ha hn;rfl
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
      (lowerPathSave_le_one 2 _)
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
      (lowerPathSave_le_one 3 _)
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
