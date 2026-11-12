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
def rootFloor (leaf : Nat) : Nat := max 18 (poolForLeaf leaf-57)
theorem rootFloor_eq (leaf : Nat) : rootFloor leaf=18 := by
  unfold rootFloor poolForLeaf
  omega
def guardCode : List (BitVec 32) := [0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x1200e93,0x66f37,0x18f3f03,0x815e806f]
sym_block rootGuardBlock := symRun {noAlias:=true} guardCode (pcOf 26008) 20
def guardWord (_ : Nat) : Word := 18#64
theorem guard_checked : ∀ n : Fin 4096, guardWord n.val =
    BitVec.ofNat 64 (18) := by decide +kernel
theorem guard_steps {im : Image} (hc : CodeAt im (pcOf 26008) guardCode)
    (s : MachineState) (hp : s.pc=pcOf 26008) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66018=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 1959 ∧
      t.getReg .x29=BitVec.ofNat 64 (18) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let t := rootGuardBlock.res.toState s
  refine ⟨t,symRun_sound rootGuardBlock hc s hp (by simp [rootGuardBlock.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · simpa [t,rootGuardBlock.res,rv_simp,guardWord,h18,BitVec.sub_eq_add_neg,BitVec.neg_add,
      BitVec.add_assoc,BitVec.add_comm] using guard_checked ⟨leaf,hl⟩
  · simpa [t,rootGuardBlock.res,rv_simp] using hm
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
#print axioms guard_steps
def expandRootCode : List (BitVec 32) := [0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x1200e93,0x66f37,0x40f3f03,0x810df06f]
sym_block expandRoot := symRun {noAlias:=true} expandRootCode (pcOf 88095) 20
theorem expandRoot_steps {im : Image} (hc : CodeAt im (pcOf 88095) expandRootCode)
    (s : MachineState) (hp : s.pc=pcOf 88095) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66040=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 54317 ∧
      t.getReg .x29=BitVec.ofNat 64 (18) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let t := expandRoot.res.toState s
  refine ⟨t,symRun_sound expandRoot hc s hp (by simp [expandRoot.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · simpa [t,expandRoot.res,rv_simp,guardWord,h18,BitVec.sub_eq_add_neg,BitVec.neg_add,
      BitVec.add_assoc,BitVec.add_comm] using guard_checked ⟨leaf,hl⟩
  · simpa [t,expandRoot.res,rv_simp] using hm
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
#print axioms expandRoot_steps
def expand1Code : List (BitVec 32) := [0x40e3303,0x20e37,0x550e3383,0xc3d393,0x73f393,0x2e00e13,0x7e53b3,0x13f393,0x1533e33,0x1c3f3b3,0x730333,0xd45d706f]
sym_block expand1 := symRun {noAlias:=true} expand1Code (pcOf 88060) 30
theorem expand1_counts : expand1.res.steps=12 ∧ expand1.res.cycles=12 := by decide +kernel
def expand2Code : List (BitVec 32) := [0x48e3303,0x20e37,0x550e3383,0x63d393,0x33f393,0x13de13,0x1c3c3b3,0x13f393,0x1533e33,0x1c3f3b3,0x730333,0xd55d706f]
sym_block expand2 := symRun {noAlias:=true} expand2Code (pcOf 88072) 30
theorem expand2_counts : expand2.res.steps=12 ∧ expand2.res.cycles=12 := by decide +kernel
def expand3Code : List (BitVec 32) := [0x50e3303,0x20e37,0x550e3383,0x33f393,0x13de13,0x1c3c3b3,0x13f393,0x1533e33,0x1c3f3b3,0x730333,0xd6dd706f]
sym_block expand3 := symRun {noAlias:=true} expand3Code (pcOf 88084) 30
theorem expand3_counts : expand3.res.steps=11 ∧ expand3.res.cycles=11 := by decide +kernel
def signTopCode : List (BitVec 32) := [0x18e3383,0x20e37,0x550e3e03,0xce5e13,0x7e7e13,0x2e00193,0x1c1de33,0x1e7e13,0x63b1b3,0x3e7e33,0x1c383b3,0x66e37,0xcacfc06f]
sym_block signTop := symRun {noAlias:=true} signTopCode (pcOf 26019) 30
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

theorem lower_word (lay n : Nat) (hl : 1≤lay ∧ lay≤3) (hn : n<2^64) :
    lowerWord lay (BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (lowerPathSave lay (n/2^(if lay=1 then 12 else if lay=2 then 6 else 0))) := by
  have h7 := extract_word n 12 3 hn (by decide)
  have h3a := extract_word n 6 2 hn (by decide)
  have h3b := extract_word n 0 2 hn (by decide)
  have hcases : lay=1 ∨ lay=2 ∨ lay=3 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp only [lowerWord,ite_true,show (2:Nat)^3-1=7 from rfl] at h7 ⊢
    rw [h7]
    generalize hx : n/2^12%8=x
    have hxlt : x<8 := by rw [←hx];omega
    interval_cases x <;> simp_all [lowerPathSave] <;> decide
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
theorem expand1_steps {im : Image} (hc : CodeAt im (pcOf 88060) expand1Code)
    (s : MachineState) (hp : s.pc=pcOf 88060) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (h28 : s.getReg .x28=0x66000#64) (hr : s.getReg .x21=BitVec.ofNat 64 residual)
    (hm : s.getMem 417856#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 46936 ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := expand1.res.toState s
  refine ⟨t,symRun_sound expand1 hc s hp (by simp [expand1.res,rv_simp,h28];decide),rfl,?_,?_,?_⟩
  · have hw : lowerWord 1 (BitVec.ofNat 64 index) = BitVec.ofNat 64 (lowerPathSave 1 (index/2^12)) := lower_word 1 index (by decide) hi
    have hg := gated_word residual credit (lowerPathSave 1 (index/2^12)) hrLt hcLt (lowerPathSave_le_one 1 (index/2^12))
    rw [←hw] at hg
    simp [t,expand1.res,rv_simp,h28,hr]
    rw [hm,hindex]
    simpa [lowerWord] using hg
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
theorem signTop_steps {im : Image} (hc : CodeAt im (pcOf 26019) signTopCode)
    (s : MachineState) (hp : s.pc=pcOf 26019) (index credit residual : Nat)
    (hi : index<2^64) (hcLt : credit<2^64) (hrLt : residual<2^64)
    (hr : s.getReg .x6=BitVec.ofNat 64 residual) (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem 0x66018#64=BitVec.ofNat 64 credit)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 22234 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit residual credit
        (lowerPathSave 1 (index/2^12))) ∧ t.getReg .x28=0x66000#64 ∧
      RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let t := signTop.res.toState s
  refine ⟨t,symRun_sound signTop hc s hp (by simp [signTop.res,rv_simp,h28] <;> decide),rfl,?_,rfl,?_,?_⟩
  · have hw : lowerWord 1 (BitVec.ofNat 64 index)=BitVec.ofNat 64 (lowerPathSave 1 (index/2^12)) :=
      lower_word 1 index (by decide) hi
    have hg := gated_word residual credit (lowerPathSave 1 (index/2^12)) hrLt hcLt
      (lowerPathSave_le_one 1 _)
    rw [←hw] at hg
    simp [t,signTop.res,rv_simp,hr,h28]
    rw [hm,hindex]
    simpa [lowerWord] using hg
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
