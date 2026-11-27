import SigGolfCandidate.MachineCounterCaps
import SigGolfCandidate.Route16Guard
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace SigGolfCandidate.Route16Machine
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9

/-! C39: the root credit pool `75 - topPathSave leaf` and the top floor `max 16 (18 - topPathSave leaf)` are computed
by relocated straight-line blocks (41-word `save_code`) reached by one-word jumps from the old block sites. A symbolic
value that reads a single register is checked on all 4096 leaves through a canonical state (`leaf_value`). -/

/-- `e` reads no memory and no register other than `r`. -/
def onlyReg (r : Reg) : E → Bool
  | .c _ => true
  | .reg r' => decide (r' = r)
  | .ld _ => false
  | .un _ a => onlyReg r a
  | .bin _ a b => onlyReg r a && onlyReg r b
  | .ite _ x y a b => onlyReg r x && onlyReg r y && onlyReg r a && onlyReg r b

theorem eval_congr (r : Reg) (s s' : MachineState) (hs : s.getReg r = s'.getReg r) :
    ∀ e : E, onlyReg r e = true → e.eval s = e.eval s'
  | .c _, _ => rfl
  | .reg r', h => by
    have h' : r' = r := of_decide_eq_true h
    subst h'
    exact hs
  | .ld _, h => by simp [onlyReg] at h
  | .un op a, h => by
    simp only [E.eval]
    rw [eval_congr r s s' hs a h]
  | .bin op a b, h => by
    simp only [onlyReg, Bool.and_eq_true] at h
    simp only [E.eval]
    rw [eval_congr r s s' hs a h.1, eval_congr r s s' hs b h.2]
  | .ite op x y a b, h => by
    simp only [onlyReg, Bool.and_eq_true] at h
    simp only [E.eval]
    rw [eval_congr r s s' hs x h.1.1.1, eval_congr r s s' hs y h.1.1.2, eval_congr r s s' hs a h.1.2,
      eval_congr r s s' hs b h.2]

/-- A canonical state holding `x` in every register. -/
def regState (x : Word) : MachineState := { regs := fun _ => x, mem := fun _ => 0, pc := 0 }

theorem regState_getReg (x : Word) {r : Reg} (h : r ≠ .x0) : (regState x).getReg r = x := by
  cases r <;> first | exact absurd rfl h | rfl

/-- A 4096-leaf check of a single-register symbolic value holds in every state with that register `< 4096`. -/
theorem leaf_value {e : E} {r : Reg} (hr : r ≠ .x0) (he : onlyReg r e = true) {f : Nat → Nat}
    (hchk : ∀ n : Fin 4096, e.eval (regState (BitVec.ofNat 64 n.val)) = BitVec.ofNat 64 (f n.val))
    (s : MachineState) (leaf : Nat) (hl : leaf<4096) (hs : s.getReg r = BitVec.ofNat 64 leaf) :
    e.eval s = BitVec.ofNat 64 (f leaf) := by
  rw [eval_congr r s (regState (BitVec.ofNat 64 leaf)) (by rw [hs, regState_getReg _ hr]) e he]
  exact hchk ⟨leaf, hl⟩

theorem codeAt_split {im : Image} {pc : Word} {a b : List (BitVec 32)} (h : CodeAt im pc (a ++ b)) :
    CodeAt im pc a ∧ CodeAt im (pc + BitVec.ofNat 64 (4 * a.length)) b :=
  ⟨by simpa using CodeAt.drop_prefix (pre := []) (seg := a) (post := b) (by simpa using h),
   CodeAt.drop_prefix (pre := a) (seg := b) (post := []) (by simpa using h)⟩

/-! Sign top-floor guard: `26008: jal 26461`; 26461: `save_code(s2,t4,t5)`, the floor, `lui t5,0x66; ld t5,24(t5);
jal 1959`. -/
def guardCode : List (BitVec 32) := [0x7140006f,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13]
def guardTailCode : List (BitVec 32) :=
  Route16Guard.saveWords ++ Route16Guard.floorWords ++ [0x66f37,0x18f3f03,0x86ce806f]
sym_block guardJump := symRun {noAlias:=true} guardCode (pcOf 26008) 20
sym_block guardBlock := symRun {noAlias:=true} guardTailCode (pcOf 26461) 60
theorem guard_only : onlyReg .x18 (guardBlock.res.st.regs.get .x29) = true := by decide +kernel
theorem guard_checked : ∀ n : Fin 4096, (guardBlock.res.st.regs.get .x29).eval (regState (BitVec.ofNat 64 n.val)) =
    BitVec.ofNat 64 (Route16Guard.floor n.val) := by decide +kernel

theorem guard_steps {im : Image} (hc : CodeAt im (pcOf 26008) guardCode) (ht : CodeAt im (pcOf 26461) guardTailCode)
    (s : MachineState) (hp : s.pc=pcOf 26008) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66018=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 49 49 t ∧ t.pc=pcOf 1959 ∧
      t.getReg .x29=BitVec.ofNat 64 (Route16Guard.floor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let u := guardJump.res.toState s
  have su : Steps im s 1 1 u := symRun_sound guardJump hc s hp (by simp [guardJump.res,rv_simp])
  have ru : RegsExcept s u [] := by intro r hr;cases r <;> rfl
  let t := guardBlock.res.toState u
  have st : Steps im u 48 48 t := symRun_sound guardBlock ht u rfl (by simp [guardBlock.res,rv_simp])
  have rt : RegsExcept u t [.x29,.x30] := by intro r hr;cases r <;> simp at hr <;> rfl
  refine ⟨t,su.trans st,rfl,?_,?_,(ru.trans rt).mono (by simp),?_⟩
  · rw [Result.toState_getReg]
    exact leaf_value (by decide) guard_only guard_checked u leaf hl ((ru.get (by simp)).trans h18)
  · simpa [t,u,guardBlock.res,guardJump.res,rv_simp] using hm
  · intro A ha hn;rfl

/-! Expand top-floor guard: `88095: jal 88480`; 88480: the same words, `lui t5,0x66; ld t5,64(t5); jal 54317`. -/
def expandCode : List (BitVec 32) := [0x6040006f,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13]
def expandTailCode : List (BitVec 32) :=
  Route16Guard.saveWords ++ Route16Guard.floorWords ++ [0x66f37,0x40f3f03,0x979de06f]
sym_block expandJump := symRun {noAlias:=true} expandCode (pcOf 88095) 20
sym_block expandBlock := symRun {noAlias:=true} expandTailCode (pcOf 88480) 60
theorem expand_only : onlyReg .x18 (expandBlock.res.st.regs.get .x29) = true := by decide +kernel
theorem expand_checked : ∀ n : Fin 4096, (expandBlock.res.st.regs.get .x29).eval (regState (BitVec.ofNat 64 n.val)) =
    BitVec.ofNat 64 (Route16Guard.floor n.val) := by decide +kernel

theorem expand_steps {im : Image} (hc : CodeAt im (pcOf 88095) expandCode) (ht : CodeAt im (pcOf 88480) expandTailCode)
    (s : MachineState) (hp : s.pc=pcOf 88095) (leaf credit : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) (hm : s.getMem 0x66040=BitVec.ofNat 64 credit) :
    ∃ t, Steps im s 49 49 t ∧ t.pc=pcOf 54317 ∧
      t.getReg .x29=BitVec.ofNat 64 (Route16Guard.floor leaf) ∧
      t.getReg .x30=BitVec.ofNat 64 credit ∧ RegsExcept s t [.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let u := expandJump.res.toState s
  have su : Steps im s 1 1 u := symRun_sound expandJump hc s hp (by simp [expandJump.res,rv_simp])
  have ru : RegsExcept s u [] := by intro r hr;cases r <;> rfl
  let t := expandBlock.res.toState u
  have st : Steps im u 48 48 t := symRun_sound expandBlock ht u rfl (by simp [expandBlock.res,rv_simp])
  have rt : RegsExcept u t [.x29,.x30] := by intro r hr;cases r <;> simp at hr <;> rfl
  refine ⟨t,su.trans st,rfl,?_,?_,(ru.trans rt).mono (by simp),?_⟩
  · rw [Result.toState_getReg]
    exact leaf_value (by decide) expand_only expand_checked u leaf hl ((ru.get (by simp)).trans h18)
  · simpa [t,u,expandBlock.res,expandJump.res,rv_simp] using hm
  · intro A ha hn;rfl

/-! Sign root pool: `1970: jal 26415`; 26415: `save_code(s2,t1,t3)`, `sub t1,zero,t1; addi t1,t1,75; lui t3,0x66;
sd t1,8(t3); jal 22230`. -/
def signPoolCode : List (BitVec 32) := [0x5f51706f,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13]
def signPoolTailCode : List (BitVec 32) := [0x3f97313,0x7e7f0e37,0xffee0e13,0xbe1e13,0x7ffe0e13,0xbe1e13,0x7ffe0e13,
  0xae1e13,0x3fee0e13,0x6e5e33,0x1e7e13,0x6e1e13,0x1c30333,0x6e37,0x666e0e13,0xbe1e13,0x333e0e13,0xbe1e13,0x199e0e13,
  0xae1e13,0x260e0e13,0x6e5e33,0x1e7e13,0x6e1e13,0x1c30333,0xfc037313,0x695e13,0x3fe7e13,0x1c30333,0x6e66fe37,
  0xeeee0e13,0xbe1e13,0x333e0e13,0xbe1e13,0x3bbe0e13,0xae1e13,0x2eee0e13,0x6e5e33,0x1e7e13,0x635313,0x1c30333,
  0x40600333,0x4b30313,0x66e37,0x6e3423,0xde9fb06f]
sym_block signPoolJump := symRun {noAlias:=true} signPoolCode (pcOf 1970) 20
sym_block signPoolBlock := symRun {noAlias:=true} signPoolTailCode (pcOf 26415) 60
/-- The value stored at `0x66008` by the sign pool block. -/
def signPoolValue : E := match signPoolBlock.res.st.mem with
  | [(_, v)] => v
  | _ => .c 0
theorem signPool_only : onlyReg .x18 signPoolValue = true := by decide +kernel
theorem signPool_checked : ∀ n : Fin 4096, signPoolValue.eval (regState (BitVec.ofNat 64 n.val)) =
    BitVec.ofNat 64 (75-CanonicalPolicy.topPathSave n.val) := by decide +kernel

theorem signPool_steps {im : Image} (hc : CodeAt im (pcOf 1970) signPoolCode)
    (ht : CodeAt im (pcOf 26415) signPoolTailCode)
    (s : MachineState) (hp : s.pc=pcOf 1970) (leaf : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 47 47 t ∧ t.pc=pcOf 22230 ∧
      t.getMem 0x66008=BitVec.ofNat 64 (75-CanonicalPolicy.topPathSave leaf) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A=>A=0x66008) := by
  let u := signPoolJump.res.toState s
  have su : Steps im s 1 1 u := symRun_sound signPoolJump hc s hp (by simp [signPoolJump.res,rv_simp])
  have ru : RegsExcept s u [] := by intro r hr;cases r <;> rfl
  let t := signPoolBlock.res.toState u
  have st : Steps im u 46 46 t := symRun_sound signPoolBlock ht u rfl (by simp [signPoolBlock.res,rv_simp])
  have rt : RegsExcept u t [.x6,.x28] := by intro r hr;cases r <;> simp at hr <;> rfl
  refine ⟨t,su.trans st,rfl,?_,(ru.trans rt).mono (by simp),?_⟩
  · have hv : t.getMem 0x66008 = signPoolValue.eval u := rfl
    rw [hv]
    exact leaf_value (f:=fun n=>75-CanonicalPolicy.topPathSave n) (by decide) signPool_only signPool_checked
      u leaf hl ((ru.get (by simp)).trans h18)
  · intro A ha hn
    have hA : BitVec.ofNat 64 A ≠ 0x66008#64 := by
      intro h
      apply hn
      have h' := congrArg BitVec.toNat h
      have ha' : A<18446744073709551616 := ha
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha'] at h'
      exact h'
    show (signPoolBlock.res.toState u).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
    rw [Result.toState_getMem_frame _ _ _ (by
      intro p hp
      simp only [signPoolBlock.res,List.mem_cons,List.not_mem_nil,or_false] at hp
      subst hp
      exact hA)]
    rfl

/-! Expand root pool: `54324: jal 88400`; 88400: `lui t3,0x20; ld t3,1360(t3); srli t3,t3,19` (the root leaf
`index/2^19`), `save_code(t3,s5,s4)`, `sub s5,zero,s5; addi s5,s5,75; lui t3,0x66; ld s4,0(t3); jal 46933`. -/
def expandPoolCode : List (BitVec 32) := [0x4702106f,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13]
def expandLeafCode : List (BitVec 32) := [0x20e37,0x550e3e03,0x13e5e13]
def expandPoolBodyCode : List (BitVec 32) := [0x3fe7a93,0x7e7f0a37,0xffea0a13,0xba1a13,0x7ffa0a13,0xba1a13,
  0x7ffa0a13,0xaa1a13,0x3fea0a13,0x15a5a33,0x1a7a13,0x6a1a13,0x14a8ab3,0x6a37,0x666a0a13,0xba1a13,0x333a0a13,
  0xba1a13,0x199a0a13,0xaa1a13,0x260a0a13,0x15a5a33,0x1a7a13,0x6a1a13,0x14a8ab3,0xfc0afa93,0x6e5a13,0x3fa7a13,
  0x14a8ab3,0x6e66fa37,0xeeea0a13,0xba1a13,0x333a0a13,0xba1a13,0x3bba0a13,0xaa1a13,0x2eea0a13,0x15a5a33,0x1a7a13,
  0x6ada93,0x14a8ab3,0x41500ab3,0x4ba8a93,0x66e37,0xe3a03,0xf54d706f]
def expandPoolTailCode : List (BitVec 32) := expandLeafCode ++ expandPoolBodyCode
sym_block expandPoolJump := symRun {noAlias:=true} expandPoolCode (pcOf 54324) 20
sym_block expandLeaf := symRun {noAlias:=true} expandLeafCode (pcOf 88400) 10
sym_block expandPoolBlock := symRun {noAlias:=true} expandPoolBodyCode (pcOf 88403) 60
theorem expandPool_only : onlyReg .x28 (expandPoolBlock.res.st.regs.get .x21) = true := by decide +kernel
theorem expandPool_checked : ∀ n : Fin 4096,
    (expandPoolBlock.res.st.regs.get .x21).eval (regState (BitVec.ofNat 64 n.val)) =
      BitVec.ofNat 64 (75-CanonicalPolicy.topPathSave n.val) := by decide +kernel
theorem root_word (index : Nat) (hi : index<2^31) :
    BitVec.ofNat 64 index >>> 19 = BitVec.ofNat 64 (index/2^19) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show index<2^64 by omega),Nat.mod_eq_of_lt (show index/2^19<2^64 by omega)]

theorem expandPool_steps {im : Image} (hc : CodeAt im (pcOf 54324) expandPoolCode)
    (ht : CodeAt im (pcOf 88400) expandPoolTailCode)
    (s : MachineState) (hp : s.pc=pcOf 54324) (index H : Nat) (hi : index<2^31)
    (hmidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hm : s.getMem 0x66000=BitVec.ofNat 64 H) :
    ∃ t, Steps im s 50 50 t ∧ t.pc=pcOf 46933 ∧
      t.getReg .x21=BitVec.ofNat 64 (75-CanonicalPolicy.topPathSave (index/2^19)) ∧
      t.getReg .x20=BitVec.ofNat 64 H ∧ RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hl,hb⟩ := codeAt_split ht
  have hb' : CodeAt im (pcOf 88403) expandPoolBodyCode := hb
  let u := expandPoolJump.res.toState s
  have su : Steps im s 1 1 u := symRun_sound expandPoolJump hc s hp (by simp [expandPoolJump.res,rv_simp])
  have ru : RegsExcept s u [] := by intro r hr;cases r <;> rfl
  let v := expandLeaf.res.toState u
  have sv : Steps im u 3 3 v := symRun_sound expandLeaf hl u rfl (by simp [expandLeaf.res,rv_simp])
  have rv : RegsExcept u v [.x28] := by intro r hr;cases r <;> simp at hr <;> rfl
  let t := expandPoolBlock.res.toState v
  have st : Steps im v 46 46 t := symRun_sound expandPoolBlock hb' v rfl (by simp [expandPoolBlock.res,rv_simp])
  have rt : RegsExcept v t [.x20,.x21,.x28] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hv28 : v.getReg .x28 = BitVec.ofNat 64 (index/2^19) := by
    have hmu : u.getMem 132432#64 = BitVec.ofNat 64 index := hmidx
    simp only [v,Result.toState_getReg,expandLeaf.res,rv_simp]
    rw [hmu]
    show BitVec.ofNat 64 index >>> 19 = _
    exact root_word index hi
  refine ⟨t,(su.trans sv).trans st,rfl,?_,?_,((ru.trans rv).trans rt).mono (by simp),?_⟩
  · rw [Result.toState_getReg]
    exact leaf_value (f:=fun n=>75-CanonicalPolicy.topPathSave n) (by decide) expandPool_only expandPool_checked
      v (index/2^19) (by omega) hv28
  · simpa [t,v,u,expandPoolBlock.res,expandLeaf.res,expandPoolJump.res,rv_simp] using hm
  · intro A ha hn;rfl

#print axioms guard_steps
#print axioms expand_steps
#print axioms signPool_steps
#print axioms expandPool_steps
end SigGolfCandidate.Route16Machine
