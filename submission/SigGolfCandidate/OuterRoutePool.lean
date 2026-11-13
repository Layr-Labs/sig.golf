import SigGolfCandidate.OuterSigning
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
namespace OuterRoutePool
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option Elab.async false
def poolWord (n : Nat) : Word :=
  let d := (BitVec.ofNat 64 n >>> 1) ^^^ BitVec.ofNat 64 n
  73#64 - ((d &&& 1#64) + ((d >>> 6) &&& 1#64))
theorem pool_checked : ∀ n : Fin 4096, poolWord n.val = BitVec.ofNat 64 (OuterSigning.rootPool n.val) := by decide +kernel
def signCode : List (BitVec 32) := [0x195313,0x1234333,0x137e13,0x635313,0x137313,0x1c30333,0x40600333,0x4930313,0x66e37,0x6e3423,0x4691306f]
sym_block sign := symRun {noAlias:=true} signCode (pcOf 1970) 12
theorem sign_steps {im : Image} (hc : CodeAt im (pcOf 1970) signCode)
    (s : MachineState) (hp : s.pc=pcOf 1970) (leaf : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 11 11 t ∧ t.pc=pcOf 22230 ∧
      t.getMem 0x66008=BitVec.ofNat 64 (OuterSigning.rootPool leaf) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A=>A=0x66008) := by
  let t := sign.res.toState s
  refine ⟨t, symRun_sound sign hc s hp (by simp [sign.res,rv_simp]), rfl, ?_, ?_, ?_⟩
  · simpa [t,sign.res,rv_simp,poolWord,h18,BitVec.sub_eq_add_neg,BitVec.neg_add,
      BitVec.add_assoc,BitVec.add_comm] using pool_checked ⟨leaf,hl⟩
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn
    dsimp only [t]
    simp only [Result.toState_getMem,sign.res]; t3n []
    change A ≠ 417800 at hn
    norm_num at ha
    rw [Nat.mod_eq_of_lt ha, if_neg hn]
def expandIndexCode : List (BitVec 32) := [0x20e37,0x550e3a83,0x13ada93,0x1ada13,0x15a4ab3,0x1afa13,0x6ada93,0x1afa93,0x14a8ab3,0x41500ab3,0x49a8a93,0x66e37,0xe3a03,0xc51f806f]
sym_block expandIndex := symRun {noAlias:=true} expandIndexCode (pcOf 54324) 20
theorem root_word (index : Nat) (hi : index<2^31) :
    BitVec.ofNat 64 index >>> 19 = BitVec.ofNat 64 (index/2^19) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show index<2^64 by omega),Nat.mod_eq_of_lt (show index/2^19<2^64 by omega)]
theorem expandIndex_steps {im : Image} (hc : CodeAt im (pcOf 54324) expandIndexCode)
    (s : MachineState) (hp : s.pc=pcOf 54324) (index H : Nat) (hi : index<2^31)
    (hmidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hm : s.getMem 0x66000=BitVec.ofNat 64 H) :
    ∃ t, Steps im s 14 14 t ∧ t.pc=pcOf 46933 ∧
      t.getReg .x21=BitVec.ofNat 64 (OuterSigning.rootPool (index/2^19)) ∧
      t.getReg .x20=BitVec.ofNat 64 H ∧ RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  let t := expandIndex.res.toState s
  refine ⟨t,symRun_sound expandIndex hc s hp (by simp [expandIndex.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · have hh : index/2^19<4096 := by omega
    have hs (x : Word) : x >>> 20 = (x >>> 19) >>> 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
      omega
    dsimp only [t]
    simp only [Result.toState_getReg,expandIndex.res,rv_simp]
    have haddr : s.getMem (132432#64) = BitVec.ofNat 64 index := hmidx
    rw [haddr]
    simp only [BitVec.toNat_ofNat,Nat.reduceMod]
    rw [root_word index hi]
    simpa [poolWord,BitVec.xor_comm,BitVec.sub_eq_add_neg,BitVec.neg_add,
      BitVec.add_assoc,BitVec.add_comm] using pool_checked ⟨index/2^19,hh⟩
  · simpa [t,expandIndex.res,rv_simp] using hm
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn; rfl
end OuterRoutePool
#print axioms OuterRoutePool.sign_steps
#print axioms OuterRoutePool.expandIndex_steps
