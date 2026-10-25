import SigGolfCandidate.T3M_Search_TopSegments
import SigGolfCandidate.T3M_Search_TopWindow

section
namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def Writes (A : Nat) : Prop := DIGITS ≤ A ∧ A < DIGITS+64
abbrev Changed : List Reg := [.x6,.x7,.x20,.x21,.x28,.x29,.x30]
theorem read_wu_byte (s : MachineState) (A k : Nat) (hA : A+8 < 2^64)
    (hal : A%4=0) (hk : k<4) :
    (LoadKind.wu.read s (BitVec.ofNat 64 A) >>> (8*k)).truncate 8 =
      s.getByte (BitVec.ofNat 64 (A+k)) := by
  rw [LoadKind.read_sub _ _ _ (by decide),byteOffset_eq,toNat_ofNat_lt (by omega),
    getByte_eq_word _ _ (by omega)]
  have he : alignToDword (BitVec.ofNat 64 A)=BitVec.ofNat 64 ((A+k)/8*8) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat,toNat_ofNat_lt (by omega),toNat_ofNat_lt (by omega)]
    omega
  rw [he]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [LoadKind.fromWord,extractWord32,extractByte,BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight]
  have h1 : 8*k+i<32 := by omega
  have h2 : A%8/4*32+(8*k+i)=(A+k)%8*8+i := by omega
  simp only [hi,h1,show 8*k+i<64 by omega,decide_true,Bool.true_and,h2]
theorem table_rank_byte (s : MachineState) (ht : TableOK s) (r k : Nat)
    (hr : r<125) (hk : k<3) :
    s.getByte (BitVec.ofNat 64 (TOP_DATA+128+4*r+k))=BitVec.ofNat 8 (rankDigit r k) := by
  have h := ht (128+4*r+k) (by omega)
  have he : TOP_DATA+(128+4*r+k)=TOP_DATA+128+4*r+k := by omega
  rw [he] at h
  rw [h]
  unfold tableByte
  simp only [show ¬128+4*r+k<128 by omega,if_false,show 128+4*r+k<628 by omega,if_true]
  have h1 : (128+4*r+k-128)%4=k := by omega
  have h2 : (128+4*r+k-128)/4=r := by omega
  rw [h1,h2,if_pos hk]
theorem load_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+369)) (r : Nat) (hr : r<125)
    (h28 : s.getReg .x28=BitVec.ofNat 64 (TOP_DATA+128+4*r)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+370) ∧
      t.getReg .x29=LoadKind.wu.read s (BitVec.ofNat 64 (TOP_DATA+128+4*r)) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hd : decodeInstruction (0x000e6e83 : BitVec 32)=some (.base (.LWU .x29 .x28 0)) := rfl
  have hf := ((codeAt_top369 hK).fetch s hpc).trans hd
  have hv : accessValid (s.getReg .x28+0) 4=true := by
    rw [h28]; simp only [add_zero,accessValid_iff,MEMORY_BYTES]
    norm_num [TOP_DATA]
    omega
  have hs : ordinaryStep s (.base (.LWU .x29 .x28 0))=
      some ((s.setReg .x29 (LoadKind.wu.read s (BitVec.ofNat 64 (TOP_DATA+128+4*r)))).setPC (s.pc+4)) := by
    rw [classify_sound (show classify (.base (.LWU .x29 .x28 0))=some (.load .wu .x29 .x28 0) from rfl)]
    simp only [Micro.exec,LoadKind.width,show accessValid (s.getReg .x28+0) 4=true from hv,if_true]
    rw [h28,add_zero]
  refine ⟨_,Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl rfl,?_,?_,?_,?_⟩
  · change s.pc+4=pcOf (b+370)
    rw [hpc,pcOf_add4]
  · change (s.setReg .x29 _).getReg .x29=_
    exact MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ Reg.x0)
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; rfl
theorem store_spec {image : Image} (s : MachineState) (pc : Word) (inst : BitVec 32)
    (rs : Reg) (off : BitVec 12) (A : Nat) (value : BitVec 8)
    (hc : CodeAt image pc [inst]) (hpc : s.pc=pc)
    (hd : decodeInstruction inst=some (.base (.SB .x21 rs off)))
    (ha : s.getReg .x21+signExtend12 off=BitVec.ofNat 64 A)
    (hv : (s.getReg rs).truncate 8=value) (hA : DIGITS ≤ A ∧ A<DIGITS+54) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pc+4 ∧
      (∀ B, B<2^64 → t.getByte (BitVec.ofNat 64 B)=
        if B=A then value else s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [] ∧ Frame s t Writes := by
  have hAb : A<2^64 := by unfold DIGITS at hA;omega
  have haccess : accessValid (s.getReg .x21+signExtend12 off) 1=true := by
    rw [ha]
    simp only [accessValid_iff,MEMORY_BYTES,toNat_ofNat_lt hAb,Nat.mod_one,and_true,true_and]
    unfold DIGITS at hA
    omega
  have hs := steps_sb hc hpc hd haccess
  rw [ha,hv] at hs
  refine ⟨_,hs,congrArg (fun p => p+4) hpc,?_,?_,?_⟩
  · intro B hB
    simp only [getByte_setPC,getByte_setByte s A B hAb hB]
  · intro q _; simp only [getReg_setPC',getReg_setByte]
  · intro B hB hn
    simp only [getMem_setPC']
    apply getMem_setByte s A B hAb hB value
    unfold Writes at hn
    unfold DIGITS at hn hA
    omega
theorem pair_shift (X : Nat) :
    (BitVec.ofNat 64 X >>> 7 ||| BitVec.ofNat 64 (X/2^64) <<< 57)=
      BitVec.ofNat 64 (X/2^7) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat,Nat.testBit_div_two_pow,hi,decide_true,Bool.true_and]
  by_cases h : 7+i<64
  · simp only [h,decide_true,Bool.true_and,show i<57 by omega,decide_true,Bool.not_true,
      Bool.false_and,Bool.or_false]
    congr 1
    omega
  · simp only [h,decide_false,Bool.false_and,Bool.false_or,show ¬i<57 by omega,decide_false,
      Bool.not_false,Bool.true_and,show i-57<64 by omega,decide_true]
    congr 1
    omega
end SigGolfCandidate.T3M.Search.TopUnpack
end
section
namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def jumpCode (b : Nat) : List (BitVec 32) := if b=354 then [0x2312906f] else [0x7591306f]
def initCode : List (BitVec 32) := [133815,0x420a8a93,0x80f0f13]
def ptrCode : List (BitVec 32) := [0x7f37e13,3022355,32378419]
def initLayout (b : Nat) : Rv.Layout := [(0,jumpCode b),(1,initCode),(4,ptrCode)]
theorem initLayout_ok (b : Nat) : layoutOk 0 (initLayout b)=true := by
  by_cases hb : b=354 <;> simp [initLayout,jumpCode,hb] <;> decide +kernel
theorem initLayout_code (b : Nat) : topSeg362 b=layoutCode (initLayout b) := by
  by_cases hb : b=354 <;> simp [topSeg362,initLayout,jumpCode,hb] <;> decide +kernel
theorem code_jump {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (b+362)) (jumpCode b) := by
  have hc := codeAt_top362 hK
  rw [initLayout_code] at hc
  have h := codeAt_sublayout hc (initLayout_ok b) (i:=0) (o:=0) (seg:=jumpCode b) (by rfl)
  simpa only [Nat.add_zero] using h
theorem code_init {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (b+363)) initCode := by
  have hc := codeAt_top362 hK
  rw [initLayout_code] at hc
  have h := codeAt_sublayout hc (initLayout_ok b) (i:=1) (o:=1) (seg:=initCode) (by rfl)
  simpa only [Nat.add_assoc,Nat.reduceAdd] using h
theorem code_ptr {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (b+366)) ptrCode := by
  have hc := codeAt_top362 hK
  rw [initLayout_code] at hc
  have h := codeAt_sublayout hc (initLayout_ok b) (i:=2) (o:=4) (seg:=ptrCode) (by rfl)
  simpa only [Nat.add_assoc,Nat.reduceAdd] using h
sym_block uj354 := symRun {noAlias:=true} (jumpCode 354) (pcOf (354+362)) 200
sym_block uj543 := symRun {noAlias:=true} (jumpCode 543) (pcOf (543+362)) 200
def jumpState : SymState := uj354.res.st
theorem run_jump {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (jumpCode b) (pcOf (b+362)) 200=
      some ⟨jumpState,.c (pcOf (Reward.base b true)),uj354.res.stop,uj354.res.steps,uj354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact uj354.trans (congrArg some (by kernel_rfl))
  · exact uj543.trans (congrArg some (by kernel_rfl))
theorem jump_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+362)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (Reward.base b true) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_jump hK.2.1) (code_jump hK) s hpc
    (by simp [jumpState,uj354.res,rv_simp]),?_,?_,?_⟩
  · rfl
  · intro r hr; cases r <;> simp_all [jumpState,uj354.res,rv_simp] <;> rfl
  · intro A _ _; simp [jumpState,uj354.res,rv_simp]
sym_block ui354 := symRun {noAlias:=true} initCode (pcOf (354+363)) 200
sym_block ui543 := symRun {noAlias:=true} initCode (pcOf (543+363)) 200
def initState : SymState := ui354.res.st
theorem run_init {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} initCode (pcOf (b+363)) 200=
      some ⟨initState,.c (pcOf (b+366)),ui354.res.stop,ui354.res.steps,ui354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact ui354.trans (congrArg some (by kernel_rfl))
  · exact ui543.trans (congrArg some (by kernel_rfl))
sym_block up354 := symRun {noAlias:=true} ptrCode (pcOf (354+366)) 200
sym_block up543 := symRun {noAlias:=true} ptrCode (pcOf (543+366)) 200
def ptrState : SymState := up354.res.st
theorem run_ptr {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} ptrCode (pcOf (b+366)) 200=
      some ⟨ptrState,.c (pcOf (b+369)),up354.res.stop,up354.res.steps,up354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact up354.trans (congrArg some (by kernel_rfl))
  · exact up543.trans (congrArg some (by kernel_rfl))
theorem init_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+363)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc=pcOf (b+366) ∧
      t.getReg .x20=s.getReg .x20 ∧ t.getReg .x21=BitVec.ofNat 64 DIGITS ∧
      t.getReg .x30=s.getReg .x30+128#64 ∧
      RegsExcept s t [.x21,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_init hK.2.1) (code_init hK) s hpc
    (by simp [initState,ui354.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · rfl
  · simp [initState,ui354.res,rv_simp]
  · simp [initState,ui354.res,rv_simp,DIGITS]
  · simp [initState,ui354.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [initState,ui354.res,rv_simp] <;> rfl
  · intro A _ _; simp [initState,ui354.res,rv_simp]
theorem ptr_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+366)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc=pcOf (b+369) ∧
      t.getReg .x28=((s.getReg .x6 &&& 127#64) <<< 2)+s.getReg .x30 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_ptr hK.2.1) (code_ptr hK) s hpc
    (by simp [ptrState,up354.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [ptrState,up354.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [ptrState,up354.res,rv_simp] <;> rfl
  · intro A _ _; simp [ptrState,up354.res,rv_simp]
theorem shift371_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+371)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+372) ∧
      t.getReg .x29=s.getReg .x29 >>> 8 ∧ RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top371 hK.2.1) (codeAt_top371 hK) s hpc
    (by simp [topState371,tb354_371.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [topState371,tb354_371.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState371,tb354_371.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState371,tb354_371.res,rv_simp]
theorem shift373_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+373)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+374) ∧
      t.getReg .x29=s.getReg .x29 >>> 8 ∧ RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top373 hK.2.1) (codeAt_top373 hK) s hpc
    (by simp [topState373,tb354_373.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [topState373,tb354_373.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState373,tb354_373.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState373,tb354_373.res,rv_simp]
theorem update_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+375)) (i : Nat) (hi : i<17)
    (h20 : s.getReg .x20=BitVec.ofNat 64 i) :
    ∃ t, Steps image s 8 8 t ∧
      t.pc=(if i+1<17 then pcOf (b+366) else pcOf (b+383)) ∧
      t.getReg .x6=(s.getReg .x6 >>> 7 ||| s.getReg .x7 <<< 57) ∧
      t.getReg .x7=s.getReg .x7 >>> 7 ∧ t.getReg .x21=s.getReg .x21+3#64 ∧
      t.getReg .x20=BitVec.ofNat 64 (i+1) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top375 hK.2.1) (codeAt_top375 hK) s hpc
    (by simp [topState375,tb354_375.res,rv_simp]),?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,topEnd375,rebase,tb354_375.res,E.eval,CmpOp.eval,BinOp.eval,h20,
      BitVec.toNat_ofNat,Nat.reduceMod,ofNat_add_ofNat]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (show i+1<18446744073709551616 by omega)]
    by_cases h : i+1<17 <;> simp [h]
  · simp [topState375,tb354_375.res,rv_simp]
  · simp [topState375,tb354_375.res,rv_simp]
  · simp [topState375,tb354_375.res,rv_simp]
  · simp only [Result.toState_getReg,topState375,tb354_375.res,rv_simp,h20,ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [topState375,tb354_375.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState375,tb354_375.res,rv_simp]
end SigGolfCandidate.T3M.Search.TopUnpack
end
section
namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem triple_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+369)) (i r : Nat) (hi : i<17) (hr : r<125)
    (h21 : s.getReg .x21=BitVec.ofNat 64 (DIGITS+3*i))
    (h28 : s.getReg .x28=BitVec.ofNat 64 (TOP_DATA+128+4*r)) (ht : TableOK s) :
    ∃ t, Steps image s 6 6 t ∧ t.pc=pcOf (b+375) ∧
      (∀ B, B<2^64 → t.getByte (BitVec.ofNat 64 B)=
        if B=DIGITS+3*i+2 then BitVec.ofNat 8 (rankDigit r 2)
        else if B=DIGITS+3*i+1 then BitVec.ofNat 8 (rankDigit r 1)
        else if B=DIGITS+3*i then BitVec.ofNat 8 (rankDigit r 0)
        else s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [.x29] ∧ Frame s t Writes := by
  have hb (k : Nat) (hk : k<3) :
      (LoadKind.wu.read s (BitVec.ofNat 64 (TOP_DATA+128+4*r)) >>> (8*k)).truncate 8=
        BitVec.ofNat 8 (rankDigit r k) := by
    rw [read_wu_byte s _ k (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega) (by omega)]
    exact table_rank_byte s ht r k hr hk
  obtain ⟨t1,s1,p1,h29,r1,f1⟩ := load_spec hK s hpc r hr h28
  have hv0 : (t1.getReg .x29).truncate 8=BitVec.ofNat 8 (rankDigit r 0) := by
    rw [h29]
    simpa using hb 0 (by decide)
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := store_spec t1 (pcOf (b+370)) 0x01da8023 .x29 0
    (DIGITS+3*i) (BitVec.ofNat 8 (rankDigit r 0)) (codeAt_top370 hK) p1 rfl
    (by rw [r1.get (by decide),h21]; simp [signExtend12]) hv0 (by omega)
  have p2' : t2.pc=pcOf (b+371) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p2
  obtain ⟨t3,s3,p3,h29a,r3,f3⟩ := shift371_spec hK t2 p2'
  have hv1 : (t3.getReg .x29).truncate 8=BitVec.ofNat 8 (rankDigit r 1) := by
    rw [h29a,r2.get (by decide),h29]
    exact hb 1 (by decide)
  obtain ⟨t4,s4,p4,g4,r4,f4⟩ := store_spec t3 (pcOf (b+372)) 0x01da80a3 .x29 1
    (DIGITS+3*i+1) (BitVec.ofNat 8 (rankDigit r 1)) (codeAt_top372 hK) p3 rfl
    (by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 1) hv1 (by omega)
  have p4' : t4.pc=pcOf (b+373) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p4
  obtain ⟨t5,s5,p5,h29b,r5,f5⟩ := shift373_spec hK t4 p4'
  have hv2 : (t5.getReg .x29).truncate 8=BitVec.ofNat 8 (rankDigit r 2) := by
    rw [h29b,r4.get (by decide),h29a,r2.get (by decide),h29,←BitVec.shiftRight_add]
    exact hb 2 (by decide)
  obtain ⟨t6,s6,p6,g6,r6,f6⟩ := store_spec t5 (pcOf (b+374)) 0x01da8123 .x29 2
    (DIGITS+3*i+2) (BitVec.ofNat 8 (rankDigit r 2)) (codeAt_top374 hK) p5 rfl
    (by rw [r5.get (by decide),r4.get (by decide),r3.get (by decide),r2.get (by decide),r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 2) hv2 (by omega)
  refine ⟨t6,(((((s1.trans s2).trans s3).trans s4).trans s5).trans s6),?_,?_,?_,?_⟩
  · simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p6
  · intro B hB
    rw [g6 B hB,f5.getByte hB (by simp),g4 B hB,f3.getByte hB (by simp),g2 B hB,
      f1.getByte hB (by simp)]
  · exact (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide)
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (by simp)
end SigGolfCandidate.T3M.Search.TopUnpack
end
section
namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
structure Inv (b : Nat) (s0 : MachineState) (v : Digest) (i : Nat) (t : MachineState) : Prop where
  bound : i ≤ 17
  pc : t.pc=if i<17 then pcOf (b+366) else pcOf (b+383)
  lo : t.getReg .x6=BitVec.ofNat 64 (v.toNat/2^(7*i))
  hi : t.getReg .x7=BitVec.ofNat 64 (v.toNat/2^(7*i)/2^64)
  index : t.getReg .x20=BitVec.ofNat 64 i
  ptr : t.getReg .x21=BitVec.ofNat 64 (DIGITS+3*i)
  table : t.getReg .x30=BitVec.ofNat 64 (TOP_DATA+128)
  digits : ∀ j, j<3*i → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (T3.coreDigit 0 (T3.topFlip v) j)
  regs : RegsExcept s0 t Changed
  frame : Frame s0 t Writes
theorem ptr_address (X : Nat) :
    ((BitVec.ofNat 64 X &&& 127#64) <<< 2)+BitVec.ofNat 64 (TOP_DATA+128)=
      BitVec.ofNat 64 (TOP_DATA+128+4*(X%128)) := by
  rw [ofNat_and127, ofNat_shl, ofNat_add_ofNat]
  congr 1
  omega


end SigGolfCandidate.T3M.Search.TopUnpack
end
section
namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
theorem tail383_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+383)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+384) ∧
      t.getReg .x28=s.getReg .x6 &&& 7#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top383 hK.2.1) (codeAt_top383 hK) s hpc
    (by simp [topState383,tb354_383.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [topState383,topEnd383,tb354_383.res,rv_simp]
  · simp [topState383,tb354_383.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState383,tb354_383.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState383,tb354_383.res,rv_simp]
theorem tail385_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+385)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=pcOf (b+387) ∧
      t.getReg .x6=s.getReg .x6 >>> 3 ∧ t.getReg .x28=(s.getReg .x6 >>> 3) &&& 7#64 ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top385 hK.2.1) (codeAt_top385 hK) s hpc
    (by simp [topState385,tb354_385.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [topState385,topEnd385,tb354_385.res,rv_simp]
  · simp [topState385,tb354_385.res,rv_simp]
  · simp [topState385,tb354_385.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState385,tb354_385.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState385,tb354_385.res,rv_simp]
theorem tail388_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+388)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=pcOf (b+390) ∧
      t.getReg .x6=s.getReg .x6 >>> 3 ∧ t.getReg .x28=(s.getReg .x6 >>> 3) &&& 7#64 ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top388 hK.2.1) (codeAt_top388 hK) s hpc
    (by simp [topState388,tb354_388.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [topState388,topEnd388,tb354_388.res,rv_simp]
  · simp [topState388,tb354_388.res,rv_simp]
  · simp [topState388,tb354_388.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState388,tb354_388.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState388,tb354_388.res,rv_simp]
theorem tail391_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+391)) (ret : Nat) (h1 : s.getReg .x1=pcOf ret) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf ret ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top391 hK.2.1) (codeAt_top391 hK) s hpc
    (by simp [topState391,tb354_391.res,rv_simp]),?_,?_,?_⟩
  · simp [topState391,topEnd391,tb354_391.res,rv_simp,h1]
  · intro r hr; simp at hr; cases r <;> simp_all [topState391,tb354_391.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState391,tb354_391.res,rv_simp]
end SigGolfCandidate.T3M.Search.TopUnpack
end
section
namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem mask_byte (X : Nat) :
    (BitVec.ofNat 64 X &&& 7#64).truncate 8=BitVec.ofNat 8 (X%8) := by
  rw [ofNat_and7]
  apply BitVec.eq_of_toNat_eq
  simp
/-- Campaign T8D (NF17): the three raw radix-8 digits above bit 119 (`X = v / 2^119 < 512`): chain 53 = `X % 8`
(stored first, at `DIGITS + 53`), chain 51 = `X / 8 % 8`, chain 52 = `X / 64 % 8`. -/
theorem tail_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (b+383)) (X : Nat) (hX : X<512)
    (h6 : s.getReg .x6=BitVec.ofNat 64 X)
    (h21 : s.getReg .x21=BitVec.ofNat 64 (DIGITS+51)) (ret : Nat) (h1 : s.getReg .x1=pcOf ret) :
    ∃ t, Steps image s 9 9 t ∧ t.pc=pcOf ret ∧
      (∀ B, B<2^64 → t.getByte (BitVec.ofNat 64 B)=
        if B=DIGITS+52 then BitVec.ofNat 8 (X/64%8)
        else if B=DIGITS+51 then BitVec.ofNat 8 (X/8%8)
        else if B=DIGITS+53 then BitVec.ofNat 8 (X%8)
        else s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t Writes := by
  obtain ⟨t1,s1,p1,h28,r1,f1⟩ := tail383_spec hK s hpc
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := store_spec t1 (pcOf (b+384)) 0x01ca8123 .x28 2
    (DIGITS+53) (BitVec.ofNat 8 (X%8)) (codeAt_top384 hK) p1 rfl
    (by rw [r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 2) (by rw [h28,h6,mask_byte]) (by omega)
  have p2' : t2.pc=pcOf (b+385) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p2
  obtain ⟨t3,s3,p3,g6a,h28a,r3,f3⟩ := tail385_spec hK t2 p2'
  have l3 : t3.getReg .x6=BitVec.ofNat 64 (X/8) := by
    rw [g6a,r2.get (by decide),r1.get (by decide),h6,ofNat_shr _ _ (by omega)]
    rfl
  have h28a' : t3.getReg .x28=BitVec.ofNat 64 (X/8) &&& 7#64 := by
    rw [h28a,r2.get (by decide),r1.get (by decide),h6,ofNat_shr _ _ (by omega)]
    rfl
  obtain ⟨t4,s4,p4,g4,r4,f4⟩ := store_spec t3 (pcOf (b+387)) 0x01ca8023 .x28 0
    (DIGITS+51) (BitVec.ofNat 8 (X/8%8)) (codeAt_top387 hK) p3 rfl
    (by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),h21];simp [signExtend12])
    (by rw [h28a',mask_byte]) (by omega)
  have p4' : t4.pc=pcOf (b+388) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p4
  obtain ⟨t5,s5,p5,g6b,h28b,r5,f5⟩ := tail388_spec hK t4 p4'
  have h28b' : t5.getReg .x28=BitVec.ofNat 64 (X/64) &&& 7#64 := by
    rw [h28b,r4.get (by decide),l3,ofNat_shr _ _ (by omega)]
    rw [Nat.div_div_eq_div_mul]
    rfl
  obtain ⟨t6,s6,p6,g6,r6,f6⟩ := store_spec t5 (pcOf (b+390)) 0x01ca80a3 .x28 1
    (DIGITS+52) (BitVec.ofNat 8 (X/64%8)) (codeAt_top390 hK) p5 rfl
    (by rw [r5.get (by decide),r4.get (by decide),r3.get (by decide),r2.get (by decide),r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 1) (by rw [h28b',mask_byte]) (by omega)
  have p6' : t6.pc=pcOf (b+391) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p6
  obtain ⟨t7,s7,p7,r7,f7⟩ := tail391_spec hK t6 p6' ret (by rw [r6.get (by decide),r5.get (by decide),r4.get (by decide),r3.get (by decide),r2.get (by decide),r1.get (by decide),h1])
  refine ⟨t7,((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7),?_,?_,?_,?_⟩
  · exact p7
  · intro B hB
    rw [f7.getByte hB (by simp),g6 B hB,f5.getByte hB (by simp),g4 B hB,
      f3.getByte hB (by simp),g2 B hB,f1.getByte hB (by simp)]
  · exact ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).mono (by decide)
  · exact ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).mono (by simp)
end SigGolfCandidate.T3M.Search.TopUnpack
end
section
namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem init_inv {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (v : Digest) (hpc : s.pc=pcOf (b+363))
    (h6 : s.getReg .x6=BitVec.ofNat 64 v.toNat)
    (h7 : s.getReg .x7=BitVec.ofNat 64 (v.toNat/2^64))
    (h30 : s.getReg .x30=BitVec.ofNat 64 TOP_DATA) (h20z : s.getReg .x20=0) :
    ∃ t, Steps image s 3 3 t ∧ Inv b s v 0 t := by
  obtain ⟨t,hs,hp,h20,h21,h30',hr,hf⟩ := init_spec hK s hpc
  refine ⟨t,hs,⟨by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · simpa using hp
  · simpa using (hr.get (r:=.x6) (by decide)).trans h6
  · simpa using (hr.get (r:=.x7) (by decide)).trans h7
  · rw [h20,h20z]; rfl
  · simpa using h21
  · rw [h30',h30,ofNat_add_ofNat]
  · intro j hj; omega
  · exact hr.mono (by decide)
  · exact hf.mono (by simp)
end SigGolfCandidate.T3M.Search.TopUnpack
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false



end SigGolfCandidate.T3M.Search
end

/-! ## T51 top-trial kernel: generic machine pieces (campaign T51, stream SIGNA) -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem step_alu {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32} {i : Instruction}
    {rd : Reg} {op : BinOp} {a b : Src} (hc : CodeAt image pc [w]) (hpc : s.pc = pc)
    (hdec : decodeInstruction w = some i) (hcl : classify i = some (.alu rd op a b)) :
    Steps image s 1 (instructionCycles i)
      ((s.setReg rd (op.eval (a.eval s) (b.eval s))).setPC (s.pc + 4)) := by
  have hf : fetch image s = some i := (hc.fetch s hpc).trans hdec
  have hs : ordinaryStep s i = some ((s.setReg rd (op.eval (a.eval s) (b.eval s))).setPC (s.pc + 4)) := by
    rw [classify_sound hcl]; rfl
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl (by simp)
theorem step_lwu {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32} {i : Instruction}
    {rd rs : Reg} {off : Word} (hc : CodeAt image pc [w]) (hpc : s.pc = pc)
    (hdec : decodeInstruction w = some i) (hcl : classify i = some (.load .wu rd rs off))
    (hv : accessValid (s.getReg rs + off) 4 = true) :
    Steps image s 1 (instructionCycles i)
      ((s.setReg rd ((s.getWord32 (s.getReg rs + off)).zeroExtend 64)).setPC (s.pc + 4)) := by
  have hf : fetch image s = some i := (hc.fetch s hpc).trans hdec
  have hs : ordinaryStep s i =
      some ((s.setReg rd ((s.getWord32 (s.getReg rs + off)).zeroExtend 64)).setPC (s.pc + 4)) := by
    rw [classify_sound hcl]
    simp only [Micro.exec, LoadKind.width, hv, if_true, LoadKind.read]
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl (by simp)
/-- One table lookup of the half test: `shift t3, src, sh ; andi t3, t3, mask ; add t3, t3, a0 ;
lwu t4, off(t3) ; add acc, acc, t4` (decode facts of the five concrete words are `rfl`). -/
theorem look5 {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 w4 : BitVec 32}
    {i0 i1 i2 i3 i4 : Instruction} {src acc : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3, w4]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 +
      (instructionCycles i4 + 0)))) = 5)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29) (hsrc : src ≠ .x0)
    (hv : accessValid (((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10 + off) 4 = true) :
    let base := ((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10
    let ld := (s.getWord32 (base + off)).zeroExtend 64
    ∃ t, Steps image s 5 5 t ∧ t.pc = s.pc + 20 ∧ t.getReg .x28 = base ∧ t.getReg .x29 = ld ∧
      t.getReg acc = s.getReg acc + ld ∧ RegsExcept s t [.x28, .x29, acc] ∧ Frame s t (fun _ => False) := by
  intro base ld
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have spc : ∀ (x : MachineState) (v : Word), (x.setPC v).pc = v := fun _ _ => rfl
  have sreg : ∀ (x : MachineState) (r : Reg) (v : Word), (x.setReg r v).pc = x.pc := by
    intro x r v; cases r <;> rfl
  have w32p : ∀ (x : MachineState) (v a : Word), (x.setPC v).getWord32 a = x.getWord32 a := fun _ _ _ => rfl
  have w32r : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getWord32 a = x.getWord32 a := by
    intro x r v a; cases r <;> rfl
  have memp : ∀ (x : MachineState) (v a : Word), (x.setPC v).getMem a = x.getMem a := fun _ _ _ => rfl
  have memr : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getMem a = x.getMem a := by
    intro x r v a; cases r <;> rfl
  have gp : ∀ (x : MachineState) (v : Word) (r : Reg), (x.setPC v).getReg r = x.getReg r := getReg_setPC'
  have geq : ∀ (x : MachineState) (r : Reg) (v : Word), r ≠ .x0 → (x.setReg r v).getReg r = v :=
    fun x r v h => MachineState.getReg_setReg_eq h
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have c1 := hc.tail
  have c2 := c1.tail
  have c3 := c2.tail
  have c4 := c3.tail
  have hx28 : (.x28 : Reg) ≠ .x0 := by decide
  have hx29 : (.x29 : Reg) ≠ .x0 := by decide
  have st0 := step_alu (hd hc) hpc hd0 hc0
  generalize hu1 : (s.setReg .x28 (op0.eval ((Src.reg src).eval s) ((Src.imm sh).eval s))).setPC (s.pc + 4) = u1
    at st0
  have p1 : u1.pc = pc + 4 := by rw [← hu1, spc, hpc]
  have r1 : ∀ q, q ≠ .x28 → u1.getReg q = s.getReg q := fun q hq => by rw [← hu1, gp, gne _ _ _ _ hq]
  have g1 : u1.getReg .x28 = op0.eval (s.getReg src) sh := by rw [← hu1, gp, geq _ _ _ hx28]; rfl
  have st1 := step_alu (hd c1) p1 hd1 hc1
  generalize hu2 : (u1.setReg .x28 (BinOp.and.eval ((Src.reg .x28).eval u1) ((Src.imm mask).eval u1))).setPC
    (u1.pc + 4) = u2 at st1
  have p2 : u2.pc = pc + 4 + 4 := by rw [← hu2, spc, p1]
  have r2 : ∀ q, q ≠ .x28 → u2.getReg q = s.getReg q := fun q hq => by rw [← hu2, gp, gne _ _ _ _ hq, r1 q hq]
  have g2 : u2.getReg .x28 = op0.eval (s.getReg src) sh &&& mask := by
    rw [← hu2, gp, geq _ _ _ hx28]; show u1.getReg .x28 &&& mask = _; rw [g1]
  have st2 := step_alu (hd c2) p2 hd2 hc2
  generalize hu3 : (u2.setReg .x28 (BinOp.add.eval ((Src.reg .x28).eval u2) ((Src.reg .x10).eval u2))).setPC
    (u2.pc + 4) = u3 at st2
  have p3 : u3.pc = pc + 4 + 4 + 4 := by rw [← hu3, spc, p2]
  have r3 : ∀ q, q ≠ .x28 → u3.getReg q = s.getReg q := fun q hq => by rw [← hu3, gp, gne _ _ _ _ hq, r2 q hq]
  have g3 : u3.getReg .x28 = base := by
    rw [← hu3, gp, geq _ _ _ hx28]; show u2.getReg .x28 + u2.getReg .x10 = base; rw [g2, r2 .x10 (by decide)]
  have m3 : ∀ a, u3.getWord32 a = s.getWord32 a := fun a => by
    rw [← hu3, w32p, w32r, ← hu2, w32p, w32r, ← hu1, w32p, w32r]
  have hv3 : accessValid (u3.getReg .x28 + off) 4 = true := by rw [g3]; exact hv
  have st3 := step_lwu (hd c3) p3 hd3 hc3 hv3
  generalize hu4 : (u3.setReg .x29 ((u3.getWord32 (u3.getReg .x28 + off)).zeroExtend 64)).setPC (u3.pc + 4) = u4
    at st3
  have p4 : u4.pc = pc + 4 + 4 + 4 + 4 := by rw [← hu4, spc, p3]
  have g4 : u4.getReg .x29 = ld := by rw [← hu4, gp, geq _ _ _ hx29, g3, m3]
  have g4' : u4.getReg .x28 = base := by rw [← hu4, gp, gne _ _ _ _ (by decide), g3]
  have r4 : ∀ q, q ≠ .x28 → q ≠ .x29 → u4.getReg q = s.getReg q := fun q hq hq' => by
    rw [← hu4, gp, gne _ _ _ _ hq', r3 q hq]
  have st4 := step_alu (hd c4) p4 hd4 hc4
  generalize hu5 : (u4.setReg acc (BinOp.add.eval ((Src.reg acc).eval u4) ((Src.reg .x29).eval u4))).setPC
    (u4.pc + 4) = u5 at st4
  refine ⟨u5, ((((st0.trans st1).trans st2).trans st3).trans st4).of_eq rfl ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hcy
  · rw [← hu5, spc, p4, hpc]; bv_omega
  · rw [← hu5, gp, gne _ _ _ _ (Ne.symm hacc.2.1), g4']
  · rw [← hu5, gp, gne _ _ _ _ (Ne.symm hacc.2.2), g4]
  · rw [← hu5, gp, geq _ _ _ hacc.1]; show u4.getReg acc + u4.getReg .x29 = _; rw [g4, r4 acc hacc.2.1 hacc.2.2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [← hu5, gp, gne _ _ _ _ hr.2.2, r4 r hr.1 hr.2.1]
  · intro A _ _
    rw [← hu5, memp, memr, ← hu4, memp, memr, ← hu3, memp, memr, ← hu2, memp, memr, ← hu1, memp, memr]
/-! ### Field extraction and table addressing -/
theorem shr_and_mul4 (x : Word) (S w : Nat) (h : S + 2 + w ≤ 64) :
    (x >>> S) &&& BitVec.ofNat 64 (4 * (2 ^ w - 1)) = BitVec.ofNat 64 (4 * (x.toNat / 2 ^ (S + 2) % 2 ^ w)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 : 4 * (2 ^ w - 1) = (2 ^ w - 1) * 2 ^ 2 := by ring
  have e2 : 4 * (x.toNat / 2 ^ (S + 2) % 2 ^ w) = (x.toNat / 2 ^ (S + 2) % 2 ^ w) * 2 ^ 2 := by ring
  rw [e1, e2]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, hi, decide_true,
    Bool.true_and, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, BitVec.testBit_toNat]
  by_cases h2 : 2 ≤ i
  · by_cases hw : i - 2 < w
    · simp only [h2, hw, decide_true, Bool.true_and, Bool.and_true]
      congr 1; omega
    · simp [h2, hw]
  · simp [h2]
theorem shl2_and_mul4 (x : Word) (w : Nat) (h : 2 + w ≤ 64) :
    (x <<< 2) &&& BitVec.ofNat 64 (4 * (2 ^ w - 1)) = BitVec.ofNat 64 (4 * (x.toNat % 2 ^ w)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 : 4 * (2 ^ w - 1) = (2 ^ w - 1) * 2 ^ 2 := by ring
  have e2 : 4 * (x.toNat % 2 ^ w) = (x.toNat % 2 ^ w) * 2 ^ 2 := by ring
  rw [e1, e2]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi, decide_true,
    Bool.true_and, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, BitVec.testBit_toNat]
  by_cases h2 : 2 ≤ i
  · by_cases hw : i - 2 < w
    · simp only [h2, hw, decide_true, Bool.true_and, Bool.and_true, Bool.not_false]
      simp [show ¬ i < 2 by omega]
    · simp [h2, hw]
  · simp [h2, show i < 2 by omega]
/-- A table lookup with a known field value: the accumulator gains the packed entry `f`. -/
theorem look5_entry {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 w4 : BitVec 32}
    {i0 i1 i2 i3 i4 : Instruction} {src acc : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3, w4]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 +
      (instructionCycles i4 + 0)))) = 5)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29) (hsrc : src ≠ .x0)
    {blk r f : Nat} (ht : T51TableW blk s) (hblk : blk % 8 = 0) (hb : blk + 1896 < 2 ^ 24) (hf : f < 473)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f)) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = s.pc + 20 ∧ t.getReg .x29 = BitVec.ofNat 64 (tEntry f) ∧
      t.getReg acc = s.getReg acc + BitVec.ofNat 64 (tEntry f) ∧ RegsExcept s t [.x28, .x29, acc] ∧
      Frame s t (fun _ => False) := by
  have haddr : (op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off = BitVec.ofNat 64 (blk + 4 * f) := by
    rw [hbase, h10, hoff]
  have hv : accessValid ((op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off) 4 = true := by
    rw [haddr]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show blk + 4 * f < 2 ^ 64 by omega)]
    omega
  obtain ⟨t, st, pt, _, g29, gacc, rt, ft⟩ := look5 hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hd4 hc4 hcy hacc hsrc hv
  have hw : (s.getWord32 (BitVec.ofNat 64 (blk + 4 * f))).zeroExtend 64 = BitVec.ofNat 64 (tEntry f) := by
    rw [ht f hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
    have := tEntry_lt f hf
    have h64 : tEntry f < 2 ^ 64 := by omega
    simp only [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h64]
  refine ⟨t, st, pt, ?_, ?_, rt, ft⟩
  · rw [g29, haddr, hw]
  · rw [gacc, haddr, hw]
theorem lo_field (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (v.extractLsb' 0 64).toNat / 2 ^ S % 2 ^ w = v.toNat / 2 ^ S % 2 ^ w := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, show i + S < 64 by omega]
  · simp [hi]
/-! ### BitVec value helpers -/
theorem bv_and_mask (x : Word) (w : Nat) (hw : w ≤ 64) :
    x &&& BitVec.ofNat 64 (2 ^ w - 1) = BitVec.ofNat 64 (x.toNat % 2 ^ w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ w - 1 < 2 ^ 64 by
      have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
      have : 0 < 2 ^ w := by positivity
      omega), Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt
  have : x.toNat % 2 ^ w < 2 ^ 64 := lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
  rw [Nat.mod_eq_of_lt this]
theorem bv_shr (a k : Nat) (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) :=
  ofNat_shr a k ha
theorem bv_ult (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp [BitVec.ult, toNat_ofNat_lt ha, toNat_ofNat_lt hb]
theorem bv_sub (a b : Nat) (hab : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  omega
theorem bv_and_ofNat (a m : Nat) (ha : a < 2 ^ 64) (hm : m < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 m = BitVec.ofNat 64 (a &&& m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt ha, toNat_ofNat_lt hm,
    toNat_ofNat_lt (lt_of_le_of_lt Nat.and_le_left ha)]
/-! ### Generic single-instruction pieces (branch / jump), via a pc-generic symbolic run -/
theorem br_spec {image : Image} {w : BitVec 32} {pc off : Word} {op : CmpOp} {x y : E}
    (hrun : symRun { noAlias := true } [w] pc 10 =
      some ⟨SymState.init, .ite op x y (.c (pc + off)) (.c (pc + 4)), .branch, 1, 1⟩)
    (hc : CodeAt image pc [w]) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if op.eval (x.eval s) (y.eval s) then pc + off else pc + 4) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [rv_simp, SymState.init]), ?_, ?_, ?_⟩
  · simp only [rv_simp] <;> split <;> rfl
  · intro r _; simp only [rv_simp, SymState.init]; cases r <;> rfl
  · intro A _ _; simp only [rv_simp, SymState.init]
theorem jal_spec {image : Image} {w : BitVec 32} {pc off : Word}
    (hrun : symRun { noAlias := true } [w] pc 10 = some ⟨SymState.init, .c (pc + off), .jump, 1, 1⟩)
    (hc : CodeAt image pc [w]) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + off ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [rv_simp, SymState.init]), ?_, ?_, ?_⟩
  · simp only [rv_simp]
  · intro r _; simp only [rv_simp, SymState.init]; cases r <;> rfl
  · intro A _ _; simp only [rv_simp, SymState.init]
theorem land_mask (n w : Nat) : n &&& (2 ^ w - 1) = n % 2 ^ w := Nat.and_two_pow_sub_one_eq_mod n w
theorem t5_val (v : Digest) :
    (v.extractLsb' 0 64 >>> 63) ||| (v.extractLsb' 64 64 <<< 1) = BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat]
  simp only [BitVec.getLsbD, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hi, decide_true, Bool.true_and]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · simp only [show ¬ 63 + i < 64 by omega, show ¬ i < 1 by omega, show i - 1 < 64 by omega, decide_false,
      decide_true, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and]
    rw [show 64 + (i - 1) = i + 63 by omega]
/-! ### pc arithmetic -/
theorem pcOf_plus (k n : Nat) (h : 0x1000 + 4 * (k + n) < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 (4 * n) = pcOf (k + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
theorem pcOf_minus (k n : Nat) (hn : n ≤ k) (h : 0x1000 + 4 * k < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 (2 ^ 64 - 4 * n) = pcOf (k - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
theorem pcOf_4 (k : Nat) : pcOf k + 4 = pcOf (k + 1) := pcOf_add4 k
theorem pcOf_4' (k : Nat) : pcOf k + 4#64 = pcOf (k + 1) := pcOf_add4 k
/-! ### Table lookups -/
/-- Four-instruction lookup (`shift t3, src, sh ; andi t3, t3, mask ; add t3, t3, a0 ; lwu rd, off(t3)`). -/
theorem look4 {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 : BitVec 32}
    {i0 i1 i2 i3 : Instruction} {src rd : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu rd .x28 off))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 + 0))) = 4)
    (hrd : rd ≠ .x0 ∧ rd ≠ .x28) (hsrc : src ≠ .x0)
    (hv : accessValid (((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10 + off) 4 = true) :
    let base := ((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10
    let ld := (s.getWord32 (base + off)).zeroExtend 64
    ∃ t, Steps image s 4 4 t ∧ t.pc = s.pc + 16 ∧ t.getReg rd = ld ∧
      RegsExcept s t [.x28, rd] ∧ Frame s t (fun _ => False) := by
  intro base ld
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have spc : ∀ (x : MachineState) (v : Word), (x.setPC v).pc = v := fun _ _ => rfl
  have w32p : ∀ (x : MachineState) (v a : Word), (x.setPC v).getWord32 a = x.getWord32 a := fun _ _ _ => rfl
  have w32r : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getWord32 a = x.getWord32 a := by
    intro x r v a; cases r <;> rfl
  have memp : ∀ (x : MachineState) (v a : Word), (x.setPC v).getMem a = x.getMem a := fun _ _ _ => rfl
  have memr : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getMem a = x.getMem a := by
    intro x r v a; cases r <;> rfl
  have gp : ∀ (x : MachineState) (v : Word) (r : Reg), (x.setPC v).getReg r = x.getReg r := getReg_setPC'
  have geq : ∀ (x : MachineState) (r : Reg) (v : Word), r ≠ .x0 → (x.setReg r v).getReg r = v :=
    fun x r v h => MachineState.getReg_setReg_eq h
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have c1 := hc.tail
  have c2 := c1.tail
  have c3 := c2.tail
  have hx28 : (.x28 : Reg) ≠ .x0 := by decide
  have st0 := step_alu (hd hc) hpc hd0 hc0
  generalize hu1 : (s.setReg .x28 (op0.eval ((Src.reg src).eval s) ((Src.imm sh).eval s))).setPC (s.pc + 4) = u1
    at st0
  have p1 : u1.pc = pc + 4 := by rw [← hu1, spc, hpc]
  have r1 : ∀ q, q ≠ .x28 → u1.getReg q = s.getReg q := fun q hq => by rw [← hu1, gp, gne _ _ _ _ hq]
  have g1 : u1.getReg .x28 = op0.eval (s.getReg src) sh := by rw [← hu1, gp, geq _ _ _ hx28]; rfl
  have st1 := step_alu (hd c1) p1 hd1 hc1
  generalize hu2 : (u1.setReg .x28 (BinOp.and.eval ((Src.reg .x28).eval u1) ((Src.imm mask).eval u1))).setPC
    (u1.pc + 4) = u2 at st1
  have p2 : u2.pc = pc + 4 + 4 := by rw [← hu2, spc, p1]
  have r2 : ∀ q, q ≠ .x28 → u2.getReg q = s.getReg q := fun q hq => by rw [← hu2, gp, gne _ _ _ _ hq, r1 q hq]
  have g2 : u2.getReg .x28 = op0.eval (s.getReg src) sh &&& mask := by
    rw [← hu2, gp, geq _ _ _ hx28]; show u1.getReg .x28 &&& mask = _; rw [g1]
  have st2 := step_alu (hd c2) p2 hd2 hc2
  generalize hu3 : (u2.setReg .x28 (BinOp.add.eval ((Src.reg .x28).eval u2) ((Src.reg .x10).eval u2))).setPC
    (u2.pc + 4) = u3 at st2
  have p3 : u3.pc = pc + 4 + 4 + 4 := by rw [← hu3, spc, p2]
  have r3 : ∀ q, q ≠ .x28 → u3.getReg q = s.getReg q := fun q hq => by rw [← hu3, gp, gne _ _ _ _ hq, r2 q hq]
  have g3 : u3.getReg .x28 = base := by
    rw [← hu3, gp, geq _ _ _ hx28]; show u2.getReg .x28 + u2.getReg .x10 = base; rw [g2, r2 .x10 (by decide)]
  have m3 : ∀ a, u3.getWord32 a = s.getWord32 a := fun a => by
    rw [← hu3, w32p, w32r, ← hu2, w32p, w32r, ← hu1, w32p, w32r]
  have hv3 : accessValid (u3.getReg .x28 + off) 4 = true := by rw [g3]; exact hv
  have st3 := step_lwu (hd c3) p3 hd3 hc3 hv3
  generalize hu4 : (u3.setReg rd ((u3.getWord32 (u3.getReg .x28 + off)).zeroExtend 64)).setPC (u3.pc + 4) = u4
    at st3
  refine ⟨u4, (((st0.trans st1).trans st2).trans st3).of_eq rfl ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hcy
  · rw [← hu4, spc, p3, hpc]; bv_omega
  · rw [← hu4, gp, geq _ _ _ hrd.1, g3, m3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [← hu4, gp, gne _ _ _ _ hr.2, r3 r hr.1]
  · intro A _ _
    rw [← hu4, memp, memr, ← hu3, memp, memr, ← hu2, memp, memr, ← hu1, memp, memr]
theorem look4_entry {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 : BitVec 32}
    {i0 i1 i2 i3 : Instruction} {src rd : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu rd .x28 off))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 + 0))) = 4)
    (hrd : rd ≠ .x0 ∧ rd ≠ .x28) (hsrc : src ≠ .x0)
    {blk r f : Nat} (ht : T51TableW blk s) (hblk : blk % 8 = 0) (hb : blk + 1896 < 2 ^ 24) (hf : f < 473)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = s.pc + 16 ∧ t.getReg rd = BitVec.ofNat 64 (tEntry f) ∧
      RegsExcept s t [.x28, rd] ∧ Frame s t (fun _ => False) := by
  have haddr : (op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off = BitVec.ofNat 64 (blk + 4 * f) := by
    rw [hbase, h10, hoff]
  have hv : accessValid ((op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off) 4 = true := by
    rw [haddr]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show blk + 4 * f < 2 ^ 64 by omega)]
    omega
  obtain ⟨t, st, pt, grd, rt, ft⟩ := look4 hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hcy hrd hsrc hv
  have hw : (s.getWord32 (BitVec.ofNat 64 (blk + 4 * f))).zeroExtend 64 = BitVec.ofNat 64 (tEntry f) := by
    rw [ht f hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
    have := tEntry_lt f hf
    have h64 : tEntry f < 2 ^ 64 := by omega
    simp only [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h64]
  refine ⟨t, st, pt, ?_, rt, ft⟩
  rw [grd]; simp only [haddr, hw]
/-- Five-instruction lookup with accumulation, relative to the half-test start state `s0`. -/
theorem lookR {image : Image} {s0 s : MachineState} {k : Nat} {w0 w1 w2 w3 w4 : BitVec 32}
    {i0 i1 i2 i3 i4 : Instruction} {src acc : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image (pcOf k) [w0, w1, w2, w3, w4]) (hpc : s.pc = pcOf k) (hk : 0x1000 + 4 * (k + 5) < 2 ^ 64)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 +
      (instructionCycles i4 + 0)))) = 5)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29) (hsrc : src ≠ .x0)
    {L : List Reg} (hL : .x28 ∈ L ∧ .x29 ∈ L ∧ acc ∈ L) (h10L : .x10 ∉ L)
    (hR : RegsExcept s0 s L) (hF : Frame s0 s (fun _ => False))
    {blk r f n : Nat} (ht : T51TableW blk s0) (hblk : blk % 8 = 0) (hb : blk + 1896 < 2 ^ 24) (hf : f < 473)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f))
    (hn : s.getReg acc = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf (k + 5) ∧ RegsExcept s0 t L ∧ Frame s0 t (fun _ => False) ∧
      t.getReg acc = BitVec.ofNat 64 (n + tEntry f) ∧ RegsExcept s t [.x28, .x29, acc] := by
  have ht' : T51TableW blk s := ht.frame hF hblk (by omega) (fun _ _ h => h)
  have h10' : s.getReg .x10 = BitVec.ofNat 64 (blk + 160) := (hR .x10 h10L).trans h10
  obtain ⟨t, st, pt, _, gacc, rt, ft⟩ :=
    look5_entry hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hd4 hc4 hcy hacc hsrc ht' hblk hb hf h10' hbase hoff
  refine ⟨t, st, ?_, ?_, ?_, ?_, rt⟩
  · rw [pt, hpc, show (20 : Word) = BitVec.ofNat 64 (4 * 5) from rfl, pcOf_plus _ _ hk]
  · refine (hR.trans rt).mono ?_
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq | hq
    · exact hq
    · exact hq ▸ hL.1
    · exact hq ▸ hL.2.1
    · exact hq ▸ hL.2.2
  · exact (hF.trans ft).mono (fun _ _ h => by simpa using h)
  · rw [gacc, hn, ofNat_add_ofNat]
/-- Four-instruction lookup (the accumulator is loaded), relative to the half-test start state `s0`. -/
theorem lookW {image : Image} {s0 s : MachineState} {k : Nat} {w0 w1 w2 w3 : BitVec 32}
    {i0 i1 i2 i3 : Instruction} {src rd : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image (pcOf k) [w0, w1, w2, w3]) (hpc : s.pc = pcOf k) (hk : 0x1000 + 4 * (k + 4) < 2 ^ 64)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu rd .x28 off))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 + 0))) = 4)
    (hrd : rd ≠ .x0 ∧ rd ≠ .x28) (hsrc : src ≠ .x0)
    {L : List Reg} (hL : .x28 ∈ L ∧ rd ∈ L) (h10L : .x10 ∉ L)
    (hR : RegsExcept s0 s L) (hF : Frame s0 s (fun _ => False))
    {blk r f : Nat} (ht : T51TableW blk s0) (hblk : blk % 8 = 0) (hb : blk + 1896 < 2 ^ 24) (hf : f < 473)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (k + 4) ∧ RegsExcept s0 t L ∧ Frame s0 t (fun _ => False) ∧
      t.getReg rd = BitVec.ofNat 64 (tEntry f) ∧ RegsExcept s t [.x28, rd] := by
  have ht' : T51TableW blk s := ht.frame hF hblk (by omega) (fun _ _ h => h)
  have h10' : s.getReg .x10 = BitVec.ofNat 64 (blk + 160) := (hR .x10 h10L).trans h10
  obtain ⟨t, st, pt, grd, rt, ft⟩ :=
    look4_entry hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hcy hrd hsrc ht' hblk hb hf h10' hbase hoff
  refine ⟨t, st, ?_, ?_, ?_, grd, rt⟩
  · rw [pt, hpc, show (16 : Word) = BitVec.ofNat 64 (4 * 4) from rfl, pcOf_plus _ _ hk]
  · refine (hR.trans rt).mono ?_
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq
    · exact hq
    · exact hq ▸ hL.1
    · exact hq ▸ hL.2
  · exact (hF.trans ft).mono (fun _ _ h => by simpa using h)
theorem hoff_eq {blk r f O : Nat} (h : (4 * r + (blk + 160) + O) % 2 ^ 64 = blk + 4 * f) :
    BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + BitVec.ofNat 64 O = BitVec.ofNat 64 (blk + 4 * f) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, h]
  have : blk + 4 * f < 2 ^ 64 := by rw [← h]; exact Nat.mod_lt _ (by norm_num)
  omega
theorem lo_mod (v : Digest) (w : Nat) (h : w ≤ 64) : (v.extractLsb' 0 64).toNat % 2 ^ w = v.toNat % 2 ^ w := by
  have := lo_field v 0 w (by omega)
  simpa using this
theorem t5_field (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    v.toNat / 2 ^ 63 % 2 ^ 64 / 2 ^ S % 2 ^ w = v.toNat / 2 ^ (63 + S) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, show i + S < 64 by omega]
    congr 1; omega
  · simp [hi]
theorem t5_mod (v : Digest) (w : Nat) (h : w ≤ 64) :
    v.toNat / 2 ^ 63 % 2 ^ 64 % 2 ^ w = v.toNat / 2 ^ 63 % 2 ^ w :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)
theorem t5_lt (v : Digest) : v.toNat / 2 ^ 63 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
theorem pcOf_3 (k : Nat) : pcOf k + 4 + 4 + 4 = pcOf (k + 3) := by
  rw [pcOf_4, pcOf_4, pcOf_4]
end SigGolfCandidate.T3M.Search.T51
end

/-! ## T51 top-trial kernel: instance parameters, layout and the half test (campaign T51, stream SIGNA)
One kernel `K` (129 words) for sign and expand. The instances differ only in five parameter words, abstracted here
by `KInst` (the words) and the hooks of `T51KAt` (their behaviour):
* words 0, 1: `lui a0 ; addi a0` = table block + 160 (`hE`);
* word 117: `sd t4, CREDIT(t5)` (`hCr`, credit cell `0x66000 + CREDIT`);
* word 119: `j U_ENTRY` (`hU`);
* word 128: `j NEXT` (`hN`, the reject continuation).
Sign: `K_ENTRY` 1798, block 0xFFF800, credit 0x66018, `U_ENTRY` 21230, `NEXT` 1011.
Expand: `K_ENTRY` 54176, block RAM 0xA0000, credit 0x66040, `U_ENTRY` 54356, `NEXT` 822. -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The choice flag cell (0 = LOW, 128 = HIGH); `FLAG` in `Selector`. -/
abbrev FLAGA : Nat := 0x667F8
/-- Instance parameters of the shared kernel and unpacker. -/
structure KInst where
  /-- `K_ENTRY` (word index). -/
  kb : Nat
  /-- `U_ENTRY` (first unpacker segment, 112 words). -/
  ub : Nat
  /-- Second unpacker segment (54 words). -/
  uc : Nat
  /-- Steps from `ub + 112` to `uc` (sign: 1, the split jump; expand: 0, contiguous). -/
  uj : Nat
  /-- Table block address (the kernel's `a0` is `blk + 160`). -/
  blk : Nat
  /-- Credit cell (`0x66000 + CREDIT`). -/
  credit : Nat
  /-- Reject continuation (word index). -/
  rej : Nat
  w0 : BitVec 32
  w1 : BitVec 32
  wCr : BitVec 32
  wU : BitVec 32
  wN : BitVec 32
def kE2 : List (BitVec 32) := [0xa13,0xc00a93]
def kG0a : List (BitVec 32) := [0x231e13,0x3fce7e13,0xae0e33,0xf60e6c83]
def kG0b : List (BitVec 32) := [0xccde93,0x4efe93,0x1dc8cb3]
def kLk1 : List (BitVec 32) := [0x635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk2 : List (BitVec 32) := [0xe35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk3 : List (BitVec 32) := [0x1635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk4 : List (BitVec 32) := [0x1e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk5 : List (BitVec 32) := [0x2635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk6 : List (BitVec 32) := [0x2e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kR7a : List (BitVec 32) := [0x3635e13,0x1fce7e13,0x13ce3e93]
def kR7b : List (BitVec 32) := [0x120e9863]
def kR7l : List (BitVec 32) := [0xae0e33,0x4c4e6e83,0x1dc8cb3]
def kT5 : List (BitVec 32) := [0x3f35f13,0x139e13,0x1cf6f33]
def kQ9 : List (BitVec 32) := [0x2f1e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kQ10 : List (BitVec 32) := [0x5f5e13,0x1fce7e13,0xae0e33,0x400e6583]
def kQ11 : List (BitVec 32) := [0xcf5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3]
def kQ12 : List (BitVec 32) := [0x13f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3]
def kQ13 : List (BitVec 32) := [0x1af5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kQ14 : List (BitVec 32) := [0x21f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kQ15 : List (BitVec 32) := [0x28f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kG7 : List (BitVec 32) := [0x2e3de13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kG8 : List (BitVec 32) := [0x363de13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kTot : List (BitVec 32) := [0xbc8cb3,0x125d593,0xf5f593,0x16cde13,0x41c88e33,0x6e3e93]
def kBr101 : List (BitVec 32) := [0x40e8663]
def kH2a : List (BitVec 32) := [0x8cde93,0x3fefe93,0x1e3f13,0x1ee8eb3,0x8ebe93]
def kBr107 : List (BitVec 32) := [0x20e8a63]
def kH3a : List (BitVec 32) := [0xffcfe93,0x40be8eb3,0xffce0f13,0x1f3f13,0x1ee8eb3]
def kBr113 : List (BitVec 32) := [0x15ece63]
def kBrA0 : List (BitVec 32) := [0xa1463]
def kA1 : List (BitVec 32) := [0x2e8e93]
def kLuiT5 : List (BitVec 32) := [0x66f37]
def kSdF : List (BitVec 32) := [0x7f4f3c23]
def kBrF0 : List (BitVec 32) := [0x20a1063]
def kF1a : List (BitVec 32) := [0x3e3de93]
def kBr122 : List (BitVec 32) := [0xe8c63]
def kF2a : List (BitVec 32) := [0x8000a13,0xe00a93,0x1063303,0x1863383]
def kJ127 : List (BitVec 32) := [0xe15ff06f]
/-- Fine layout of the 129-word kernel (every lookup, every branch and every parameter word its own segment). -/
def kLF (P : KInst) : Rv.Layout := [(0, [P.w0, P.w1]), (2, kE2), (4, kG0a), (8, kG0b), (11, kLk1), (16, kLk2),
  (21, kLk3), (26, kLk4), (31, kLk5), (36, kLk6), (41, kR7a), (44, kR7b), (45, kR7l), (48, kT5), (51, kQ9),
  (56, kQ10), (60, kQ11), (65, kQ12), (70, kQ13), (75, kQ14), (80, kQ15), (85, kG7), (90, kG8), (95, kTot),
  (101, kBr101), (102, kH2a), (107, kBr107), (108, kH3a), (113, kBr113), (114, kBrA0), (115, kA1), (116, kLuiT5),
  (117, [P.wCr]), (118, kSdF), (119, [P.wU]), (120, kBrF0), (121, kF1a), (122, kBr122), (123, kF2a), (127, kJ127),
  (128, [P.wN])]
/-- The kernel code of instance `P`. -/
def kCode (P : KInst) : List (BitVec 32) := layoutCode (kLF P)
theorem kLF_ok (P : KInst) : layoutOk 0 (kLF P) = true := rfl
/-- The kernel is installed for instance `P`, with the behaviour of its parameter words. -/
structure T51KAt (image : Image) (P : KInst) : Prop where
  code : CodeAt image (pcOf P.kb) (kCode P)
  kbLt : P.kb + 129 < 2 ^ 40
  blk8 : P.blk % 8 = 0
  blkLt : P.blk + 1896 < 2 ^ 24
  credit8 : P.credit % 8 = 0
  creditLt : P.credit < 2 ^ 24
  creditNe : P.credit ≠ FLAGA
  hE : ∀ s : MachineState, s.pc = pcOf P.kb → ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (P.kb + 2) ∧
    t.getReg .x10 = BitVec.ofNat 64 (P.blk + 160) ∧ RegsExcept s t [.x10] ∧ Frame s t (fun _ => False)
  hCr : ∀ s : MachineState, s.pc = pcOf (P.kb + 117) → s.getReg .x30 = BitVec.ofNat 64 0x66000 →
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (P.kb + 118) ∧ t.getMem (BitVec.ofNat 64 P.credit) = s.getReg .x29 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = P.credit)
  hU : ∀ s : MachineState, s.pc = pcOf (P.kb + 119) → ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf P.ub ∧
    RegsExcept s t [] ∧ Frame s t (fun _ => False)
  hN : ∀ s : MachineState, s.pc = pcOf (P.kb + 128) → ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf P.rej ∧
    RegsExcept s t [] ∧ Frame s t (fun _ => False)
theorem codeAt_kf {image : Image} {P : KInst} (h : T51KAt image P) (i : Nat) {o : Nat} {seg : List (BitVec 32)}
    (hi : (kLF P)[i]? = some (o, seg)) : CodeAt image (pcOf (P.kb + o)) seg :=
  codeAt_sublayout h.code (kLF_ok P) hi
/-! ### Three-instruction lookup tail (`add t3, t3, a0 ; lwu t4, off(t3) ; add acc, acc, t4`) -/
theorem look3 {image : Image} {s : MachineState} {pc : Word} {w2 w3 w4 : BitVec 32}
    {i2 i3 i4 : Instruction} {acc : Reg} {off : Word}
    (hc : CodeAt image pc [w2, w3, w4]) (hpc : s.pc = pc)
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i2 + (instructionCycles i3 + (instructionCycles i4 + 0)) = 3)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29)
    (hv : accessValid (s.getReg .x28 + s.getReg .x10 + off) 4 = true) :
    let ld := (s.getWord32 (s.getReg .x28 + s.getReg .x10 + off)).zeroExtend 64
    ∃ t, Steps image s 3 3 t ∧ t.pc = s.pc + 12 ∧ t.getReg .x29 = ld ∧
      t.getReg acc = s.getReg acc + ld ∧ RegsExcept s t [.x28, .x29, acc] ∧ Frame s t (fun _ => False) := by
  intro ld
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have spc : ∀ (x : MachineState) (v : Word), (x.setPC v).pc = v := fun _ _ => rfl
  have w32p : ∀ (x : MachineState) (v a : Word), (x.setPC v).getWord32 a = x.getWord32 a := fun _ _ _ => rfl
  have w32r : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getWord32 a = x.getWord32 a := by
    intro x r v a; cases r <;> rfl
  have memp : ∀ (x : MachineState) (v a : Word), (x.setPC v).getMem a = x.getMem a := fun _ _ _ => rfl
  have memr : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getMem a = x.getMem a := by
    intro x r v a; cases r <;> rfl
  have gp : ∀ (x : MachineState) (v : Word) (r : Reg), (x.setPC v).getReg r = x.getReg r := getReg_setPC'
  have geq : ∀ (x : MachineState) (r : Reg) (v : Word), r ≠ .x0 → (x.setReg r v).getReg r = v :=
    fun x r v h => MachineState.getReg_setReg_eq h
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have c3 := hc.tail
  have c4 := c3.tail
  have hx28 : (.x28 : Reg) ≠ .x0 := by decide
  have hx29 : (.x29 : Reg) ≠ .x0 := by decide
  have st2 := step_alu (hd hc) hpc hd2 hc2
  generalize hu3 : (s.setReg .x28 (BinOp.add.eval ((Src.reg .x28).eval s) ((Src.reg .x10).eval s))).setPC
    (s.pc + 4) = u3 at st2
  have p3 : u3.pc = pc + 4 := by rw [← hu3, spc, hpc]
  have r3 : ∀ q, q ≠ .x28 → u3.getReg q = s.getReg q := fun q hq => by rw [← hu3, gp, gne _ _ _ _ hq]
  have g3 : u3.getReg .x28 = s.getReg .x28 + s.getReg .x10 := by
    rw [← hu3, gp, geq _ _ _ hx28]; rfl
  have m3 : ∀ a, u3.getWord32 a = s.getWord32 a := fun a => by rw [← hu3, w32p, w32r]
  have hv3 : accessValid (u3.getReg .x28 + off) 4 = true := by rw [g3]; exact hv
  have st3 := step_lwu (hd c3) p3 hd3 hc3 hv3
  generalize hu4 : (u3.setReg .x29 ((u3.getWord32 (u3.getReg .x28 + off)).zeroExtend 64)).setPC (u3.pc + 4) = u4
    at st3
  have p4 : u4.pc = pc + 4 + 4 := by rw [← hu4, spc, p3]
  have g4 : u4.getReg .x29 = ld := by rw [← hu4, gp, geq _ _ _ hx29, g3, m3]
  have r4 : ∀ q, q ≠ .x28 → q ≠ .x29 → u4.getReg q = s.getReg q := fun q hq hq' => by
    rw [← hu4, gp, gne _ _ _ _ hq', r3 q hq]
  have st4 := step_alu (hd c4) p4 hd4 hc4
  generalize hu5 : (u4.setReg acc (BinOp.add.eval ((Src.reg acc).eval u4) ((Src.reg .x29).eval u4))).setPC
    (u4.pc + 4) = u5 at st4
  refine ⟨u5, ((st2.trans st3).trans st4).of_eq rfl ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hcy
  · rw [← hu5, spc, p4, hpc]; bv_omega
  · rw [← hu5, gp, gne _ _ _ _ (Ne.symm hacc.2.2), g4]
  · rw [← hu5, gp, geq _ _ _ hacc.1]; show u4.getReg acc + u4.getReg .x29 = _; rw [g4, r4 acc hacc.2.1 hacc.2.2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [← hu5, gp, gne _ _ _ _ hr.2.2, r4 r hr.1 hr.2.1]
  · intro A _ _
    rw [← hu5, memp, memr, ← hu4, memp, memr, ← hu3, memp, memr]
/-! ### Kernel pieces (fixed words, pc-generic symbolic runs) -/
theorem steps_sd {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32}
    (hc : CodeAt image pc [w]) (hpc : s.pc = pc) {rs1 rs2 : Reg} {off : BitVec 12}
    (hdec : decodeInstruction w = some (.base (.SD rs1 rs2 off)))
    (hv : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    Steps image s 1 1 ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4)) := by
  have hf : fetch image s = some (.base (.SD rs1 rs2 off)) := (hc.fetch s hpc).trans hdec
  have hcl : classify (.base (.SD rs1 rs2 off)) = some (.store .d rs1 rs2 (signExtend12 off)) := rfl
  have hs : ordinaryStep s (.base (.SD rs1 rs2 off)) =
      some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4)) := by
    rw [classify_sound hcl]
    simp only [Micro.exec, StoreKind.width, hv, if_true, StoreKind.write]
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl rfl
/-- A store `sd rs2, off(rs1)` with `rs1 = base` (8-aligned target `base + c`): writes `rs2` there, nothing else. -/
theorem sd_spec {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32} {rs1 rs2 : Reg} {off : BitVec 12}
    {base c : Nat} (hc : CodeAt image pc [w]) (hpc : s.pc = pc)
    (hdec : decodeInstruction w = some (.base (.SD rs1 rs2 off))) (hoff : signExtend12 off = BitVec.ofNat 64 c)
    (h1 : s.getReg rs1 = BitVec.ofNat 64 base) (hal : (base + c) % 8 = 0) (hlt : base + c + 8 ≤ 2 ^ 24) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getMem (BitVec.ofNat 64 (base + c)) = s.getReg rs2 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = base + c) := by
  have ha : s.getReg rs1 + signExtend12 off = BitVec.ofNat 64 (base + c) := by rw [h1, hoff, ofNat_add_ofNat]
  have hv : accessValid (s.getReg rs1 + signExtend12 off) 8 = true := by
    rw [ha]; simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show base + c < 2 ^ 64 by omega)]; omega
  have st := steps_sd hc hpc hdec hv
  rw [ha] at st
  refine ⟨_, st, by rw [hpc]; rfl, ?_, fun r _ => by simp only [getReg_setPC']; rfl, ?_⟩
  · simp only [getMem_setPC']
    rw [getMem_setMem_ofNat _ _ _ _ (by omega) (by omega), if_pos rfl]
  · intro A hA hn
    simp only [getMem_setPC']
    rw [getMem_setMem_ofNat _ _ _ _ (by omega) hA, if_neg hn]
sym_block e2Run := symRun { noAlias := true } kE2 0 10
theorem run_e2 (pc : Word) : symRun { noAlias := true } kE2 pc 10 =
    some ⟨e2Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
theorem e2_spec {image : Image} {pc : Word} (hc : CodeAt image pc kE2) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x20 = 0 ∧ t.getReg .x21 = BitVec.ofNat 64 12 ∧
      RegsExcept s t [.x20, .x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_e2 pc) hc s hpc (by simp [e2Run.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [rv_simp]
  · simp only [rv_simp, e2Run.res] <;> rfl
  · simp only [rv_simp, e2Run.res] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [e2Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [e2Run.res, rv_simp]
sym_block g0bRun := symRun { noAlias := true } kG0b 0 10
theorem run_g0b (pc : Word) : symRun { noAlias := true } kG0b pc 10 =
    some ⟨g0bRun.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl
theorem g0b_spec {image : Image} {pc : Word} (hc : CodeAt image pc kG0b) (s : MachineState) (hpc : s.pc = pc)
    {f : Nat} (hf : f < 473) (h25 : s.getReg .x25 = BitVec.ofNat 64 (tEntry f)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x25 = BitVec.ofNat 64 (tEntry f + 4 * eD f) ∧
      RegsExcept s t [.x25, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_g0b pc) hc s hpc (by simp [g0bRun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [g0bRun.res, rv_simp]
  · have he := tEntry_lt f hf
    simp only [rv_simp, g0bRun.res, h25, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [bv_shr _ _ (by omega), bv_and_ofNat _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num),
      e_d0 f hf, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [g0bRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [g0bRun.res, rv_simp]
sym_block r7aRun := symRun { noAlias := true } kR7a 0 10
theorem run_r7a (pc : Word) : symRun { noAlias := true } kR7a pc 10 =
    some ⟨r7aRun.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl
theorem r7a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kR7a) (s : MachineState) (hpc : s.pc = pc)
    (v : Digest) (h6 : s.getReg .x6 = v.extractLsb' 0 64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧
      t.getReg .x28 = BitVec.ofNat 64 (4 * (v.toNat / 2 ^ 56 % 128)) ∧
      t.getReg .x29 = (if v.toNat / 2 ^ 56 % 128 < 79 then 1 else 0) ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hx : (s.getReg .x6 >>> 54) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) =
      BitVec.ofNat 64 (4 * (v.toNat / 2 ^ 56 % 128)) := by
    rw [h6, shr_and_mul4 _ 54 7 (by norm_num), lo_field v (54 + 2) 7 (by norm_num)]; norm_num
  have hlt : 4 * (v.toNat / 2 ^ 56 % 128) < 2 ^ 64 := by omega
  refine ⟨_, symRun_sound (run_r7a pc) hc s hpc (by simp [r7aRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [r7aRun.res, rv_simp]
  · simp only [rv_simp, r7aRun.res]
    exact hx
  · simp only [rv_simp, r7aRun.res]
    change (if (((s.getReg .x6 >>> 54) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)))).ult (BitVec.ofNat 64 316) then
      (1 : Word) else 0) = _
    rw [hx, bv_ult _ _ hlt (by norm_num)]
    by_cases h : v.toNat / 2 ^ 56 % 128 < 79
    · rw [if_pos (by simp; omega), if_pos h]; rfl
    · rw [if_neg (by simp; omega), if_neg h]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [r7aRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [r7aRun.res, rv_simp]
theorem run_brR7 (pc : Word) : symRun { noAlias := true } kR7b pc 10 =
    some ⟨SymState.init, .ite .ne (.reg .x29) (.c 0) (.c (pc + BitVec.ofNat 64 304)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
sym_block t5Run := symRun { noAlias := true } kT5 0 10
theorem run_t5 (pc : Word) : symRun { noAlias := true } kT5 pc 10 =
    some ⟨t5Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl
theorem t5_spec {image : Image} {pc : Word} (hc : CodeAt image pc kT5) (s : MachineState) (hpc : s.pc = pc)
    (v : Digest) (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧
      t.getReg .x30 = BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_t5 pc) hc s hpc (by simp [t5Run.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [t5Run.res, rv_simp]
  · simp only [rv_simp, t5Run.res, h6, h7, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact t5_val v
  · intro r hr; simp at hr; cases r <;> simp_all [t5Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [t5Run.res, rv_simp]
sym_block totRun := symRun { noAlias := true } kTot 0 10
theorem run_tot (pc : Word) : symRun { noAlias := true } kTot pc 10 =
    some ⟨totRun.res.st, .c (pc + 4 + 4 + 4 + 4 + 4 + 4), .endOfCode, 6, 6⟩ := by rfl
theorem tot_spec {image : Image} {pc : Word} (hc : CodeAt image pc kTot) (s : MachineState) (hpc : s.pc = pc)
    {S A : Nat} (hSA : S + A < 2 ^ 64) (h25 : s.getReg .x25 = BitVec.ofNat 64 S)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 A) (h17 : s.getReg .x17 = BitVec.ofNat 64 152) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 + 4 ∧
      t.getReg .x25 = BitVec.ofNat 64 (S + A) ∧ t.getReg .x11 = BitVec.ofNat 64 (A / 2 ^ 18 % 16) ∧
      t.getReg .x28 = BitVec.ofNat 64 152 - BitVec.ofNat 64 ((S + A) / 2 ^ 22) ∧
      t.getReg .x29 = (if (BitVec.ofNat 64 152 - BitVec.ofNat 64 ((S + A) / 2 ^ 22)).ult (BitVec.ofNat 64 6)
        then 1 else 0) ∧
      RegsExcept s t [.x11, .x25, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hA : A < 2 ^ 64 := by omega
  refine ⟨_, symRun_sound (run_tot pc) hc s hpc (by simp [totRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [totRun.res, rv_simp]
  · simp only [rv_simp, totRun.res, h25, h11, ofNat_add_ofNat]
  · simp only [rv_simp, totRun.res, h11, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [bv_shr _ _ hA, bv_and_ofNat _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) hA) (by norm_num),
      show (15 : Nat) = 2 ^ 4 - 1 from rfl, land_mask]
    norm_num
  · simp only [rv_simp, totRun.res, h25, h11, h17, ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    rw [bv_shr _ _ hSA]
    norm_num
  · simp only [rv_simp, totRun.res, h25, h11, h17, ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    rw [bv_shr _ _ hSA]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [totRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [totRun.res, rv_simp]
sym_block h2aRun := symRun { noAlias := true } kH2a 0 10
theorem run_h2a (pc : Word) : symRun { noAlias := true } kH2a pc 10 =
    some ⟨h2aRun.res.st, .c (pc + 4 + 4 + 4 + 4 + 4), .endOfCode, 5, 5⟩ := by rfl
theorem h2a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kH2a) (s : MachineState) (hpc : s.pc = pc)
    {S d : Nat} (hS : S < 2 ^ 64) (hd : d < 2 ^ 64) (h25 : s.getReg .x25 = BitVec.ofNat 64 S)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 d) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 ∧
      t.getReg .x29 = (if S / 2 ^ 8 % 64 + (if d = 0 then 1 else 0) < 8 then 1 else 0) ∧
      RegsExcept s t [.x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_h2a pc) hc s hpc (by simp [h2aRun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [h2aRun.res, rv_simp]
  · simp only [rv_simp, h2aRun.res, h25, h28, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [bv_shr _ _ hS, bv_and_ofNat _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) hS) (by norm_num),
      show (63 : Nat) = 2 ^ 6 - 1 from rfl, land_mask, bv_ult _ _ hd (by norm_num)]
    by_cases h0 : d = 0
    · simp only [h0, show (0 : Nat) < 1 by norm_num, decide_true, if_true, ofNat_add_ofNat]
      rw [bv_ult _ _ (by omega) (by norm_num)]
      simp
    · simp only [h0, show ¬ d < 1 by omega, decide_false, if_false, Bool.false_eq_true, BitVec.add_zero]
      rw [bv_ult _ _ (by omega) (by norm_num)]
      simp
  · intro r hr; simp at hr; cases r <;> simp_all [h2aRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [h2aRun.res, rv_simp]
theorem bv_eq4 (d : Nat) (hd : d < 2 ^ 63) :
    (BitVec.ofNat 64 d - 4#64).ult 1#64 = decide (d = 4) := by
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)]
  by_cases h : d = 4
  · subst h; decide
  · simp only [h, decide_false, decide_eq_false_iff_not]
    omega
sym_block h3aRun := symRun { noAlias := true } kH3a 0 10
theorem run_h3a (pc : Word) : symRun { noAlias := true } kH3a pc 10 =
    some ⟨h3aRun.res.st, .c (pc + 4 + 4 + 4 + 4 + 4), .endOfCode, 5, 5⟩ := by rfl
theorem h3a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kH3a) (s : MachineState) (hpc : s.pc = pc)
    {S P d : Nat} (hS : S < 2 ^ 64) (hd : d < 2 ^ 63) (h25 : s.getReg .x25 = BitVec.ofNat 64 S)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 P) (h28 : s.getReg .x28 = BitVec.ofNat 64 d) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 ∧
      t.getReg .x29 = BitVec.ofNat 64 (S % 256 + (if d = 4 then 1 else 0)) - BitVec.ofNat 64 P ∧
      RegsExcept s t [.x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_h3a pc) hc s hpc (by simp [h3aRun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [h3aRun.res, rv_simp]
  · simp only [rv_simp, h3aRun.res, h25, h11, h28]
    rw [show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl, bv_and_mask _ 8 (by norm_num),
      toNat_ofNat_lt hS]
    change BitVec.ofNat 64 (S % 2 ^ 8) - BitVec.ofNat 64 P +
      (if (BitVec.ofNat 64 d - 4#64).ult 1#64 then 1#64 else 0#64) = _
    rw [bv_eq4 d hd]
    by_cases h4 : d = 4
    · simp only [h4, decide_true, if_true]
      rw [show S % 256 + 1 = S % 2 ^ 8 + 1 by norm_num, ← ofNat_add_ofNat (S % 2 ^ 8) 1]
      ring
    · simp only [h4, decide_false, if_false, Bool.false_eq_true]
      simp
  · intro r hr; simp at hr; cases r <;> simp_all [h3aRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [h3aRun.res, rv_simp]
theorem run_br101 (pc : Word) : symRun { noAlias := true } kBr101 pc 10 =
    some ⟨SymState.init, .ite .eq (.reg .x29) (.c 0) (.c (pc + BitVec.ofNat 64 76)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
theorem run_br107 (pc : Word) : symRun { noAlias := true } kBr107 pc 10 =
    some ⟨SymState.init, .ite .eq (.reg .x29) (.c 0) (.c (pc + BitVec.ofNat 64 52)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
theorem run_br113 (pc : Word) : symRun { noAlias := true } kBr113 pc 10 =
    some ⟨SymState.init, .ite .lt (.reg .x29) (.reg .x21) (.c (pc + BitVec.ofNat 64 28)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
theorem run_brA0 (pc : Word) : symRun { noAlias := true } kBrA0 pc 10 =
    some ⟨SymState.init, .ite .ne (.reg .x20) (.c 0) (.c (pc + BitVec.ofNat 64 8)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
theorem run_brF0 (pc : Word) : symRun { noAlias := true } kBrF0 pc 10 =
    some ⟨SymState.init, .ite .ne (.reg .x20) (.c 0) (.c (pc + BitVec.ofNat 64 32)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
theorem run_br122 (pc : Word) : symRun { noAlias := true } kBr122 pc 10 =
    some ⟨SymState.init, .ite .eq (.reg .x29) (.c 0) (.c (pc + BitVec.ofNat 64 24)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
theorem run_j127 (pc : Word) : symRun { noAlias := true } kJ127 pc 10 =
    some ⟨SymState.init, .c (pc + BitVec.ofNat 64 18446744073709551124), .jump, 1, 1⟩ := by
  rfl
theorem run_a1 (pc : Word) : symRun { noAlias := true } kA1 pc 10 =
    some ⟨⟨{ RegFile.init with r29 := .bin .add (.reg .x29) (.c 2) }, [], []⟩, .c (pc + 4), .endOfCode, 1, 1⟩ := by
  rfl
theorem a1_spec {image : Image} {pc : Word} (hc : CodeAt image pc kA1) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x29 = s.getReg .x29 + 2 ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_a1 pc) hc s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [rv_simp]
  · simp only [rv_simp] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [rv_simp, RegFile.init] <;> rfl
  · intro A _ _; simp [rv_simp]
theorem run_luiT5 (pc : Word) : symRun { noAlias := true } kLuiT5 pc 10 =
    some ⟨⟨{ RegFile.init with r30 := .c 0x66000 }, [], []⟩, .c (pc + 4), .endOfCode, 1, 1⟩ := by
  rfl
theorem luiT5_spec {image : Image} {pc : Word} (hc : CodeAt image pc kLuiT5) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x30 = BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_luiT5 pc) hc s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [rv_simp]
  · simp only [rv_simp] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [rv_simp, RegFile.init] <;> rfl
  · intro A _ _; simp [rv_simp]
theorem run_f1a (pc : Word) : symRun { noAlias := true } kF1a pc 10 =
    some ⟨⟨{ RegFile.init with r29 := .bin .srl (.reg .x7) (.c 62) }, [], []⟩, .c (pc + 4), .endOfCode, 1, 1⟩ := by
  rfl
theorem f1a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kF1a) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x29 = s.getReg .x7 >>> 62 ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_f1a pc) hc s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [rv_simp]
  · simp only [rv_simp] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [rv_simp, RegFile.init] <;> rfl
  · intro A _ _; simp [rv_simp]
sym_block f2aRun := symRun { noAlias := true } kF2a 0 10
theorem run_f2a (pc : Word) : symRun { noAlias := true } kF2a pc 10 =
    some ⟨f2aRun.res.st, .c (pc + 4 + 4 + 4 + 4), .endOfCode, 4, 4⟩ := by rfl
theorem f2a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kF2a) (s : MachineState) (hpc : s.pc = pc)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 EOUT) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pc + 4 + 4 + 4 + 4 ∧
      t.getReg .x6 = s.getMem (BitVec.ofNat 64 (EOUT + 16)) ∧ t.getReg .x7 = s.getMem (BitVec.ofNat 64 (EOUT + 24)) ∧
      t.getReg .x20 = BitVec.ofNat 64 128 ∧ t.getReg .x21 = BitVec.ofNat 64 14 ∧
      RegsExcept s t [.x6, .x7, .x20, .x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_f2a pc) hc s hpc
    (by simp only [rv_simp, f2aRun.res, h12, EOUT, accessValid_iff, MEMORY_BYTES]; decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rv_simp]
  · simp only [rv_simp, f2aRun.res, h12] <;> rfl
  · simp only [rv_simp, f2aRun.res, h12] <;> rfl
  · simp only [rv_simp, f2aRun.res] <;> rfl
  · simp only [rv_simp, f2aRun.res] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [f2aRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [f2aRun.res, rv_simp]
end SigGolfCandidate.T3M.Search.T51
end

/-! ## T51 top-trial kernel: the 17 lookups, the half test, the trial (campaign T51, stream SIGNA) -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
abbrev KL : List Reg := [.x11, .x25, .x28, .x29, .x30]
theorem hi_field (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (v.extractLsb' 64 64).toNat / 2 ^ S % 2 ^ w = v.toNat / 2 ^ (64 + S) % 2 ^ w := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, show i + S < 64 by omega]
    congr 1; omega
  · simp [hi]
/-- Three-instruction lookup tail with accumulation, relative to the half-test start state `s0`. -/
theorem lookR3 {image : Image} {s0 s : MachineState} {k : Nat} {w2 w3 w4 : BitVec 32}
    {i2 i3 i4 : Instruction} {acc : Reg} {off : Word}
    (hc : CodeAt image (pcOf k) [w2, w3, w4]) (hpc : s.pc = pcOf k) (hk : 0x1000 + 4 * (k + 3) < 2 ^ 64)
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i2 + (instructionCycles i3 + (instructionCycles i4 + 0)) = 3)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29)
    {L : List Reg} (hL : .x28 ∈ L ∧ .x29 ∈ L ∧ acc ∈ L) (h10L : .x10 ∉ L)
    (hR : RegsExcept s0 s L) (hF : Frame s0 s (fun _ => False))
    {blk r f n : Nat} (ht : T51TableW blk s0) (hblk : blk % 8 = 0) (hb : blk + 1896 < 2 ^ 24) (hf : f < 473)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (blk + 160)) (h28 : s.getReg .x28 = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f))
    (hn : s.getReg acc = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (k + 3) ∧ RegsExcept s0 t L ∧ Frame s0 t (fun _ => False) ∧
      t.getReg acc = BitVec.ofNat 64 (n + tEntry f) ∧ RegsExcept s t [.x28, .x29, acc] := by
  have ht' : T51TableW blk s := ht.frame hF hblk (by omega) (fun _ _ h => h)
  have h10' : s.getReg .x10 = BitVec.ofNat 64 (blk + 160) := (hR .x10 h10L).trans h10
  have haddr : s.getReg .x28 + s.getReg .x10 + off = BitVec.ofNat 64 (blk + 4 * f) := by rw [h28, h10', hoff]
  have hv : accessValid (s.getReg .x28 + s.getReg .x10 + off) 4 = true := by
    rw [haddr]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show blk + 4 * f < 2 ^ 64 by omega)]
    omega
  obtain ⟨t, st, pt, _, gacc, rt, ft⟩ := look3 hc hpc hd2 hc2 hd3 hc3 hd4 hc4 hcy hacc hv
  have hw : (s.getWord32 (BitVec.ofNat 64 (blk + 4 * f))).zeroExtend 64 = BitVec.ofNat 64 (tEntry f) := by
    rw [ht' f hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
    have := tEntry_lt f hf
    have h64 : tEntry f < 2 ^ 64 := by omega
    simp only [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h64]
  refine ⟨t, st, ?_, ?_, ?_, ?_, rt⟩
  · rw [pt, hpc, show (12 : Word) = BitVec.ofNat 64 (4 * 3) from rfl, pcOf_plus _ _ hk]
  · refine (hR.trans rt).mono ?_
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq | hq
    · exact hq
    · exact hq ▸ hL.1
    · exact hq ▸ hL.2.1
    · exact hq ▸ hL.2.2
  · exact (hF.trans ft).mono (fun _ _ h => by simpa using h)
  · rw [gacc, haddr, hw, hn, ofNat_add_ofNat]
/-- Kernel value of `s9` after the r6 groups g0..g6 (machine order). -/
def kA (v : Digest) : Nat :=
  tEntry (gIdx v 0) + 4 * eD (gIdx v 0) + tEntry (gIdx v 1) + tEntry (gIdx v 2) + tEntry (gIdx v 3) +
    tEntry (gIdx v 4) + tEntry (gIdx v 5) + tEntry (gIdx v 6)
/-- Kernel value of `s9` before the penalty merge (machine order) and of `a1` (penalty groups q10..q12). -/
def kS9 (v : Digest) : Nat :=
  kA v + tEntry (gIdx v 16) + tEntry (gIdx v 9) + tEntry (gIdx v 13) + tEntry (gIdx v 14) + tEntry (gIdx v 15) +
    tEntry (gIdx v 7) + tEntry (gIdx v 8)
def kPen (v : Digest) : Nat := tEntry (gIdx v 10) + tEntry (gIdx v 11) + tEntry (gIdx v 12)
/-- Lookups g0..g6 and the r7 range test (kernel offsets 4..43). -/
theorem h1a_run {image : Image} {P : KInst} (hK : T51KAt image P) (s0 s : MachineState)
    (hpc : s.pc = pcOf (P.kb + 4)) (v : Digest)
    (h6 : s0.getReg .x6 = v.extractLsb' 0 64)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (P.blk + 160)) (ht : T51TableW P.blk s0)
    (hR0 : RegsExcept s0 s KL) (hF0 : Frame s0 s (fun _ => False)) :
    ∃ t, Steps image s 40 40 t ∧ t.pc = pcOf (P.kb + 44) ∧
      t.getReg .x25 = BitVec.ofNat 64 (kA v) ∧
      t.getReg .x28 = BitVec.ofNat 64 (4 * (v.toNat / 2 ^ 56 % 128)) ∧
      t.getReg .x29 = (if v.toNat / 2 ^ 56 % 128 < 79 then 1 else 0) ∧
      RegsExcept s0 t KL ∧ Frame s0 t (fun _ => False) := by
  have hblk := hK.blk8
  have hbb := hK.blkLt
  have hkb := hK.kbLt
  have hvl : v.toNat < 2 ^ 128 := v.isLt
  obtain ⟨t1, s1, p1, R1, F1, a25_1, x1⟩ := lookW (s0 := s0) (k := P.kb + 4) (src := .x6) (rd := .x25) (codeAt_kf hK 2 rfl) hpc (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) hR0 hF0 ht hblk hbb
    (r := v.toNat % 256) (f := gIdx v 0) (gIdx_lt v 0) h10
    (by change (s.getReg .x6 <<< 2) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [(hR0 .x6 (by decide)).trans h6, shl2_and_mul4 _ 8 (by norm_num), lo_mod v 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 18446744073709551456 = BitVec.ofNat 64 (P.blk + 4 * (v.toNat % 256))
        exact hoff_eq (by omega))
  obtain ⟨t2, s2, p2, a25_2, x2, f2⟩ := g0b_spec (codeAt_kf hK 3 rfl) t1 (by rw [p1]) (gIdx_lt v 0) a25_1
  have R2 : RegsExcept s0 t2 KL := (R1.trans x2).mono (by decide)
  have F2 : Frame s0 t2 (fun _ => False) := (F1.trans f2).mono (fun _ _ h => by simpa using h)
  have p2' : t2.pc = pcOf (P.kb + 11) := by rw [p2, pcOf_3]
  obtain ⟨t3, s3, p3, R3, F3, g3, x3⟩ := lookR (s0 := s0) (k := P.kb + 11) (src := .x6) (acc := .x25) (codeAt_kf hK 4 rfl) p2' (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R2 F2 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 1) % 256) (f := gIdx v 1) (gIdx_lt v 1) h10
    (by change (t2.getReg .x6 >>> 6) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R2 .x6 (by decide)).trans h6), shr_and_mul4 _ 6 8 (by norm_num), lo_field v (6 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ (8 * 1) % 256))
        exact hoff_eq (by omega))
    a25_2
  obtain ⟨t4, s4, p4, R4, F4, g4, x4⟩ := lookR (s0 := s0) (k := P.kb + 16) (src := .x6) (acc := .x25) (codeAt_kf hK 5 rfl) p3 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R3 F3 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 2) % 256) (f := gIdx v 2) (gIdx_lt v 2) h10
    (by change (t3.getReg .x6 >>> 14) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R3 .x6 (by decide)).trans h6), shr_and_mul4 _ 14 8 (by norm_num), lo_field v (14 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ (8 * 2) % 256))
        exact hoff_eq (by omega))
    g3
  obtain ⟨t5, s5, p5, R5, F5, g5, x5⟩ := lookR (s0 := s0) (k := P.kb + 21) (src := .x6) (acc := .x25) (codeAt_kf hK 6 rfl) p4 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R4 F4 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 3) % 256) (f := gIdx v 3) (gIdx_lt v 3) h10
    (by change (t4.getReg .x6 >>> 22) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R4 .x6 (by decide)).trans h6), shr_and_mul4 _ 22 8 (by norm_num), lo_field v (22 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ (8 * 3) % 256))
        exact hoff_eq (by omega))
    g4
  obtain ⟨t6, s6, p6, R6, F6, g6, x6⟩ := lookR (s0 := s0) (k := P.kb + 26) (src := .x6) (acc := .x25) (codeAt_kf hK 7 rfl) p5 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R5 F5 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 4) % 256) (f := gIdx v 4) (gIdx_lt v 4) h10
    (by change (t5.getReg .x6 >>> 30) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R5 .x6 (by decide)).trans h6), shr_and_mul4 _ 30 8 (by norm_num), lo_field v (30 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ (8 * 4) % 256))
        exact hoff_eq (by omega))
    g5
  obtain ⟨t7, s7, p7, R7, F7, g7, x7⟩ := lookR (s0 := s0) (k := P.kb + 31) (src := .x6) (acc := .x25) (codeAt_kf hK 8 rfl) p6 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R6 F6 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 5) % 256) (f := gIdx v 5) (gIdx_lt v 5) h10
    (by change (t6.getReg .x6 >>> 38) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R6 .x6 (by decide)).trans h6), shr_and_mul4 _ 38 8 (by norm_num), lo_field v (38 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ (8 * 5) % 256))
        exact hoff_eq (by omega))
    g6
  obtain ⟨t8, s8, p8, R8, F8, g8, x8⟩ := lookR (s0 := s0) (k := P.kb + 36) (src := .x6) (acc := .x25) (codeAt_kf hK 9 rfl) p7 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R7 F7 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 6) % 256) (f := gIdx v 6) (gIdx_lt v 6) h10
    (by change (t7.getReg .x6 >>> 46) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R7 .x6 (by decide)).trans h6), shr_and_mul4 _ 46 8 (by norm_num), lo_field v (46 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ (8 * 6) % 256))
        exact hoff_eq (by omega))
    g7
  obtain ⟨t9, s9, p9, x28_9, x29_9, r9, f9⟩ := r7a_spec (codeAt_kf hK 10 rfl) t8 (by rw [p8]) v ((R8 .x6 (by decide)).trans h6)
  refine ⟨t9, ((((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9).of_eq rfl rfl,
    by rw [p9, pcOf_3], ?_, x28_9, x29_9, (R8.trans r9).mono (by decide),
    (F8.trans f9).mono (fun _ _ h => by simpa using h)⟩
  rw [r9 .x25 (by decide), g8]
  rfl
/-- The r7 lookup and the lookups t5, q9..q15, g7, g8 (kernel offsets 45..94), for a valid r7 field. -/
theorem h1b_run {image : Image} {P : KInst} (hK : T51KAt image P) (s0 s : MachineState)
    (hpc : s.pc = pcOf (P.kb + 45)) (v : Digest)
    (h6 : s0.getReg .x6 = v.extractLsb' 0 64) (h7 : s0.getReg .x7 = v.extractLsb' 64 64)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (P.blk + 160)) (ht : T51TableW P.blk s0)
    (hR0 : RegsExcept s0 s KL) (hF0 : Frame s0 s (fun _ => False))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (kA v)) (h28 : s.getReg .x28 = BitVec.ofNat 64 (4 * (v.toNat / 2 ^ 56 % 128))) :
    ∃ t, Steps image s 50 50 t ∧ t.pc = pcOf (P.kb + 95) ∧
      t.getReg .x25 = BitVec.ofNat 64 (kS9 v) ∧ t.getReg .x11 = BitVec.ofNat 64 (kPen v) ∧
      RegsExcept s0 t KL ∧ Frame s0 t (fun _ => False) := by
  have hblk := hK.blk8
  have hbb := hK.blkLt
  have hkb := hK.kbLt
  have hvl : v.toNat < 2 ^ 128 := v.isLt
  obtain ⟨t1, s1, p1, R1, F1, g1, x1⟩ := lookR3 (s0 := s0) (k := P.kb + 45) (acc := .x25) (codeAt_kf hK 12 rfl) hpc (by omega)
    rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) hR0 hF0 ht hblk hbb
    (r := v.toNat / 2 ^ 56 % 128) (f := gIdx v 16) (gIdx_lt v 16) h10 h28
    (by change _ + _ + BitVec.ofNat 64 1220 = BitVec.ofNat 64 (P.blk + 4 * (345 + v.toNat / 2 ^ 56 % 128))
        exact hoff_eq (by omega))
    h25
  obtain ⟨t2, s2, p2, a30_2, x2, f2⟩ := t5_spec (codeAt_kf hK 13 rfl) t1 (by rw [p1]) v
    ((R1 .x6 (by decide)).trans h6) ((R1 .x7 (by decide)).trans h7)
  have R2 : RegsExcept s0 t2 KL := (R1.trans x2).mono (by decide)
  have F2 : Frame s0 t2 (fun _ => False) := (F1.trans f2).mono (fun _ _ h => by simpa using h)
  have p2' : t2.pc = pcOf (P.kb + 51) := by rw [p2, pcOf_3]
  have a25_2 : t2.getReg .x25 = _ := (x2 .x25 (by decide)).trans g1
  obtain ⟨t3, s3, p3, R3, F3, g3, x3⟩ := lookR (s0 := s0) (k := P.kb + 51) (src := .x30) (acc := .x25) (codeAt_kf hK 14 rfl) p2' (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R2 F2 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 9) % 128) (f := gIdx v 9) (gIdx_lt v 9) h10
    (by change (t2.getReg .x30 <<< 2) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_2, shl2_and_mul4 _ 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_mod v 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (P.blk + 4 * (296 + v.toNat / 2 ^ (7 * 9) % 128))
        exact hoff_eq (by omega))
    a25_2
  have a30_3 : t3.getReg .x30 = _ := (x3 .x30 (by decide)).trans a30_2
  obtain ⟨t4, s4, p4, R4, F4, a11_4, x4⟩ := lookW (s0 := s0) (k := P.kb + 56) (src := .x30) (rd := .x11) (codeAt_kf hK 15 rfl) p3 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R3 F3 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 10) % 128) (f := gIdx v 10) (gIdx_lt v 10) h10
    (by change (t3.getReg .x30 >>> 5) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_3, shr_and_mul4 _ 5 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (5 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (P.blk + 4 * (296 + v.toNat / 2 ^ (7 * 10) % 128))
        exact hoff_eq (by omega))
  have a25_4 : t4.getReg .x25 = _ := (x4 .x25 (by decide)).trans g3
  have a30_4 : t4.getReg .x30 = _ := (x4 .x30 (by decide)).trans a30_3
  obtain ⟨t5, s5, p5, R5, F5, g5, x5⟩ := lookR (s0 := s0) (k := P.kb + 60) (src := .x30) (acc := .x11) (codeAt_kf hK 16 rfl) p4 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R4 F4 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 11) % 128) (f := gIdx v 11) (gIdx_lt v 11) h10
    (by change (t4.getReg .x30 >>> 12) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_4, shr_and_mul4 _ 12 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (12 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (P.blk + 4 * (296 + v.toNat / 2 ^ (7 * 11) % 128))
        exact hoff_eq (by omega))
    a11_4
  have a25_5 : t5.getReg .x25 = _ := (x5 .x25 (by decide)).trans a25_4
  have a30_5 : t5.getReg .x30 = _ := (x5 .x30 (by decide)).trans a30_4
  obtain ⟨t6, s6, p6, R6, F6, g6, x6⟩ := lookR (s0 := s0) (k := P.kb + 65) (src := .x30) (acc := .x11) (codeAt_kf hK 17 rfl) p5 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R5 F5 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 12) % 128) (f := gIdx v 12) (gIdx_lt v 12) h10
    (by change (t5.getReg .x30 >>> 19) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_5, shr_and_mul4 _ 19 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (19 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (P.blk + 4 * (296 + v.toNat / 2 ^ (7 * 12) % 128))
        exact hoff_eq (by omega))
    g5
  have a25_6 : t6.getReg .x25 = _ := (x6 .x25 (by decide)).trans a25_5
  have a30_6 : t6.getReg .x30 = _ := (x6 .x30 (by decide)).trans a30_5
  obtain ⟨t7, s7, p7, R7, F7, g7, x7⟩ := lookR (s0 := s0) (k := P.kb + 70) (src := .x30) (acc := .x25) (codeAt_kf hK 18 rfl) p6 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R6 F6 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 13) % 128) (f := gIdx v 13) (gIdx_lt v 13) h10
    (by change (t6.getReg .x30 >>> 26) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_6, shr_and_mul4 _ 26 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (26 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (P.blk + 4 * (296 + v.toNat / 2 ^ (7 * 13) % 128))
        exact hoff_eq (by omega))
    a25_6
  have a11_7 : t7.getReg .x11 = _ := (x7 .x11 (by decide)).trans g6
  have a30_7 : t7.getReg .x30 = _ := (x7 .x30 (by decide)).trans a30_6
  obtain ⟨t8, s8, p8, R8, F8, g8, x8⟩ := lookR (s0 := s0) (k := P.kb + 75) (src := .x30) (acc := .x25) (codeAt_kf hK 19 rfl) p7 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R7 F7 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 14) % 128) (f := gIdx v 14) (gIdx_lt v 14) h10
    (by change (t7.getReg .x30 >>> 33) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_7, shr_and_mul4 _ 33 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (33 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (P.blk + 4 * (296 + v.toNat / 2 ^ (7 * 14) % 128))
        exact hoff_eq (by omega))
    g7
  have a11_8 : t8.getReg .x11 = _ := (x8 .x11 (by decide)).trans a11_7
  have a30_8 : t8.getReg .x30 = _ := (x8 .x30 (by decide)).trans a30_7
  obtain ⟨t9, s9, p9, R9, F9, g9, x9⟩ := lookR (s0 := s0) (k := P.kb + 80) (src := .x30) (acc := .x25) (codeAt_kf hK 20 rfl) p8 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R8 F8 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 15) % 128) (f := gIdx v 15) (gIdx_lt v 15) h10
    (by change (t8.getReg .x30 >>> 40) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_8, shr_and_mul4 _ 40 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (40 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (P.blk + 4 * (296 + v.toNat / 2 ^ (7 * 15) % 128))
        exact hoff_eq (by omega))
    g8
  have a11_9 : t9.getReg .x11 = _ := (x9 .x11 (by decide)).trans a11_8
  have a30_9 : t9.getReg .x30 = _ := (x9 .x30 (by decide)).trans a30_8
  obtain ⟨t10, s10, p10, R10, F10, g10, x10⟩ := lookR (s0 := s0) (k := P.kb + 85) (src := .x7) (acc := .x25) (codeAt_kf hK 21 rfl) p9 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R9 F9 ht hblk hbb
    (r := v.toNat / 2 ^ 112 % 256) (f := gIdx v 7) (gIdx_lt v 7) h10
    (by change (t9.getReg .x7 >>> 46) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R9 .x7 (by decide)).trans h7), shr_and_mul4 _ 46 8 (by norm_num), hi_field v (46 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ 112 % 256))
        exact hoff_eq (by omega))
    g9
  have a11_10 : t10.getReg .x11 = _ := (x10 .x11 (by decide)).trans a11_9
  obtain ⟨t11, s11, p11, R11, F11, g11, x11⟩ := lookR (s0 := s0) (k := P.kb + 90) (src := .x7) (acc := .x25) (codeAt_kf hK 22 rfl) p10 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R10 F10 ht hblk hbb
    (r := v.toNat / 2 ^ 120 % 256) (f := gIdx v 8) (gIdx_lt v 8) h10
    (by change (t10.getReg .x7 >>> 54) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R10 .x7 (by decide)).trans h7), shr_and_mul4 _ 54 8 (by norm_num), hi_field v (54 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (P.blk + 4 * (40 + v.toNat / 2 ^ 120 % 256))
        exact hoff_eq (by omega))
    g10
  have a11_11 : t11.getReg .x11 = _ := (x11 .x11 (by decide)).trans a11_10
  refine ⟨t11, ((((((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9).trans s10).trans s11).of_eq rfl rfl, p11, ?_, ?_, R11, F11⟩
  · rw [g11]; rfl
  · rw [a11_11]; rfl
end SigGolfCandidate.T3M.Search.T51
end

/-! ## T51 top-trial kernel: lane arithmetic, the half test, the tails and the trial (campaign T51, stream SIGNA) -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem e_r7P : ∀ f < 473, 424 ≤ f → eP f = 0 := by decide +kernel
theorem gIdx_r6lt (v : Digest) (j : Nat) (hj : j < 9) : gIdx v j < 296 := by
  unfold gIdx; split_ifs <;> omega
theorem gIdx_r5ge (v : Digest) (j : Nat) (hj : 9 ≤ j) : 296 ≤ gIdx v j := by
  unfold gIdx; split_ifs <;> omega
theorem kLanes (v : Digest) (hr7 : 79 ≤ v.toNat / 2 ^ 56 % 128) :
    kS9 v + kPen v = LW v * 2 ^ 22 + LP v * 2 ^ 18 + LD v * 2 ^ 14 + LZ v * 2 ^ 8 + (LS v + 4 * eD (gIdx v 0)) ∧
      LP v ≤ 7 ∧ LD v ≤ 9 ∧ LZ v ≤ 51 ∧ LS v + 4 * eD (gIdx v 0) ≤ 140 ∧ LW v ≤ 4352 ∧
      kPen v / 2 ^ 18 % 16 = LPen v := by
  have H : ∀ j < 17, tEntry (gIdx v j) = eW (gIdx v j) * 2 ^ 22 + eP (gIdx v j) * 2 ^ 18 +
      eD (gIdx v j) * 2 ^ 14 + eZ (gIdx v j) * 2 ^ 8 + eS (gIdx v j) ∧ eW (gIdx v j) ≤ 256 ∧ eP (gIdx v j) ≤ 1 ∧
      eD (gIdx v j) ≤ 1 ∧ eZ (gIdx v j) ≤ 3 ∧ eS (gIdx v j) ≤ 8 := fun j _ => tEntry_lanes _ (gIdx_lt v j)
  have P6 : ∀ j < 9, eP (gIdx v j) = 0 := fun j hj => e_r6P _ (gIdx_r6lt v j hj)
  have P7 : eP (gIdx v 16) = 0 := e_r7P _ (gIdx_lt v 16) (by rw [(gIdx_r7 v).2.1]; omega)
  have D5 : ∀ j, 9 ≤ j → eD (gIdx v j) = 0 := fun j hj => e_r5D _ (gIdx_lt v j) (gIdx_r5ge v j hj)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [kS9, kA, kPen, LW, LP, LD, LZ, LS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [(H 0 (by norm_num)).1, (H 1 (by norm_num)).1, (H 2 (by norm_num)).1, (H 3 (by norm_num)).1, (H 4 (by norm_num)).1, (H 5 (by norm_num)).1, (H 6 (by norm_num)).1, (H 7 (by norm_num)).1, (H 8 (by norm_num)).1, (H 9 (by norm_num)).1, (H 10 (by norm_num)).1, (H 11 (by norm_num)).1, (H 12 (by norm_num)).1, (H 13 (by norm_num)).1, (H 14 (by norm_num)).1, (H 15 (by norm_num)).1, (H 16 (by norm_num)).1]
    ring
  · simp only [LP, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := P6 0 (by norm_num); have := P6 1 (by norm_num); have := P6 2 (by norm_num); have := P6 3 (by norm_num); have := P6 4 (by norm_num); have := P6 5 (by norm_num); have := P6 6 (by norm_num); have := P6 7 (by norm_num); have := P6 8 (by norm_num)
    have := (H 9 (by norm_num)).2.2.1; have := (H 10 (by norm_num)).2.2.1; have := (H 11 (by norm_num)).2.2.1; have := (H 12 (by norm_num)).2.2.1; have := (H 13 (by norm_num)).2.2.1; have := (H 14 (by norm_num)).2.2.1; have := (H 15 (by norm_num)).2.2.1
    omega
  · simp only [LD, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := D5 9 (by norm_num); have := D5 10 (by norm_num); have := D5 11 (by norm_num); have := D5 12 (by norm_num); have := D5 13 (by norm_num); have := D5 14 (by norm_num); have := D5 15 (by norm_num); have := D5 16 (by norm_num)
    have := (H 0 (by norm_num)).2.2.2.1; have := (H 1 (by norm_num)).2.2.2.1; have := (H 2 (by norm_num)).2.2.2.1; have := (H 3 (by norm_num)).2.2.2.1; have := (H 4 (by norm_num)).2.2.2.1; have := (H 5 (by norm_num)).2.2.2.1; have := (H 6 (by norm_num)).2.2.2.1; have := (H 7 (by norm_num)).2.2.2.1; have := (H 8 (by norm_num)).2.2.2.1
    omega
  · simp only [LZ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := (H 0 (by norm_num)).2.2.2.2.1; have := (H 1 (by norm_num)).2.2.2.2.1; have := (H 2 (by norm_num)).2.2.2.2.1; have := (H 3 (by norm_num)).2.2.2.2.1; have := (H 4 (by norm_num)).2.2.2.2.1; have := (H 5 (by norm_num)).2.2.2.2.1; have := (H 6 (by norm_num)).2.2.2.2.1; have := (H 7 (by norm_num)).2.2.2.2.1; have := (H 8 (by norm_num)).2.2.2.2.1; have := (H 9 (by norm_num)).2.2.2.2.1; have := (H 10 (by norm_num)).2.2.2.2.1; have := (H 11 (by norm_num)).2.2.2.2.1; have := (H 12 (by norm_num)).2.2.2.2.1; have := (H 13 (by norm_num)).2.2.2.2.1; have := (H 14 (by norm_num)).2.2.2.2.1; have := (H 15 (by norm_num)).2.2.2.2.1; have := (H 16 (by norm_num)).2.2.2.2.1
    omega
  · simp only [LS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := (H 0 (by norm_num)).2.2.2.1
    have := (H 0 (by norm_num)).2.2.2.2.2; have := (H 1 (by norm_num)).2.2.2.2.2; have := (H 2 (by norm_num)).2.2.2.2.2; have := (H 3 (by norm_num)).2.2.2.2.2; have := (H 4 (by norm_num)).2.2.2.2.2; have := (H 5 (by norm_num)).2.2.2.2.2; have := (H 6 (by norm_num)).2.2.2.2.2; have := (H 7 (by norm_num)).2.2.2.2.2; have := (H 8 (by norm_num)).2.2.2.2.2; have := (H 9 (by norm_num)).2.2.2.2.2; have := (H 10 (by norm_num)).2.2.2.2.2; have := (H 11 (by norm_num)).2.2.2.2.2; have := (H 12 (by norm_num)).2.2.2.2.2; have := (H 13 (by norm_num)).2.2.2.2.2; have := (H 14 (by norm_num)).2.2.2.2.2; have := (H 15 (by norm_num)).2.2.2.2.2; have := (H 16 (by norm_num)).2.2.2.2.2
    omega
  · simp only [LW, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := (H 0 (by norm_num)).2.1; have := (H 1 (by norm_num)).2.1; have := (H 2 (by norm_num)).2.1; have := (H 3 (by norm_num)).2.1; have := (H 4 (by norm_num)).2.1; have := (H 5 (by norm_num)).2.1; have := (H 6 (by norm_num)).2.1; have := (H 7 (by norm_num)).2.1; have := (H 8 (by norm_num)).2.1; have := (H 9 (by norm_num)).2.1; have := (H 10 (by norm_num)).2.1; have := (H 11 (by norm_num)).2.1; have := (H 12 (by norm_num)).2.1; have := (H 13 (by norm_num)).2.1; have := (H 14 (by norm_num)).2.1; have := (H 15 (by norm_num)).2.1; have := (H 16 (by norm_num)).2.1
    omega
  · unfold kPen LPen
    rw [(H 10 (by norm_num)).1, (H 11 (by norm_num)).1, (H 12 (by norm_num)).1]
    obtain ⟨_, _, p10, _, z10, s10⟩ := H 10 (by norm_num); have d10 := D5 10 (by norm_num)
    obtain ⟨_, _, p11, _, z11, s11⟩ := H 11 (by norm_num); have d11 := D5 11 (by norm_num)
    obtain ⟨_, _, p12, _, z12, s12⟩ := H 12 (by norm_num); have d12 := D5 12 (by norm_num)
    omega
theorem kSum_lt (v : Digest) (hr7 : 79 ≤ v.toNat / 2 ^ 56 % 128) : kS9 v + kPen v < 2 ^ 62 := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v hr7; omega
theorem kSum_W (v : Digest) (hr7 : 79 ≤ v.toNat / 2 ^ 56 % 128) : (kS9 v + kPen v) / 2 ^ 22 = LW v := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v hr7; omega
theorem kSum_Z (v : Digest) (hr7 : 79 ≤ v.toNat / 2 ^ 56 % 128) : (kS9 v + kPen v) / 2 ^ 8 % 64 = LZ v := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v hr7; omega
theorem kSum_S (v : Digest) (hr7 : 79 ≤ v.toNat / 2 ^ 56 % 128) :
    (kS9 v + kPen v) % 256 = LS v + 4 * eD (gIdx v 0) := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v hr7; omega
theorem LPen_le (v : Digest) : LPen v ≤ 3 := by
  unfold LPen
  have a := (tEntry_lanes _ (gIdx_lt v 10)).2.2.1; have b := (tEntry_lanes _ (gIdx_lt v 11)).2.2.1
  have c := (tEntry_lanes _ (gIdx_lt v 12)).2.2.1
  omega
/-! ### Branch-condition arithmetic -/
theorem window_bv (W : Nat) (hW : W < 2 ^ 62) :
    (BitVec.ofNat 64 152 - BitVec.ofNat 64 W).ult (BitVec.ofNat 64 6) = decide (W ≤ 152 ∧ 152 - W < 6) := by
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega)]
  by_cases h : W ≤ 152
  · simp only [h, true_and]
    rw [show 2 ^ 64 - W + 152 % 2 ^ 64 = 152 - W + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show 152 - W < 2 ^ 64 by omega)]
  · simp only [h, false_and, decide_false, decide_eq_false_iff_not]
    omega
theorem slt_sub (R P thr : Nat) (hR : R < 2 ^ 62) (hP : P < 2 ^ 62) (ht : thr < 2 ^ 62) :
    (BitVec.ofNat 64 R - BitVec.ofNat 64 P).slt (BitVec.ofNat 64 thr) = decide (R < P + thr) := by
  by_cases h : P ≤ R
  · rw [bv_sub R P h (by omega), ofNat_slt _ _ (by omega) (by omega)]
    simp only [decide_eq_decide]; omega
  · have hneg : (BitVec.ofNat 64 R - BitVec.ofNat 64 P).toInt < 0 := by
      rw [BitVec.toInt_eq_toNat_cond]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show R < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show P < 2 ^ 64 by omega)]
      split_ifs with h1 <;> omega
    have htp : (BitVec.ofNat 64 thr).toInt = thr := by
      rw [BitVec.toInt_eq_toNat_of_msb]; · simp; omega
      rw [BitVec.msb_eq_decide]; simp; omega
    rw [BitVec.slt, htp]
    simp only [decide_eq_decide]
    constructor
    · intro _; omega
    · intro _; omega
theorem pcOf_n (k n m : Nat) (hm : m = 4 * n) (h : 0x1000 + 4 * (k + n) < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 m = pcOf (k + n) := by
  subst hm; exact pcOf_plus k n h
theorem pcOf_m (k n m : Nat) (hm : m = 2 ^ 64 - 4 * n) (hn : n ≤ k) (h : 0x1000 + 4 * k < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 m = pcOf (k - n) := by
  subst hm; exact pcOf_minus k n hn h
end SigGolfCandidate.T3M.Search.T51
end

/-! ## T51 top-trial kernel: the half test, the tails and the trial (campaign T51, stream SIGNA) -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-- The half test from `K_HALF` (`kb + 4`) at threshold `thr` (`x21`): accept at `kb + 114` with the credit
(before the LOW bonus) in `x29` and the checksum digit in `x28`, or reject at `K_FAILH` (`kb + 120`). -/
theorem half_run {image : Image} {P : KInst} (hK : T51KAt image P) (s0 : MachineState)
    (hpc : s0.pc = pcOf (P.kb + 4)) (v : Digest)
    (h6 : s0.getReg .x6 = v.extractLsb' 0 64) (h7 : s0.getReg .x7 = v.extractLsb' 64 64)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (P.blk + 160)) (h17 : s0.getReg .x17 = BitVec.ofNat 64 152)
    {thr : Nat} (hthr : thr < 2 ^ 62) (h21 : s0.getReg .x21 = BitVec.ofNat 64 thr) (ht : T51TableW P.blk s0) :
    ∃ k t, Steps image s0 k k t ∧ k ≤ 110 ∧ RegsExcept s0 t KL ∧ Frame s0 t (fun _ => False) ∧
      ((kAcc v thr ∧ k = 110 ∧ t.pc = pcOf (P.kb + 114) ∧
        t.getReg .x29 = BitVec.ofNat 64 (LS v + 4 * eD (gIdx v 0) + (if 152 - LW v = 4 then 1 else 0) - LPen v) ∧
        t.getReg .x28 = BitVec.ofNat 64 (152 - LW v)) ∨
       (¬ kAcc v thr ∧ t.pc = pcOf (P.kb + 120))) := by
  have hkb := hK.kbLt
  have hFm : ∀ {x y z : MachineState}, Frame x y (fun _ => False) → Frame y z (fun _ => False) →
      Frame x z (fun _ => False) := fun h1 h2 => (h1.trans h2).mono (fun _ _ h => by simpa using h)
  obtain ⟨u1, s1, p1, a25, a28, a29, r1, f1⟩ :=
    h1a_run hK s0 s0 hpc v h6 h10 ht (RegsExcept.refl _ _) (Frame.refl _ _)
  obtain ⟨u2, s2, p2, r2, f2⟩ := br_spec (run_brR7 _) (codeAt_kf hK 11 rfl) u1 p1
  simp only [E.eval, CmpOp.eval, a29] at p2
  have r2' : RegsExcept s0 u2 KL := (r1.trans r2).mono (by decide)
  have f2' := hFm f1 f2
  by_cases hr7 : v.toNat / 2 ^ 56 % 128 < 79
  · refine ⟨41, u2, (s1.trans s2).of_eq rfl rfl, by norm_num, r2', f2',
      Or.inr ⟨fun h => by unfold kAcc at h; omega, ?_⟩⟩
    rw [p2, if_pos hr7, if_pos (by decide), pcOf_n _ 76 _ rfl (by omega)]
  have hr7' : 79 ≤ v.toNat / 2 ^ 56 % 128 := by omega
  have p2' : u2.pc = pcOf (P.kb + 45) := by
    rw [p2, if_neg hr7, if_neg (by decide), pcOf_4]
  obtain ⟨u3, s3, p3, b25, b11, r3, f3⟩ := h1b_run hK s0 u2 p2' v h6 h7 h10 ht r2' f2'
    (by rw [r2 .x25 (by decide), a25]) (by rw [r2 .x28 (by decide), a28])
  have x17 : u3.getReg .x17 = BitVec.ofNat 64 152 := (r3 .x17 (by decide)).trans h17
  have hK2 := kSum_lt v hr7'
  obtain ⟨u4, s4, p4, c25, c11, c28, c29, r4, f4⟩ :=
    tot_spec (codeAt_kf hK 23 rfl) u3 p3 (by omega) b25 b11 x17
  rw [kSum_W v hr7'] at c28 c29
  rw [window_bv _ (by have := (kLanes v hr7').2.2.2.2.2.1; omega)] at c29
  rw [(kLanes v hr7').2.2.2.2.2.2] at c11
  have r4' : RegsExcept s0 u4 KL := (r3.trans r4).mono (by decide)
  have f4' := hFm f3 f4
  have p4' : u4.pc = pcOf (P.kb + 101) := by rw [p4]; simp only [pcOf_4]
  obtain ⟨u5, s5, p5, r5, f5⟩ := br_spec (run_br101 _) (codeAt_kf hK 24 rfl) u4 p4'
  simp only [E.eval, CmpOp.eval, c29] at p5
  have r5' : RegsExcept s0 u5 KL := (r4'.trans r5).mono (by decide)
  have f5' := hFm f4' f5
  by_cases hw : LW v ≤ 152 ∧ 152 - LW v < 6
  swap
  · refine ⟨98, u5, ((((s1.trans s2).trans s3).trans s4).trans s5).of_eq rfl rfl, by norm_num, r5', f5',
      Or.inr ⟨fun h => hw ⟨h.2.1, h.2.2.1⟩, ?_⟩⟩
    rw [p5]
    simp only [hw, decide_false, Bool.false_eq_true, if_false]
    rw [if_pos (by decide), pcOf_n _ 19 _ rfl (by omega)]
  have p5' : u5.pc = pcOf (P.kb + 102) := by
    rw [p5]; simp only [hw, and_self, decide_true, if_true]; rw [if_neg (by decide), pcOf_4]
  have hd : 152 - LW v < 6 := hw.2
  have d28 : u5.getReg .x28 = BitVec.ofNat 64 (152 - LW v) := by
    rw [r5 .x28 (by decide), c28, bv_sub _ _ hw.1 (by norm_num)]
  have d25 : u5.getReg .x25 = BitVec.ofNat 64 (kS9 v + kPen v) := by rw [r5 .x25 (by decide), c25]
  have d11 : u5.getReg .x11 = BitVec.ofNat 64 (LPen v) := by rw [r5 .x11 (by decide), c11]
  obtain ⟨u6, s6, p6, e29, r6, f6⟩ := h2a_spec (codeAt_kf hK 25 rfl) u5 p5' (by omega) (by omega) d25 d28
  rw [kSum_Z v hr7'] at e29
  have p6' : u6.pc = pcOf (P.kb + 107) := by rw [p6]; simp only [pcOf_4]
  obtain ⟨u7, s7, p7, r7, f7⟩ := br_spec (run_br107 _) (codeAt_kf hK 26 rfl) u6 p6'
  simp only [E.eval, CmpOp.eval, e29] at p7
  have r7' : RegsExcept s0 u7 KL := ((r5'.trans r6).trans r7).mono (by decide)
  have f7' := hFm (hFm f5' f6) f7
  by_cases hz : LZ v + (if 152 - LW v = 0 then 1 else 0) < 8
  swap
  · refine ⟨104, u7, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).of_eq rfl rfl,
      by norm_num, r7', f7', Or.inr ⟨fun h => hz (by have := h.2.2.2.1; omega), ?_⟩⟩
    rw [p7, if_neg hz, if_pos (by decide), pcOf_n _ 13 _ rfl (by omega)]
  have p7' : u7.pc = pcOf (P.kb + 108) := by rw [p7, if_pos hz, if_neg (by decide), pcOf_4]
  have g25 : u7.getReg .x25 = BitVec.ofNat 64 (kS9 v + kPen v) := by
    rw [r7 .x25 (by decide), r6 .x25 (by decide), d25]
  have g11 : u7.getReg .x11 = BitVec.ofNat 64 (LPen v) := by rw [r7 .x11 (by decide), r6 .x11 (by decide), d11]
  have g28 : u7.getReg .x28 = BitVec.ofNat 64 (152 - LW v) := by rw [r7 .x28 (by decide), r6 .x28 (by decide), d28]
  obtain ⟨u8, s8, p8, h29, r8, f8⟩ := h3a_spec (codeAt_kf hK 27 rfl) u7 p7' (by omega) (by omega) g25 g11 g28
  rw [kSum_S v hr7'] at h29
  have p8' : u8.pc = pcOf (P.kb + 113) := by rw [p8]; simp only [pcOf_4]
  obtain ⟨u9, s9, p9, r9, f9⟩ := br_spec (run_br113 _) (codeAt_kf hK 28 rfl) u8 p8'
  have x21 : u8.getReg .x21 = BitVec.ofNat 64 thr := by
    rw [r8 .x21 (by decide), r7' .x21 (by decide), h21]
  have hSD := (kLanes v hr7').2.2.2.2.1
  have hPl := LPen_le v
  simp only [E.eval, CmpOp.eval, h29, x21] at p9
  rw [slt_sub _ _ _ (by split_ifs <;> omega) (by omega) hthr] at p9
  have r9' : RegsExcept s0 u9 KL := ((r7'.trans r8).trans r9).mono (by decide)
  have f9' := hFm (hFm f7' f8) f9
  have hsteps : Steps image s0 110 110 u9 :=
    ((((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9).of_eq rfl rfl
  by_cases hr : LS v + 4 * eD (gIdx v 0) + (if 152 - LW v = 4 then 1 else 0) < LPen v + thr
  · refine ⟨110, u9, hsteps, le_refl _, r9', f9', Or.inr ⟨fun h => by have := h.2.2.2.2; omega, ?_⟩⟩
    rw [p9, if_pos (by simp [hr]), pcOf_n _ 7 _ rfl (by omega)]
  · refine ⟨110, u9, hsteps, le_refl _, r9', f9', Or.inl ⟨⟨hr7', hw.1, hw.2, by omega, by omega⟩, rfl, ?_, ?_, ?_⟩⟩
    · rw [p9, if_neg (by simp [hr]), pcOf_4]
    · rw [r9 .x29 (by decide), h29, bv_sub _ _ (by omega) (by split_ifs <;> omega)]
    · rw [r9 .x28 (by decide), r8 .x28 (by decide), g28]
end SigGolfCandidate.T3M.Search.T51
end

/-! ## T51 top-trial kernel: accept / reject tails and the trial (campaign T51, stream SIGNA) -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem sdF_spec {image : Image} {pc : Word} (hc : CodeAt image pc kSdF) (s : MachineState) (hpc : s.pc = pc)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 0x66000) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getMem (BitVec.ofNat 64 FLAGA) = s.getReg .x20 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = FLAGA) := by
  obtain ⟨t, st, pt, mt, rt, ft⟩ := sd_spec (base := 0x66000) (c := 2040) (off := 2040) hc hpc rfl rfl h30
    (by norm_num) (by norm_num)
  exact ⟨t, st, pt, mt, rt, ft⟩
/-- Accept with the flag `x20` (0 = LOW: `+2` path bonus; 128 = HIGH). -/
theorem accept_tail {image : Image} {P : KInst} (hK : T51KAt image P) (w : MachineState)
    (hpc : w.pc = pcOf (P.kb + 114)) (low : Bool) (h20 : w.getReg .x20 = BitVec.ofNat 64 (if low then 0 else 128)) :
    ∃ k t, Steps image w k k t ∧ k ≤ 6 ∧ t.pc = pcOf P.ub ∧
      t.getMem (BitVec.ofNat 64 P.credit) = w.getReg .x29 + BitVec.ofNat 64 (if low then 2 else 0) ∧
      t.getMem (BitVec.ofNat 64 FLAGA) = w.getReg .x20 ∧
      RegsExcept w t [.x29, .x30] ∧ Frame w t (fun A => A = P.credit ∨ A = FLAGA) := by
  have hkb := hK.kbLt
  have hcr := hK.creditLt
  have hne := hK.creditNe
  -- common store tail from kb + 116
  have tail : ∀ x : MachineState, x.pc = pcOf (P.kb + 116) →
      ∃ t, Steps image x 4 4 t ∧ t.pc = pcOf P.ub ∧
        t.getMem (BitVec.ofNat 64 P.credit) = x.getReg .x29 ∧ t.getMem (BitVec.ofNat 64 FLAGA) = x.getReg .x20 ∧
        RegsExcept x t [.x30] ∧ Frame x t (fun A => A = P.credit ∨ A = FLAGA) := by
    intro x hx
    obtain ⟨y1, sy1, py1, g30, ry1, fy1⟩ := luiT5_spec (codeAt_kf hK 31 rfl) x hx
    obtain ⟨y2, sy2, py2, m2, ry2, fy2⟩ := hK.hCr y1 (by rw [py1, pcOf_4]) g30
    obtain ⟨y3, sy3, py3, m3, ry3, fy3⟩ := sdF_spec (codeAt_kf hK 33 rfl) y2 py2
      (by rw [ry2 .x30 (by simp), g30])
    obtain ⟨y4, sy4, py4, ry4, fy4⟩ := hK.hU y3 (by rw [py3, pcOf_4])
    refine ⟨y4, (((sy1.trans sy2).trans sy3).trans sy4).of_eq rfl rfl, py4, ?_, ?_, ?_, ?_⟩
    · rw [fy4.get (by omega) (fun h => h), fy3.get (by omega) hne, m2, ry1 .x29 (by decide)]
    · rw [fy4.get (by norm_num) (fun h => h), m3, ry2 .x20 (by simp), ry1 .x20 (by decide)]
    · exact (((ry1.trans ry2).trans ry3).trans ry4).mono (by decide)
    · exact (((fy1.trans fy2).trans fy3).trans fy4).mono (fun _ _ h => by simp at h; tauto)
  obtain ⟨u1, s1, p1, r1, f1⟩ := br_spec (run_brA0 _) (codeAt_kf hK 29 rfl) w hpc
  simp only [E.eval, CmpOp.eval, h20] at p1
  cases low
  · have p1' : u1.pc = pcOf (P.kb + 116) := by
      rw [p1, if_pos (by decide), pcOf_n _ 2 _ rfl (by omega)]
    obtain ⟨u2, s2, p2, m1, m2, r2, f2⟩ := tail u1 p1'
    refine ⟨5, u2, (s1.trans s2).of_eq rfl rfl, by norm_num, p2, ?_, ?_, ?_, ?_⟩
    · rw [m1, r1 .x29 (by decide)]; simp
    · rw [m2, r1 .x20 (by decide)]
    · exact (r1.trans r2).mono (by decide)
    · exact (f1.trans f2).mono (fun _ _ h => by simp at h; exact h)
  · have p1' : u1.pc = pcOf (P.kb + 115) := by
      rw [p1, if_neg (by decide), pcOf_4]
    obtain ⟨u2, s2, p2, x29, r2, f2⟩ := a1_spec (codeAt_kf hK 30 rfl) u1 p1'
    obtain ⟨u3, s3, p3, m1, m2, r3, f3⟩ := tail u2 (by rw [p2, pcOf_4])
    refine ⟨6, u3, ((s1.trans s2).trans s3).of_eq rfl rfl, le_refl _, p3, ?_, ?_, ?_, ?_⟩
    · rw [m1, x29, r1 .x29 (by decide)]; rfl
    · rw [m2, r2 .x20 (by decide), r1 .x20 (by decide)]
    · exact ((r1.trans r2).trans r3).mono (by decide)
    · exact ((f1.trans f2).trans f3).mono (fun _ _ h => by simp at h; tauto)
theorem reject_high {image : Image} {P : KInst} (hK : T51KAt image P) (w : MachineState)
    (hpc : w.pc = pcOf (P.kb + 120)) (h20 : w.getReg .x20 = BitVec.ofNat 64 128) :
    ∃ t, Steps image w 2 2 t ∧ t.pc = pcOf P.rej ∧ RegsExcept w t [] ∧ Frame w t (fun _ => False) := by
  have hkb := hK.kbLt
  obtain ⟨u1, s1, p1, r1, f1⟩ := br_spec (run_brF0 _) (codeAt_kf hK 35 rfl) w hpc
  simp only [E.eval, CmpOp.eval, h20] at p1
  have p1' : u1.pc = pcOf (P.kb + 128) := by rw [p1, if_pos (by decide), pcOf_n _ 8 _ rfl (by omega)]
  obtain ⟨u2, s2, p2, r2, f2⟩ := hK.hN u1 p1'
  exact ⟨u2, (s1.trans s2).of_eq rfl rfl, p2, (r1.trans r2).mono (by decide),
    (f1.trans f2).mono (fun _ _ h => by simp at h)⟩
theorem blocked_bv (v : Digest) :
    (v.extractLsb' 64 64 >>> 62 == (0 : Word)) = decide (v.toNat < 2 ^ 126) := by
  have hv := v.isLt
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat, h0] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, h0]
    omega
theorem reject_low {image : Image} {P : KInst} (hK : T51KAt image P) (w : MachineState)
    (hpc : w.pc = pcOf (P.kb + 120)) (h20 : w.getReg .x20 = 0) (v : Digest)
    (h7 : w.getReg .x7 = v.extractLsb' 64 64) (h12 : w.getReg .x12 = BitVec.ofNat 64 EOUT) :
    (v.toNat < 2 ^ 126 → ∃ t, Steps image w 4 4 t ∧ t.pc = pcOf P.rej ∧ RegsExcept w t [.x29] ∧
      Frame w t (fun _ => False)) ∧
    (¬ v.toNat < 2 ^ 126 → ∃ t, Steps image w 8 8 t ∧ t.pc = pcOf (P.kb + 4) ∧
      t.getReg .x6 = w.getMem (BitVec.ofNat 64 (EOUT + 16)) ∧ t.getReg .x7 = w.getMem (BitVec.ofNat 64 (EOUT + 24)) ∧
      t.getReg .x20 = BitVec.ofNat 64 128 ∧ t.getReg .x21 = BitVec.ofNat 64 14 ∧
      RegsExcept w t [.x6, .x7, .x20, .x21, .x29] ∧ Frame w t (fun _ => False)) := by
  have hkb := hK.kbLt
  obtain ⟨u1, s1, p1, r1, f1⟩ := br_spec (run_brF0 _) (codeAt_kf hK 35 rfl) w hpc
  simp only [E.eval, CmpOp.eval, h20] at p1
  have p1' : u1.pc = pcOf (P.kb + 121) := by rw [p1, if_neg (by decide), pcOf_4]
  obtain ⟨u2, s2, p2, x29, r2, f2⟩ := f1a_spec (codeAt_kf hK 36 rfl) u1 p1'
  rw [r1 .x7 (by decide), h7] at x29
  have p2' : u2.pc = pcOf (P.kb + 122) := by rw [p2, pcOf_4]
  obtain ⟨u3, s3, p3, r3, f3⟩ := br_spec (run_br122 _) (codeAt_kf hK 37 rfl) u2 p2'
  simp only [E.eval, CmpOp.eval, x29, blocked_bv] at p3
  constructor
  · intro hbl
    have p3' : u3.pc = pcOf (P.kb + 128) := by
      rw [p3, if_pos (decide_eq_true hbl), pcOf_n _ 6 _ rfl (by omega)]
    obtain ⟨u4, s4, p4, r4, f4⟩ := hK.hN u3 p3'
    exact ⟨u4, (((s1.trans s2).trans s3).trans s4).of_eq rfl rfl, p4,
      (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by simp at h)⟩
  · intro hbl
    have p3' : u3.pc = pcOf (P.kb + 123) := by
      rw [p3, if_neg (by rw [decide_eq_true_eq]; exact hbl), pcOf_4]
    have x12 : u3.getReg .x12 = BitVec.ofNat 64 EOUT := by
      rw [r3 .x12 (by decide), r2 .x12 (by decide), r1 .x12 (by decide), h12]
    obtain ⟨u4, s4, p4, y6, y7, y20, y21, r4, f4⟩ := f2a_spec (codeAt_kf hK 38 rfl) u3 p3' x12
    have p4' : u4.pc = pcOf (P.kb + 127) := by rw [p4]; simp only [pcOf_4]
    obtain ⟨u5, s5, p5, r5, f5⟩ := jal_spec (run_j127 _) (codeAt_kf hK 39 rfl) u4 p4'
    have hF : Frame w u3 (fun _ => False) := ((f1.trans f2).trans f3).mono (fun _ _ h => by simp at h)
    refine ⟨u5, ((((s1.trans s2).trans s3).trans s4).trans s5).of_eq rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [p5, pcOf_m _ 123 18446744073709551124 (by norm_num) (by omega) (by omega)]; congr 1
    · rw [r5 .x6 (by decide), y6, hF.get (by norm_num) (fun h => h)]
    · rw [r5 .x7 (by decide), y7, hF.get (by norm_num) (fun h => h)]
    · rw [r5 .x20 (by decide), y20]
    · rw [r5 .x21 (by decide), y21]
    · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide)
    · exact ((hF.trans f4).trans f5).mono (fun _ _ h => by simp at h)
end SigGolfCandidate.T3M.Search.T51
end

/-! ## T51 top-trial kernel: the trial (campaign T51, stream SIGNA) -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
abbrev kRegs : List Reg := [.x6, .x7, .x10, .x11, .x20, .x21, .x25, .x28, .x29, .x30]
theorem producerDecodeAt_kAcc (v : Digest) (low : Bool) :
    (WCT9.CanonicalPolicy.producerDecodeAt 0 14 low v).isSome = true ↔ kAcc v (if low then 12 else 14) := by
  constructor
  · intro h
    obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.1 h
    have := ((producer_some v 14 low (by norm_num) ds).1 hds).1
    cases low <;> simpa using this
  · intro h
    have hk : kAcc v (14 - if low then 2 else 0) := by cases low <;> simpa using h
    rw [(producer_some v 14 low (by norm_num) _).2 ⟨hk, kAcc_decode hk⟩]
    rfl
theorem producerDecodeAt_some {v : Digest} {low : Bool} (h : kAcc v (if low then 12 else 14)) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 14 low v = some (T3.dataDigits 0 v ++ [152 - LW v]) := by
  have hk : kAcc v (14 - if low then 2 else 0) := by cases low <;> simpa using h
  exact (producer_some v 14 low (by norm_num) _).2 ⟨hk, kAcc_decode hk⟩
theorem producerDecodeAt_none {v : Digest} {low : Bool} (h : ¬ kAcc v (if low then 12 else 14)) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 14 low v = none := by
  cases hp : WCT9.CanonicalPolicy.producerDecodeAt 0 14 low v with
  | none => rfl
  | some ds => exact absurd ((producerDecodeAt_kAcc v low).1 (by rw [hp]; rfl)) h
theorem topGood_iff (w : Digest) : WCT9.topGood w ↔ kAcc w 12 := by
  unfold WCT9.topGood
  exact producerDecodeAt_kAcc w true
/-- One T51 top trial from `K_ENTRY` on the 256-bit answer `a` (LOW half in `x6`, `x7`; `x12` = EOUT holds `a`):
accept exactly the canonical producer answer (`producerDecodeOut 0 14`, floor = `topFloor` = 14), storing the credit
and the choice flag and entering `U_ENTRY` with the selected word and its checksum digit, or reject into `NEXT`
without a store. Generic in the instance `P` (sign and expand). -/
theorem trial {image : Image} {P : KInst} (hK : T51KAt image P) (u : MachineState) (hpc : u.pc = pcOf P.kb)
    (a : BitVec 256) (h6 : u.getReg .x6 = (a.extractLsb' 0 128).extractLsb' 0 64)
    (h7 : u.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64) (h12 : u.getReg .x12 = BitVec.ofNat 64 EOUT)
    (hH0 : u.getMem (BitVec.ofNat 64 (EOUT + 16)) = (a.extractLsb' 128 128).extractLsb' 0 64)
    (hH8 : u.getMem (BitVec.ofNat 64 (EOUT + 24)) = (a.extractLsb' 128 128).extractLsb' 64 64)
    (h17 : u.getReg .x17 = BitVec.ofNat 64 (T3.target 0)) (ht : T51TableW P.blk u) :
    (∀ ds low, WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = some (ds, low) →
      ∃ k t, Steps image u k k t ∧ k ≤ 240 ∧ t.pc = pcOf P.ub ∧
        t.getReg .x6 = (WCT9.encodingAnswer 0 a).extractLsb' 0 64 ∧
        t.getReg .x7 = (WCT9.encodingAnswer 0 a).extractLsb' 64 64 ∧
        WCT9.CanonicalPolicy.decode 0 (WCT9.encodingAnswer 0 a) = some ds ∧
        t.getReg .x28 = BitVec.ofNat 64 (ds.getD 50 0) ∧
        t.getMem (BitVec.ofNat 64 P.credit) = BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit 0 low ds) ∧
        t.getMem (BitVec.ofNat 64 FLAGA) = BitVec.ofNat 64 (if low then 0 else 128) ∧
        RegsExcept u t kRegs ∧ Frame u t (fun A => A = P.credit ∨ A = FLAGA)) ∧
    (WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = none →
      ∃ k t, Steps image u k k t ∧ k ≤ 240 ∧ t.pc = pcOf P.rej ∧ RegsExcept u t kRegs ∧
        Frame u t (fun _ => False)) := by
  have hkb := hK.kbLt
  have hbb := hK.blkLt
  have hblk := hK.blk8
  have hFm : ∀ {x y z : MachineState}, Frame x y (fun _ => False) → Frame y z (fun _ => False) →
      Frame x z (fun _ => False) := fun h1 h2 => (h1.trans h2).mono (fun _ _ h => by simpa using h)
  have hEA : WCT9.encodingAnswer 0 a =
      if WCT9.topChooseLow a then a.extractLsb' 0 128 else a.extractLsb' 128 128 := WCT9.encodingAnswer_top_eq a
  have hPDO : WCT9.CanonicalPolicy.producerDecodeOut 0 14 a =
      (WCT9.CanonicalPolicy.producerDecodeAt 0 14 (WCT9.topChooseLow a) (WCT9.encodingAnswer 0 a)).map
        (fun d => (d, WCT9.topChooseLow a)) := rfl
  obtain ⟨w0, s0, p0, e10, r0, f0⟩ := hK.hE u hpc
  obtain ⟨w1, s1', p1, e20, e21, r1', f1'⟩ := e2_spec (codeAt_kf hK 1 rfl) w0 p0
  have s1 := s0.trans s1'
  have r1 : RegsExcept u w1 [.x10, .x20, .x21] := (r0.trans r1').mono (by decide)
  have f1 := hFm f0 f1'
  have p1' : w1.pc = pcOf (P.kb + 4) := by rw [p1, pcOf_4, pcOf_4]
  have e10' : w1.getReg .x10 = BitVec.ofNat 64 (P.blk + 160) := (r1' .x10 (by decide)).trans e10
  have ht1 : T51TableW P.blk w1 := ht.frame f1 hblk (by omega) (fun _ _ h => h)
  have w6 : w1.getReg .x6 = (a.extractLsb' 0 128).extractLsb' 0 64 := (r1 .x6 (by decide)).trans h6
  have w7 : w1.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64 := (r1 .x7 (by decide)).trans h7
  have w17 : w1.getReg .x17 = BitVec.ofNat 64 152 := (r1 .x17 (by decide)).trans h17
  obtain ⟨k2, w2, s2, hk2, r2, f2, hres⟩ :=
    half_run hK w1 p1' (a.extractLsb' 0 128) w6 w7 e10' w17 (thr := 12) (by norm_num) e21 ht1
  rcases hres with ⟨hacc, _, p2, x29, x28⟩ | ⟨hrej, p2⟩
  · -- LOW accepted
    have hTC : WCT9.topChooseLow a = true :=
      decide_eq_true (Or.inl ((topGood_iff _).2 hacc))
    have hdec := kAcc_decode hacc
    have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 14 a =
        some (T3.dataDigits 0 (a.extractLsb' 0 128) ++ [152 - LW (a.extractLsb' 0 128)], true) := by
      rw [hPDO, hTC, hEA, hTC, if_pos rfl, producerDecodeAt_some (low := true) hacc]; rfl
    have hea : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by rw [hEA, hTC, if_pos rfl]
    have w20 : w2.getReg .x20 = BitVec.ofNat 64 (if true then 0 else 128) := by rw [r2 .x20 (by decide), e20]; rfl
    obtain ⟨k3, w3, s3, hk3, p3, m1, m2, r3, f3⟩ := accept_tail hK w2 p2 true w20
    refine ⟨fun ds low h => ?_, fun h => (by rw [hpdo] at h; cases h)⟩
    rw [hpdo] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨4 + k2 + k3, w3, (s1.trans s2).trans s3, by omega, p3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r3 .x6 (by decide), r2 .x6 (by decide), w6, hea]
    · rw [r3 .x7 (by decide), r2 .x7 (by decide), w7, hea]
    · rw [hea]; exact hdec
    · rw [r3 .x28 (by decide), x28, ds_getD_50' hdec]
    · rw [m1, x29, credit_lanes hdec true, ofNat_add_ofNat]
      have := hacc.2.2.2.2
      apply congrArg (BitVec.ofNat 64)
      simp only [if_true]
      omega
    · rw [m2, r2 .x20 (by decide), e20]; rfl
    · exact ((r1.trans r2).trans r3).mono (by decide)
    · exact ((hFm f1 f2).trans f3).mono (fun _ _ h => by simpa using h)
  · -- LOW rejected
    have w20 : w2.getReg .x20 = 0 := by rw [r2 .x20 (by decide), e20]
    have w7' : w2.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64 := (r2 .x7 (by decide)).trans w7
    have w12 : w2.getReg .x12 = BitVec.ofNat 64 EOUT := by
      rw [r2 .x12 (by decide), r1 .x12 (by decide), h12]
    obtain ⟨hblk', hnblk⟩ := reject_low hK w2 p2 w20 (a.extractLsb' 0 128) w7' w12
    by_cases hbl : (a.extractLsb' 0 128).toNat < 2 ^ 126
    · obtain ⟨w3, s3, p3, r3, f3⟩ := hblk' hbl
      have hTC : WCT9.topChooseLow a = true := decide_eq_true (Or.inr hbl)
      have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = none := by
        rw [hPDO, hTC, hEA, hTC, if_pos rfl, producerDecodeAt_none (low := true) hrej]; rfl
      refine ⟨fun ds low h => (by rw [hpdo] at h; cases h), fun _ => ⟨4 + k2 + 4, w3, (s1.trans s2).trans s3,
        by omega, p3, ((r1.trans r2).trans r3).mono (by decide), hFm (hFm f1 f2) f3⟩⟩
    · obtain ⟨w3, s3, p3, y6, y7, y20, y21, r3, f3⟩ := hnblk hbl
      have hTC : WCT9.topChooseLow a = false := by
        unfold WCT9.topChooseLow
        exact decide_eq_false (by rintro (h | h); exact hrej ((topGood_iff _).1 h); exact hbl h)
      have hea : WCT9.encodingAnswer 0 a = a.extractLsb' 128 128 := by rw [hEA, hTC]; rfl
      have hF2 : Frame u w2 (fun _ => False) := hFm f1 f2
      have hF3 : Frame u w3 (fun _ => False) := hFm hF2 f3
      have v6 : w3.getReg .x6 = (a.extractLsb' 128 128).extractLsb' 0 64 := by
        rw [y6, hF2.get (by norm_num) (fun h => h), hH0]
      have v7 : w3.getReg .x7 = (a.extractLsb' 128 128).extractLsb' 64 64 := by
        rw [y7, hF2.get (by norm_num) (fun h => h), hH8]
      have v10 : w3.getReg .x10 = BitVec.ofNat 64 (P.blk + 160) := by
        rw [r3 .x10 (by decide), r2 .x10 (by decide), e10']
      have v17 : w3.getReg .x17 = BitVec.ofNat 64 152 := by rw [r3 .x17 (by decide), r2 .x17 (by decide), w17]
      have ht3 : T51TableW P.blk w3 := ht.frame hF3 hblk (by omega) (fun _ _ h => h)
      obtain ⟨k4, w4, s4, hk4, r4, f4, hres2⟩ :=
        half_run hK w3 p3 (a.extractLsb' 128 128) v6 v7 v10 v17 (thr := 14) (by norm_num) y21 ht3
      have w20' : w4.getReg .x20 = BitVec.ofNat 64 128 := by rw [r4 .x20 (by decide), y20]
      rcases hres2 with ⟨hacc2, _, p4, x29, x28⟩ | ⟨hrej2, p4⟩
      · have hdec := kAcc_decode hacc2
        have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 14 a =
            some (T3.dataDigits 0 (a.extractLsb' 128 128) ++ [152 - LW (a.extractLsb' 128 128)], false) := by
          rw [hPDO, hTC, hea, producerDecodeAt_some (low := false) hacc2]; rfl
        obtain ⟨k5, w5, s5, hk5, p5, m1, m2, r5, f5⟩ := accept_tail hK w4 p4 false (by rw [w20']; rfl)
        refine ⟨fun ds low h => ?_, fun h => (by rw [hpdo] at h; cases h)⟩
        rw [hpdo] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨4 + k2 + 8 + k4 + k5, w5, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, p5,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [r5 .x6 (by decide), r4 .x6 (by decide), v6, hea]
        · rw [r5 .x7 (by decide), r4 .x7 (by decide), v7, hea]
        · rw [hea]; exact hdec
        · rw [r5 .x28 (by decide), x28, ds_getD_50' hdec]
        · rw [m1, x29, credit_lanes hdec false, ofNat_add_ofNat]
          have := hacc2.2.2.2.2
          apply congrArg (BitVec.ofNat 64)
          simp only [Bool.false_eq_true, if_false]
          omega
        · rw [m2, w20']; rfl
        · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide)
        · exact ((hFm hF3 f4).trans f5).mono (fun _ _ h => by simpa using h)
      · have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = none := by
          rw [hPDO, hTC, hea, producerDecodeAt_none (low := false) hrej2]; rfl
        obtain ⟨w5, s5, p5, r5, f5⟩ := reject_high hK w4 p4 w20'
        refine ⟨fun ds low h => (by rw [hpdo] at h; cases h), fun _ => ⟨4 + k2 + 8 + k4 + 2, w5,
          (((s1.trans s2).trans s3).trans s4).trans s5, by omega, p5,
          ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide), hFm (hFm hF3 f4) f5⟩⟩
end SigGolfCandidate.T3M.Search.T51
end
