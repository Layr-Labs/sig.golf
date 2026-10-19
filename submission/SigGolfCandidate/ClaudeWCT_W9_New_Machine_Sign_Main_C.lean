import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_Main_B

set_option Elab.async false


namespace SigGolfCandidate.T3M.Sign.SharedHints
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def firstCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x1de3823,0xe3303,0x1e400393,0xfff40f13,0xf0a63]
sym_block first := symRun { noAlias := true } firstCode (pcOf 22363) 100
def secondCode : List (BitVec 32) := bv_list% 32 [0x1600393,0xffe40f13,0xf0463]
sym_block second := symRun { noAlias := true } secondCode (pcOf 22370) 100
def thirdCode : List (BitVec 32) := bv_list% 32 [0x100393]
sym_block third := symRun { noAlias := true } thirdCode (pcOf 22373) 100
def addHintCode : List (BitVec 32) := bv_list% 32 [0x3d383b3,0x730333,0x6e3023]
sym_block addHint := symRun { noAlias := true } addHintCode (pcOf 22374) 100

theorem first_steps {im : Image} (hc : CodeAt im (pcOf 22363) firstCode)
    (s : MachineState) (hp : s.pc=pcOf 22363) (lay h f : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h29 : s.getReg .x29=BitVec.ofNat 64 f)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 h) :
    ∃ t,Steps im s 7 7 t ∧ t.pc=(if lay=1 then pcOf 22374 else pcOf 22370) ∧
      t.getReg .x6=BitVec.ofNat 64 h ∧ t.getReg .x7=484 ∧ t.getReg .x28=0x66000 ∧
      t.getMem (0x66010#64)=BitVec.ofNat 64 f ∧
      RegsExcept s t [.x6,.x7,.x28,.x30] ∧ Frame s t (fun A => A=0x66010) := by
  refine ⟨_,symRun_sound first hc s hp (by simp [first.res,rv_simp];try decide),?_,?_,?_,?_,?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩;interval_cases lay <;> simp [first.res,rv_simp,h8]
  · simp [first.res,rv_simp,hm]
  · simp [first.res,rv_simp]
  · simp [first.res,rv_simp]
  · simp [first.res,rv_simp,h29]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,first.res]; t3n []
    rw [if_neg (by omega)]

theorem second_steps {im : Image} (hc : CodeAt im (pcOf 22370) secondCode)
    (s : MachineState) (hp : s.pc=pcOf 22370) (lay : Nat) (hl : lay=2 ∨ lay=3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay=2 then pcOf 22374 else pcOf 22373) ∧
      t.getReg .x7=22 ∧ RegsExcept s t [.x7,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound second hc s hp (by simp [second.res,rv_simp]),?_,?_,?_,?_⟩
  · rcases hl with rfl|rfl <;> simp [second.res,rv_simp,h8]
  · simp [second.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem third_steps {im : Image} (hc : CodeAt im (pcOf 22373) thirdCode)
    (s : MachineState) (hp : s.pc=pcOf 22373) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22374 ∧ t.getReg .x7=1 ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound third hc s hp (by simp [third.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [third.res,rv_simp]
  · simp [third.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem add_steps {im : Image} (hc : CodeAt im (pcOf 22374) addHintCode)
    (s : MachineState) (hp : s.pc=pcOf 22374) (h f mul : Nat)
    (h6 : s.getReg .x6=BitVec.ofNat 64 h) (h7 : s.getReg .x7=BitVec.ofNat 64 mul)
    (h29 : s.getReg .x29=BitVec.ofNat 64 f) (h28 : s.getReg .x28=0x66000) :
    ∃ t,Steps im s 3 6 t ∧ t.pc=pcOf 22377 ∧
      t.getMem (0x66000#64)=BitVec.ofNat 64 (h+mul*f) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=0x66000) := by
  refine ⟨_,symRun_sound addHint hc s hp (by simp [addHint.res,rv_simp,h28];try decide),?_,?_,?_,?_⟩
  · simp [addHint.res,rv_simp]
  · simp only [Result.toState_getMem,addHint.res];t3n [h6,h7,h29,h28]
    simp [← BitVec.ofNat_mul,← BitVec.ofNat_add]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,addHint.res];t3n [h28]
    rw [if_neg (by omega)]
#print axioms add_steps
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedHints
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Code (im : Image) : Prop where
  first : CodeAt im (pcOf 22363) firstCode
  second : CodeAt im (pcOf 22370) secondCode
  third : CodeAt im (pcOf 22373) thirdCode
  add : CodeAt im (pcOf 22374) addHintCode

/-- Hint weight of layer `lay` (img-v4/v6 radix 484 / 22 / 1). -/
def hintWeight (lay : Nat) : Nat := if lay = 1 then 484 else if lay = 2 then 22 else 1
theorem steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22363)
    (lay h f : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h29 : s.getReg .x29=BitVec.ofNat 64 f)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 h) :
    ∃ t k,Steps im s k (k+3) t ∧ k≤14 ∧ t.pc=pcOf 22377 ∧
      t.getMem (0x66000#64)=BitVec.ofNat 64 (h+hintWeight lay*f) ∧
      t.getMem (0x66010#64)=BitVec.ofNat 64 f ∧
      RegsExcept s t [.x6,.x7,.x28,.x30] ∧ Frame s t (fun A => A=0x66000 ∨ A=0x66010) := by
  obtain ⟨a,sa,ap,a6,a7,a28,am,ar,af⟩ := first_steps hc.first s hp lay h f hl h8 h29 hm
  have a8 := (ar.get (by decide : Reg.x8 ∉ [.x6,.x7,.x28,.x30])).trans h8
  have a29 := (ar.get (by decide : Reg.x29 ∉ [.x6,.x7,.x28,.x30])).trans h29
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · obtain ⟨t,aToT,tp,tm,tr,tf⟩ := add_steps hc.add a (by simpa using ap) h f 484 a6 a7 a29 a28
    exact ⟨t,10,sa.trans aToT,by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans am,
      (ar.trans tr).mono (by simp),(af.trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b7,br,bf⟩ := second_steps hc.second a (by simpa using ap) 2 (by simp) a8
    obtain ⟨t,bt,tp,tm,tr,tf⟩ := add_steps hc.add b (by simpa using bp) h f 22
      ((br.get (by decide)).trans a6) b7 ((br.get (by decide)).trans a29) ((br.get (by decide)).trans a28)
    exact ⟨t,13,sa.trans (ab.trans bt),by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans ((bf.get (by decide) (by simp)).trans am),
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b7,br,bf⟩ := second_steps hc.second a (by simpa using ap) 3 (by simp) a8
    obtain ⟨c,bc,cp,c7,cr,cf⟩ := third_steps hc.third b (by simpa using bp)
    obtain ⟨t,ct,tp,tm,tr,tf⟩ := add_steps hc.add c cp h f 1
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a6)) c7
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a29))
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a28))
    exact ⟨t,14,sa.trans (ab.trans (bc.trans ct)),by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans ((cf.get (by decide) (by simp)).trans ((bf.get (by decide) (by simp)).trans am)),
      (((ar.trans br).trans cr).trans tr).mono (by simp),(((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
#print axioms steps
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_dispatch : DispatchCode Images.signImage := by
  constructor <;> apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedFloor
namespace SigGolfCandidate.T3M.Sign.SharedHints
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedControlTail
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def initResidualCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x4a00313,0x6e3423]
sym_block initResidual := symRun { noAlias := true } initResidualCode (pcOf 22226) 100
def firstLayerCode : List (BitVec 32) := bv_list% 32 [0x100413]
sym_block firstLayer := symRun { noAlias := true } firstLayerCode (pcOf 22239) 100
def nextLayerCode : List (BitVec 32) := bv_list% 32 [0x140413,0x400313,0xc8646ae3]
sym_block nextLayer := symRun { noAlias := true } nextLayerCode (pcOf 22457) 100
def topProduceCode : List (BitVec 32) := bv_list% 32 [0x413,0x493,0xc00793,0x3600d13,0x3300d93,0x9200893,0x20e37,0x550e0e13,0xe3903,0x1395913,0x90713,0xf80ea06f]
sym_block topProduce := symRun { noAlias := true } topProduceCode (pcOf 22478) 100

theorem initResidual_steps {im : Image} (hc : CodeAt im (pcOf 22226) initResidualCode)
    (s : MachineState) (hp : s.pc=pcOf 22226) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22230 ∧ t.getMem (0x66008#64)=74 ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound initResidual hc s hp (by simp [initResidual.res,rv_simp];try decide),?_,?_,?_,?_⟩
  · simp [initResidual.res,rv_simp]
  · simp [initResidual.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,initResidual.res];t3n []
    rw [if_neg (by omega)]

theorem firstLayer_steps {im : Image} (hc : CodeAt im (pcOf 22239) firstLayerCode)
    (s : MachineState) (hp : s.pc=pcOf 22239) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22240 ∧ t.getReg .x8=1 ∧
      RegsExcept s t [.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound firstLayer hc s hp (by simp [firstLayer.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [firstLayer.res,rv_simp]
  · simp [firstLayer.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem nextLayer_steps {im : Image} (hc : CodeAt im (pcOf 22457) nextLayerCode)
    (s : MachineState) (hp : s.pc=pcOf 22457) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22240 else pcOf 22460) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧ RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound nextLayer hc s hp (by simp [nextLayer.res,rv_simp]),?_,?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩;interval_cases lay <;> simp [nextLayer.res,rv_simp,h8]
  · simp [nextLayer.res,rv_simp,h8,BitVec.ofNat_add]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

structure TopPost (index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=54
  n4 : t.getReg .x27=51
  target : t.getReg .x17=146
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  regs : RegsExcept s t [.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28]
  frame : Frame s t (fun _ => False)
theorem topProduce_steps {im : Image} (hc : CodeAt im (pcOf 22478) topProduceCode)
    (s : MachineState) (hp : s.pc=pcOf 22478) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 12 12 t ∧ TopPost index s t := by
  refine ⟨_,symRun_sound topProduce hc s hp (by simp [topProduce.res,rv_simp]),?_⟩
  constructor
  all_goals first
    | solve | simp [topProduce.res,rv_simp,hidx]
    | skip
  · simp only [topProduce.res,rv_simp,hidx]
    exact ofNat_shr index 19 (by omega)
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms topProduce_steps
end SigGolfCandidate.T3M.Sign.SharedControlTail


namespace SigGolfCandidate.T3M.Sign.SharedLowerRegisters
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
def code22377 : List (BitVec 32) := bv_list% 32 [0x2b00d13,0xd93,0xc900893,0x600793,0xfff40313,0x30463]
sym_block blk22377 := symRun { noAlias := true } code22377 (pcOf 22377) 100
def code22383 : List (BitVec 32) := bv_list% 32 [0x80006f]
sym_block blk22383 := symRun { noAlias := true } code22383 (pcOf 22383) 100
def code22384 : List (BitVec 32) := bv_list% 32 [0x700793]
sym_block blk22384 := symRun { noAlias := true } code22384 (pcOf 22384) 100
def code22385 : List (BitVec 32) := bv_list% 32 [0x20e37,0x550e0e13,0xe3303,0xfff40393,0x38c63]
sym_block blk22385 := symRun { noAlias := true } code22385 (pcOf 22385) 100
def code22390 : List (BitVec 32) := bv_list% 32 [0xffe40393,0x2038063]
sym_block blk22390 := symRun { noAlias := true } code22390 (pcOf 22390) 100
def code22392 : List (BitVec 32) := bv_list% 32 [0x3f37913,0x635493,0x200006f]
sym_block blk22392 := symRun { noAlias := true } code22392 (pcOf 22392) 100
def code22395 : List (BitVec 32) := bv_list% 32 [0xc35913,0x7f97913,0x1335493,0x100006f]
sym_block blk22395 := symRun { noAlias := true } code22395 (pcOf 22395) 100
def code22399 : List (BitVec 32) := bv_list% 32 [0x635913,0x3f97913,0xc35493]
sym_block blk22399 := symRun { noAlias := true } code22399 (pcOf 22399) 100
def code22402 : List (BitVec 32) := bv_list% 32 [0x90713,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block blk22402 := symRun { noAlias := true } code22402 (pcOf 22402) 100
def code22409 : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xbd5ea0ef]
sym_block blk22409 := symRun { noAlias := true } code22409 (pcOf 22409) 100
structure Code (im : Image) : Prop where
  at22377 : CodeAt im (pcOf 22377) code22377
  at22383 : CodeAt im (pcOf 22383) code22383
  at22384 : CodeAt im (pcOf 22384) code22384
  at22385 : CodeAt im (pcOf 22385) code22385
  at22390 : CodeAt im (pcOf 22390) code22390
  at22392 : CodeAt im (pcOf 22392) code22392
  at22395 : CodeAt im (pcOf 22395) code22395
  at22399 : CodeAt im (pcOf 22399) code22399
  at22402 : CodeAt im (pcOf 22402) code22402
  at22409 : CodeAt im (pcOf 22409) code22409
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22409
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  dst : t.getReg .x28=BitVec.ofNat 64 ENC
  src : t.getReg .x29=BitVec.ofNat 64 (0x66040+32*lay)
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun _ => False)
theorem setup1 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=1)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 23 23 t ∧ Post 1 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22384.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22384 hc.at22384 s1 (by simp [s1,blk22377.res,s2,blk22384.res,rv_simp,h8]) (by simp [blk22384.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22395.res.toState s3
  have st4 : Steps im s3 4 4 s4 := symRun_sound blk22395 hc.at22395 s3 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,rv_simp,h8]) (by simp [blk22395.res,rv_simp];try decide)
  let s5 := blk22402.res.toState s4
  have st5 : Steps im s4 7 7 s5 := symRun_sound blk22402 hc.at22402 s4 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s5, st1.trans (st2.trans (st3.trans (st4.trans (st5)))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index >>> (12:Nat) &&& 127)=BitVec.ofNat 64 (index/2^12%2^7)
    rw [ofNat_shr index 12 (by omega)]
    exact ofNat_and_mask (index/2^12) 7 (by decide)
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (19:Nat)=BitVec.ofNat 64 (index/2^19)
    exact ofNat_shr index 19 (by omega)
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms setup1
theorem setup2 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=2)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 24 24 t ∧ Post 2 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22383.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22383 hc.at22383 s1 (by simp [s1,blk22377.res,s2,blk22383.res,rv_simp,h8]) (by simp [blk22383.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22390.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22390 hc.at22390 s3 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,rv_simp,h8]) (by simp [blk22390.res,rv_simp];try decide)
  let s5 := blk22399.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22399 hc.at22399 s4 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,rv_simp,h8]) (by simp [blk22399.res,rv_simp];try decide)
  let s6 := blk22402.res.toState s5
  have st6 : Steps im s5 7 7 s6 := symRun_sound blk22402 hc.at22402 s5 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index >>> (6:Nat) &&& 63)=BitVec.ofNat 64 (index/2^6%2^6)
    rw [ofNat_shr index 6 (by omega)]
    exact ofNat_and_mask (index/2^6) 6 (by decide)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (12:Nat)=BitVec.ofNat 64 (index/2^12)
    exact ofNat_shr index 12 (by omega)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms setup2
theorem setup3 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=3)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 24 24 t ∧ Post 3 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22383.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22383 hc.at22383 s1 (by simp [s1,blk22377.res,s2,blk22383.res,rv_simp,h8]) (by simp [blk22383.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22390.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22390 hc.at22390 s3 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,rv_simp,h8]) (by simp [blk22390.res,rv_simp];try decide)
  let s5 := blk22392.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22392 hc.at22392 s4 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,rv_simp,h8]) (by simp [blk22392.res,rv_simp];try decide)
  let s6 := blk22402.res.toState s5
  have st6 : Steps im s5 7 7 s6 := symRun_sound blk22402 hc.at22402 s5 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index &&& 63)=BitVec.ofNat 64 (index%2^6)
    exact ofNat_and_mask index 6 (by decide)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (6:Nat)=BitVec.ofNat 64 (index/2^6)
    exact ofNat_shr index 6 (by omega)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms setup3
end SigGolfCandidate.T3M.Sign.SharedLowerRegisters


namespace SigGolfCandidate.T3M.Sign.SharedLowerCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def code : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xbd5ea0ef]
sym_block block := symRun { noAlias := true } code (pcOf 22409) 100

structure Post (lay : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  regs : RegsExcept s t [.x1,.x6,.x7]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)
theorem steps {im : Image} (hc : CodeAt im (pcOf 22409) code)
    (s : MachineState) (hp : s.pc=pcOf 22409) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC)
    (h29 : s.getReg .x29=BitVec.ofNat 64 (0x66040+32*lay)) :
    ∃ t,Steps im s 9 9 t ∧ Post lay s t := by
  rcases hl with ⟨hlo,hhi⟩
  have hob : block.res.obligs s := by
    interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC] <;> decide
  refine ⟨_,symRun_sound block hc s hp hob,?_⟩
  constructor
  · simp [block.res,rv_simp]
  · simp [block.res,rv_simp]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res];t3n [h28,ENC]
    unfold ENC at hn
    repeat rw [if_neg (by omega)]
#print axioms steps
end SigGolfCandidate.T3M.Sign.SharedLowerCopy


namespace SigGolfCandidate.T3M.Sign.SharedLowerSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)

theorem registers {im : Image} (hc : SharedLowerRegisters.Code im) (s : MachineState)
    (hp : s.pc=pcOf 22377) (lay index : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k,Steps im s k k t ∧ k≤24 ∧ SharedLowerRegisters.Post lay index s t := by
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup1 hc s hp index hi h8 hidx
    exact ⟨t,23,ht,by decide,hp⟩
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup2 hc s hp index hi h8 hidx
    exact ⟨t,24,ht,by decide,hp⟩
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup3 hc s hp index hi h8 hidx
    exact ⟨t,24,ht,by decide,hp⟩

theorem setup {im : Image} (hc : SharedLowerRegisters.Code im) (s : MachineState)
    (hp : s.pc=pcOf 22377) (lay index : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k,Steps im s k k t ∧ k≤33 ∧ Post lay index s t := by
  obtain ⟨a,k,sa,hk,ha⟩ := registers hc s hp lay index hl hi h8 hidx
  obtain ⟨t,aToT,ht⟩ := SharedLowerCopy.steps hc.at22409 a ha.pc lay hl ha.dst ha.src
  refine ⟨t,k+9,sa.trans aToT,by omega,?_⟩
  refine ⟨ht.pc,ht.ret,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (ht.regs.get (by decide)).trans ha.chains
  · exact (ht.regs.get (by decide)).trans ha.n4
  · exact (ht.regs.get (by decide)).trans ha.target
  · exact (ht.regs.get (by decide)).trans ha.height
  · exact (ht.regs.get (by decide)).trans ha.leaf
  · rw [ht.regs.get (by decide),ht.regs.get (by decide)];exact ha.selected
  · exact (ht.regs.get (by decide)).trans ha.tree
  · exact ht.leftLo.trans (ha.frame.get (by omega) (by simp))
  · exact ht.leftHi.trans (ha.frame.get (by omega) (by simp))
  · exact ht.rightLo.trans (ha.frame.get (by omega) (by simp))
  · exact ht.rightHi.trans (ha.frame.get (by omega) (by simp))
  · exact (ha.regs.trans ht.regs).mono (by simp)
  · exact (ha.frame.trans ht.frame).mono (by tauto)
#print axioms setup
end SigGolfCandidate.T3M.Sign.SharedLowerSetup


namespace SigGolfCandidate.T3M.Sign.SharedLowerSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.WCT9
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure CallPost (lay index residual hints : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  floor : t.getMem (0x66010#64)=BitVec.ofNat 64 (ClaudeWCT.WCT9.CanonicalPolicy.threshold lay residual)
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (hints+SharedHints.hintWeight lay*ClaudeWCT.WCT9.CanonicalPolicy.threshold lay residual)
  layer : t.getReg .x8=BitVec.ofNat 64 lay
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x20,.x26,.x27,.x28,.x29,.x30]
  frame : Frame s t (fun A => A=0x66000 ∨ A=0x66010 ∨ A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)


theorem call_steps {im : Image} (hf : SharedFloor.DispatchCode im) (hh : SharedHints.Code im)
    (hc : SharedLowerRegisters.Code im) (s : MachineState) (hp : s.pc=pcOf 22240)
    (lay index residual hints : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (hr : residual < if lay=1 then 56 else if lay=2 then 41 else 22)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual)
    (hhm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t k c,Steps im s k c t ∧ c≤120 ∧ CallPost lay index residual hints s t := by
  obtain ⟨a,ka,sa,hka,ap,a29,ar,af⟩ := SharedFloor.threshold_steps hf s hp lay residual hl hr h8 hrm
  have a8 := (ar.get (by decide : Reg.x8 ∉ [.x6,.x20,.x28,.x29])).trans h8
  obtain ⟨b,kb,ab,hkb,bp,bhints,bfloor,br,bf⟩ := SharedHints.steps hh a ap lay hints _ hl a8 a29
    ((af.get (A:=0x66000) (by decide) (by simp)).trans hhm)
  have b8 := (br.get (by decide : Reg.x8 ∉ [.x6,.x7,.x28,.x30])).trans a8
  have bidx : b.getMem (0x20550#64)=BitVec.ofNat 64 index :=
    (bf.get (A:=0x20550) (by decide) (by decide)).trans ((af.get (by decide) (by simp)).trans hidx)
  obtain ⟨t,kc,bt,hkc,ht⟩ := setup hc b bp lay index hl hi b8 bidx
  refine ⟨t,ka+kb+kc,ka+(kb+3)+kc,(sa.trans ab).trans bt,by omega,?_⟩
  refine ⟨ht.pc,ht.ret,ht.chains,ht.n4,ht.target,ht.height,ht.leaf,ht.selected,ht.tree,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ht.leftLo.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.leftHi.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.rightLo.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.rightHi.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact (ht.frame.get (A:=0x66010) (by decide) (by unfold ENC;decide)).trans bfloor
  · exact (ht.frame.get (A:=0x66000) (by decide) (by unfold ENC;decide)).trans bhints
  · exact (ht.regs.get (by decide)).trans b8
  · exact ((ar.trans br).trans ht.regs).mono (by simp)
  · exact ((af.trans bf).trans ht.frame).mono (by tauto)
#print axioms call_steps
end SigGolfCandidate.T3M.Sign.SharedLowerSetup


namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest Pieces chainCount height)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem prepared_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (hsetup : SetupCode im)
    (lay : Layer) (hl : lay≠0) (leaf : Nat) (p : PreparedLower) (digits : List Nat)
    (hd : ∀ j,j<43 → digits.getD j 0<8)
    (s : MachineState) (hp : s.pc=pcOf 22418) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits.getD j 0))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay.val j d) ((p.prefixes.getD j []).getD d 0))
    (ha : DigsAt s (sigBase lay.val+688) (preparedPieces lay leaf p digits).2) :
    ∃ t k,Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (sigBase lay.val) (preparedPieces lay leaf p digits).1 ∧
      DigsAt t (sigBase lay.val+688) (preparedPieces lay leaf p digits).2 ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => sigBase lay.val≤A ∧ A<sigBase lay.val+688) := by
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have hbound := lay.isLt
  obtain ⟨t,k,hs,hk,tp,tv,tr,tf⟩ := reveal_steps hc hbcode hsetup lay.val (by omega) (by omega)
    (fun j => digits.getD j 0) (fun j d => (p.prefixes.getD j []).getD d 0) hd s hp h8 hb hv
  refine ⟨t,k,hs,hk,tp,?_,?_,tr,tf⟩
  · have hcc : chainCount lay=43 := by fin_cases lay <;> simp_all [chainCount]
    simpa [preparedPieces,hcc] using tv
  · intro j hj
    have hj' : j<height lay := by simpa [preparedPieces] using hj
    have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
    exact (ha j hj).frame tf
      (by unfold sigBase;split_ifs <;> omega)
      (by intro h;omega)
      (by intro h;omega)
#print axioms prepared_steps
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_hooks : CanonicalHooks.Code Images.signImage := by
  constructor
  · constructor <;> apply codeAt_sign_current_slice <;> decide +kernel
  all_goals apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedSearchCode

namespace SigGolfCandidate.T3M.Sign.SharedControlTail
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_initResidual : CodeAt Images.signImage (pcOf 22226) initResidualCode := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_firstLayer : CodeAt Images.signImage (pcOf 22239) firstLayerCode := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_nextLayer : CodeAt Images.signImage (pcOf 22457) nextLayerCode := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_topProduce : CodeAt Images.signImage (pcOf 22478) topProduceCode := by
  apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedControlTail
namespace SigGolfCandidate.T3M.Sign.SharedLowerRegisters
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedLowerRegisters
namespace SigGolfCandidate.T3M.Sign.SharedLowerCopy
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : CodeAt Images.signImage (pcOf 22409) code := by
  apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedLowerCopy

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def code : List (BitVec 32) := bv_list% 32 [0xfffe37,0xe0e13,0x260e0ba3,0xff0fd06f]
sym_block block := symRun {noAlias:=true} code (pcOf 24661) 6

theorem steps {im : Image} (hc : CodeAt im (pcOf 24661) code)
    (s : MachineState) (hp : s.pc=pcOf 24661) (flag : Nat) (hf : CfTableOK flag s) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22100 ∧ CfTableOK 0 t ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=TOP_DATA+624) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [block.res,rv_simp]
  · intro i hi hj
    have old:=hf i hi hj
    rw [getByte_eq_word _ _ (by unfold TOP_DATA;omega)]
    rw [getByte_eq_word _ _ (by unfold TOP_DATA;omega)] at old
    interval_cases i <;> simp only [cfByte] at old ⊢ <;>
      simp [block.res,rv_simp,TOP_DATA] at old ⊢ <;> try exact old
    all_goals first
      | exact extractByte_replaceByte_same _ _ (by decide) _
      | rw [extractByte_replaceByte_diff _ _ _ (by decide) (by decide) (by decide)];exact old
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res];t3n []
    rw [if_neg (by unfold TOP_DATA at hn;omega)]
#print axioms steps
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : CodeAt Images.signImage (pcOf 24661) code := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_jump : CodeAt Images.signImage (pcOf 378) [0x36d1706f] := by
  apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem byte_result (s : MachineState) (A : Nat) (ha : A<2^64) :
    (block.res.toState s).getByte (BitVec.ofNat 64 A) =
      if A=TOP_DATA+631 then 0 else s.getByte (BitVec.ofNat 64 A) := by
  rw [getByte_eq_word _ _ ha,getByte_eq_word _ _ ha]
  simp only [Result.toState_getMem,block.res];t3n []
  rw [Nat.mod_eq_of_lt (show A/8*8<18446744073709551616 by omega)]
  by_cases he : A/8*8=16773744
  · rw [if_pos he]
    by_cases hf : A=TOP_DATA+631
    · rw [if_pos hf]
      subst A
      exact extractByte_replaceByte_same _ _ (by decide) _
    · rw [if_neg hf]
      have hm : A%8≠7 := by unfold TOP_DATA at hf;omega
      rw [extractByte_replaceByte_diff _ _ _ (Nat.mod_lt _ (by decide)) (by decide) hm]
      rw [show BitVec.ofNat 64 (A/8*8)=16773744#64 by rw [he]]
  · rw [if_neg he,if_neg (by unfold TOP_DATA;omega)]
#print axioms byte_result
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem tables_result (s : MachineState) (flag : Nat) (ht : TableOK s)
    (hf : CfTableOK flag s) (hr : Reward.RewardTablesOK s) :
    TableOK (block.res.toState s) ∧ CfTableOK 0 (block.res.toState s) ∧
      Reward.RewardTablesOK (block.res.toState s) := by
  constructor
  · intro i hi
    rw [byte_result _ _ (by unfold TOP_DATA;omega),if_neg (by omega)]
    exact ht i hi
  constructor
  · intro i hi hj
    rw [byte_result _ _ (by unfold TOP_DATA;omega)]
    by_cases h : i=631
    · subst i;simp [cfByte]
    · rw [if_neg (by omega),hf i hi hj]
      simp [cfByte,h]
  · intro i hi hj
    rw [byte_result _ _ (by unfold TOP_DATA;omega),if_neg (by omega)]
    exact hr i hi hj
#print axioms tables_result
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_kernel (P : Prop) (hP : P) : KernAt Images.signImage 543 P := by
  refine ⟨⟨?_,?_⟩,Or.inr rfl,?_,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  all_goals apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_searchKernel : KernAt Images.signImage 543 (CanonicalHooks.Code Images.signImage) :=
  installed_kernel _ installed_hooks
end SigGolfCandidate.T3M.Sign.SharedSearchCode

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

structure Tables (s : MachineState) : Prop where
  x5 : s.getReg .x5=0
  z40 : s.getMem (BitVec.ofNat 64 (ENC+40))=0
  table : TableOK s
  cf : CfTableOK 0 s
  reward : Reward.RewardTablesOK s
  zt : ZeroCap.ZtOK 543 s

def TableCells (A : Nat) : Prop := A=ENC+40 ∨ TOP_DATA≤A ∧ A<TOP_DATA+2944 ∨ 16691072≤A ∧ A<16691200

theorem Tables.frame {s t : MachineState} {W : Nat→Prop} {regs : List Reg}
    (h : Tables s) (hf : Frame s t W) (hr : RegsExcept s t regs) (h5 : .x5∉regs)
    (hw : ∀ A, TableCells A → ¬W A) : Tables t := by
  refine ⟨(hr.get h5).trans h.x5,?_,?_,?_,?_,?_⟩
  · exact (hf.get (by unfold ENC;decide) (hw _ (Or.inl rfl))).trans h.z40
  · exact h.table.frame hf (fun i hi => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.cf.frame hf (fun i hi hj => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.reward.frame hf (fun i hi hj => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.zt.frame hf (fun r hr => hw _ (Or.inr (Or.inr (by
      simp only [ZeroCap.ZT, if_neg (show (543:Nat) ≠ 354 by decide)]; omega))))

def topArgs (index : Nat) (pair : Digest×Digest) : Canonical.CsArgs :=
  ⟨0,(route index 0).2,(route index 0).1,.pair pair.1 pair.2,22208,19⟩

theorem top_pre (index : Nat) (hi : index<2^31) (pair : Digest×Digest)
    (s t : MachineState) (h : SharedTopSetup.Post index pair.1 pair.2 s t)
    (ht : Tables t) (hc : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    Canonical.CsPre 543 (topArgs index pair) t := by
  have hr : (route index 0).2=0 := T3.route_top_tree index hi
  have hl : (route index 0).1=index/2^19 := by
    change index/2^19%2^12=index/2^19
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨h.pc,h.ret,ht.x5,h.x8,?_,?_,h.x17,h.x26,h.x27,?_,?_,?_,Or.inl hr,
    h.left.1,h.left.2,hc,ht.z40,h.right.1,h.right.2,ht.table,ht.cf,ht.reward,ht.zt,
    by change 19<22;decide,by intro; rfl,?_⟩
  · simpa [topArgs,hr] using h.x9
  · simpa only [topArgs,hl] using h.x18
  · change (route index 0).2<2^32;rw [hr];decide
  · change (route index 0).1<2^32;rw [hl];omega
  · change (route index 0).2*2^12+(route index 0).1<2^32;rw [hr,hl];omega
  · intro hn;exact (hn rfl).elim

def lowerArgs (lay : Layer) (index floor : Nat) (pair : Digest×Digest) : Canonical.CsArgs :=
  ⟨lay,(route index lay).2,(route index lay).1,.pair pair.1 pair.2,22418,floor⟩

theorem lower_pre (lay : Layer) (hl : lay≠0) (index residual hints : Nat) (hi : index<2^31)
    (pair : Digest×Digest) (s t : MachineState) (h : SharedLowerSetup.CallPost lay.val index residual hints s t)
    (ht : Tables t) (hc : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hp0 : DigAt s (0x66040+32*lay.val) pair.1)
    (hp1 : DigAt s (0x66050+32*lay.val) pair.2)
    (hf : CanonicalPolicy.threshold lay.val residual<22) :
    Canonical.CsPre 543 (lowerArgs lay index (CanonicalPolicy.threshold lay.val residual) pair) t := by
  have htree : (route index lay).2<2^32 := by fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  have hleaf : (route index lay).1<2^32 := by fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  have hroute : (route index lay).2*2^height lay+(route index lay).1<2^32 := by
    fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  refine ⟨h.pc,h.ret,ht.x5,h.layer,?_,?_,?_,?_,?_,htree,hleaf,hroute,Or.inr ?_,
    h.leftLo.trans hp0.1,?_,hc,ht.z40,h.rightLo.trans hp1.1,?_,ht.table,ht.cf,ht.reward,ht.zt,hf,?_,?_⟩
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.tree
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.leaf
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.target
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.chains
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.n4
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.height
  · change t.getMem (BitVec.ofNat 64 (ENC+8))=pair.1.extractLsb' 64 64
    have he : 0x66048+32*lay.val=(0x66040+32*lay.val)+8 := by omega
    exact h.leftHi.trans (he ▸ hp0.2)
  · change t.getMem (BitVec.ofNat 64 (ENC+56))=pair.2.extractLsb' 64 64
    have he : 0x66058+32*lay.val=(0x66050+32*lay.val)+8 := by omega
    exact h.rightHi.trans (he ▸ hp1.2)
  · intro he;exact (hl he).elim
  · intro _;exact h.floor

theorem credit_small (lay : Layer) (low : Bool) (ds : List Nat) : CanonicalPolicy.credit lay low ds<2^32 := by
  have hword : wordCredit lay ds≤T3.chainCount lay := by
    simpa only [wordCredit,List.length_range] using List.length_filter_le (fun i => decide (ds.getD i 0+1=T3.maxDigit lay i)) (List.range (T3.chainCount lay))
  have hcopy : savedCopies lay ds≤T3.chainCount lay := by
    simpa only [savedCopies,List.length_range] using List.length_filter_le (fun i => decide (safeZeroCopy lay ds i)) (List.range (T3.chainCount lay))
  have hc : T3.chainCount lay≤54 := by fin_cases lay <;> decide
  have hb := CanonicalPolicy.pathBonus_le lay low
  unfold CanonicalPolicy.credit CanonicalPolicy.pathReward CanonicalPolicy.reward
  omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def ValueWrites (A : Nat) : Prop :=
  ∃ lay : Nat, 1≤lay ∧ lay≤3 ∧ SharedRootControl.sigBase lay≤A ∧ A<SharedRootControl.sigBase lay+688

def WorkWrites (A : Nat) : Prop :=
  (ENC≤A ∧ A<ENC+40) ∨ (ENC+48≤A ∧ A<ENC+64) ∨
  (EOUT≤A ∧ A<EOUT+32) ∨ (DIGITS≤A ∧ A<DIGITS+64) ∨
  (0x66000≤A ∧ A<0x66020 ∨ A=0x667F8) ∨ (0x66100≤A ∧ A<0x66138) ∨ ValueWrites A

theorem work_bound {A : Nat} (h : WorkWrites A) : A<0x66800 := by
  rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_table {A : Nat} (h : TableCells A) : ¬WorkWrites A := by
  rcases h with rfl|h
  · intro h
    rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
    all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
    unfold SharedRootControl.sigBase at hb he
    split_ifs at hb he <;> unfold ENC at * <;> omega
  · intro hw
    have := work_bound hw
    unfold TOP_DATA at h
    omega

theorem work_not_meta {A : Nat} (hl : 0x66040≤A) (hu : A<0x660c0) : ¬WorkWrites A := by
  intro h
  rcases h with h|h|h|h|h|h|⟨lay,hlay,ulay,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_index : ¬WorkWrites 0x20550 := by
  intro h
  rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_path (lay : Layer) (hl : lay≠0) (j half : Nat)
    (hj : j<height lay) (hh : half<2) :
    ¬WorkWrites (SharedRootControl.sigBase lay.val+688+16*j+8*half) := by
  intro h
  rcases h with h|h|h|h|h|h|⟨other,ho1,ho3,hlo,hhi⟩
  all_goals first
    | (fin_cases lay <;> simp_all [SharedRootControl.sigBase,height,ENC,EOUT,DIGITS] <;> omega)
    | skip
  interval_cases other <;> fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega

theorem stored_frame {s t : MachineState} (hf : Frame s t WorkWrites)
    (lay : Layer) (hl : lay≠0) (index : Nat) (p : PreparedLower)
    (h : SharedRootControl.Stored lay index p s) : SharedRootControl.Stored lay index p t := by
  have hln : 1≤lay.val := by have := lay.isLt;by_contra hh;apply hl;exact Fin.ext (by omega)
  have hlu : lay.val<4 := lay.isLt
  refine ⟨h.plen,?_,?_,?_,?_⟩
  · intro i hi k hk
    apply (h.saved i hi k hk).frame hf
    · unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer;omega
    · intro hw;have := work_bound hw
      unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer at this;omega
    · intro hw;have := work_bound hw
      unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer at this;omega
  · intro j hj
    have hj' : j<height lay := by simpa only [List.length_map,List.length_range] using hj
    apply (h.path j hj).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega
    · simpa only [Nat.mul_zero,Nat.add_zero] using work_not_path lay hl j 0 hj' (by decide)
    · simpa only [Nat.mul_one] using work_not_path lay hl j 1 hj' (by decide)
  · apply h.left.frame hf
    · unfold SharedRootControl.metaAddr;omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
  · apply h.right.frame hf
    · unfold SharedRootControl.metaAddr;omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega

structure Stable (index : Nat) (prepared : PreparedRoots) (forest : Digest×Digest) (s : MachineState) : Prop where
  tables : Tables s
  indexMem : s.getMem (0x20550#64)=BitVec.ofNat 64 index
  one : SharedRootControl.Stored 1 index prepared.one s
  two : SharedRootControl.Stored 2 index prepared.two s
  three : SharedRootControl.Stored 3 index prepared.three s
  forestL : DigAt s 0x660a0 forest.1
  forestR : DigAt s 0x660b0 forest.2

theorem Stable.frame {s t : MachineState} {index : Nat} {prepared : PreparedRoots} {forest : Digest×Digest}
    {regs : List Reg} (h : Stable index prepared forest s) (hf : Frame s t WorkWrites)
    (hr : RegsExcept s t regs) (h5 : .x5∉regs) : Stable index prepared forest t := by
  refine ⟨h.tables.frame hf hr h5 (fun _ => work_not_table),
    (hf.get (by decide) work_not_index).trans h.indexMem,
    stored_frame hf 1 (by decide) _ _ h.one,stored_frame hf 2 (by decide) _ _ h.two,
    stored_frame hf 3 (by decide) _ _ h.three,?_,?_⟩
  · exact h.forestL.frame hf (by decide) (work_not_meta (by decide) (by decide)) (work_not_meta (by decide) (by decide))
  · exact h.forestR.frame hf (by decide) (work_not_meta (by decide) (by decide)) (work_not_meta (by decide) (by decide))

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure TopTailSteps (im : Image) : Prop where
  save : ∀ s : MachineState, s.pc=pcOf 22208 →
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22226 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => 0x66100≤A ∧ A<0x66100+56)
  init : ∀ s : MachineState, s.pc=pcOf 22226 →
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22230 ∧ t.getMem (0x66008#64)=74 ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008)
  residual : ∀ s : MachineState, s.pc=pcOf 22230 → ∀ r c : Nat, r<2^32 → c<2^32 →
    s.getMem (0x66008#64)=BitVec.ofNat 64 r → s.getMem (0x66018#64)=BitVec.ofNat 64 c →
    ∃ t k,Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22239 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008)
  first : ∀ s : MachineState, s.pc=pcOf 22239 →
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22240 ∧ t.getReg .x8=1 ∧
      RegsExcept s t [.x8] ∧ Frame s t (fun _ => False)

def TopTailWrites (A : Nat) : Prop := (0x66100≤A ∧ A<0x66138) ∨ A=0x66008

theorem topTail_subset {A : Nat} (h : TopTailWrites A) : WorkWrites A := by
  rcases h with h|rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

structure TopTailPost (low : Bool) (ds : List Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual 74 0 low ds)
  saved : ∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))
  regs : RegsExcept s t [.x6,.x7,.x8,.x28,.x29]
  frame : Frame s t TopTailWrites

theorem top_tail {im : Image} (hc : TopTailSteps im)
    (s : MachineState) (hp : s.pc=pcOf 22208) (low : Bool) (ds : List Nat)
    (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds)) :
    ∃ t k,Steps im s k k t ∧ k≤31 ∧ TopTailPost low ds s t := by
  obtain ⟨a,sa,ap,asaved,ar,af⟩ := hc.save s hp
  obtain ⟨b,ab,bp,brm,br,bf⟩ := hc.init a ap
  have bcm : b.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds) :=
    (bf.get (by decide) (by decide)).trans ((af.get (by decide) (by omega)).trans hcm)
  obtain ⟨c,k,bc,hk,cp,crm,cr,cf⟩ := hc.residual b bp 74 (CanonicalPolicy.credit 0 low ds) (by decide) (credit_small _ _ _) brm bcm
  obtain ⟨t,ct,tp,t8,tr,tf⟩ := hc.first c cp
  refine ⟨t,18+4+k+1,((sa.trans ab).trans bc).trans ct,by omega,?_,t8,?_,?_,?_,?_⟩
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

theorem top_residual_small {low : Bool} {ds : List Nat} (h : 19≤CanonicalPolicy.credit 0 low ds) :
    CanonicalPolicy.nextResidual 74 0 low ds<56 := by
  unfold CanonicalPolicy.nextResidual;omega

theorem words_bytes {s t : MachineState} (A B n : Nat) (hA : A%8=0) (hB : B%8=0)
    (hs : A+8*n<2^64) (ht : B+8*n<2^64)
    (hw : ∀ i,i<n → t.getMem (BitVec.ofNat 64 (B+8*i))=s.getMem (BitVec.ofNat 64 (A+8*i)))
    (j : Nat) (hj : j<8*n) :
    t.getByte (BitVec.ofNat 64 (B+j))=s.getByte (BitVec.ofNat 64 (A+j)) := by
  rw [getByte_eq_word t (B+j) (by omega),getByte_eq_word s (A+j) (by omega)]
  have ha : (A+j)/8*8=A+8*(j/8) := by omega
  have hb : (B+j)/8*8=B+8*(j/8) := by omega
  rw [ha,hb,hw _ (by omega)]
  congr 1
  omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure LowerTailSteps (im : Image) : Prop where
  reveal : ∀ (lay : Layer), lay≠0 → ∀ (leaf : Nat) (p : PreparedLower) (ds : List Nat),
    (∀ j,j<43 → ds.getD j 0<8) → ∀ s : MachineState, s.pc=pcOf 22418 →
    s.getReg .x8=BitVec.ofNat 64 lay.val →
    (∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)) →
    (∀ j,j<43 → ∀ d,d<8 → DigAt s (ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer lay.val j d) ((p.prefixes.getD j []).getD d 0)) →
    DigsAt s (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2 →
    ∃ t k,Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay leaf p ds).1 ∧
      DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2 ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688)
  residual : ∀ s : MachineState, s.pc=pcOf 22448 → ∀ r c : Nat, r<2^32 → c<2^32 →
    s.getMem (0x66008#64)=BitVec.ofNat 64 r → s.getMem (0x66018#64)=BitVec.ofNat 64 c →
    ∃ t k,Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22457 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008)
  next : ∀ s : MachineState, s.pc=pcOf 22457 → ∀ lay : Nat, (1≤lay ∧ lay≤3) →
    s.getReg .x8=BitVec.ofNat 64 lay →
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22240 else pcOf 22460) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧ RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False)

def LowerTailWrites (lay : Layer) (A : Nat) : Prop :=
  (SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688) ∨ A=0x66008

theorem lowerTail_subset (lay : Layer) (hl : lay≠0) {A : Nat} (h : LowerTailWrites lay A) : WorkWrites A := by
  have hh := lay.isLt
  have hz : lay.val≠0 := fun h=>hl (Fin.ext h)
  rcases h with h|rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lay.val,by omega,by omega,h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

structure LowerTailPost (lay : Layer) (leaf residual : Nat) (p : PreparedLower) (low : Bool) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=(if lay.val<3 then pcOf 22240 else pcOf 22460)
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual residual lay low ds)
  values : DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay leaf p ds).1
  path : DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2
  regs : RegsExcept s t [.x6,.x7,.x8,.x21,.x22,.x23,.x24,.x28]
  frame : Frame s t (LowerTailWrites lay)

theorem lower_tail {im : Image} (hc : LowerTailSteps im)
    (lay : Layer) (hl : lay≠0) (leaf residual : Nat) (p : PreparedLower) (low : Bool) (ds : List Nat)
    (hd : ∀ j,j<43 → ds.getD j 0<8) (s : MachineState) (hp : s.pc=pcOf 22418)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer lay.val j d) ((p.prefixes.getD j []).getD d 0))
    (ha : DigsAt s (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2)
    (hr : residual<2^32) (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual)
    (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit lay low ds)) :
    ∃ t k,Steps im s k k t ∧ k≤587 ∧ LowerTailPost lay leaf residual p low ds s t := by
  have hln : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt;have : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  have hsbase : SharedRootControl.sigBase lay.val+1024<0x66000 := by unfold SharedRootControl.sigBase;split_ifs <;> omega
  obtain ⟨a,ka,sa,hka,ap,av,aa,ar,af⟩ := hc.reveal lay hl leaf p ds hd s hp h8 hb hv ha
  obtain ⟨b,kb,ab,hkb,bp,brm,br,bf⟩ := hc.residual a ap residual (CanonicalPolicy.credit lay low ds) hr (credit_small _ _ _)
    ((af.get (by decide) (by omega)).trans hrm) ((af.get (by decide) (by omega)).trans hcm)
  have b8 := (br.get (by decide : Reg.x8∉[.x6,.x7,.x28])).trans ((ar.get (by decide)).trans h8)
  obtain ⟨t,bt,tp,t8,tr,tf⟩ := hc.next b bp lay.val hln b8
  refine ⟨t,ka+kb+3,(sa.trans ab).trans bt,by omega,tp,t8,?_,?_,?_,?_,?_⟩
  · exact (tf.get (by decide) (by simp)).trans brm
  · intro j hj
    have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
    have hj' : j<43 := by simpa [preparedPieces,hcc] using hj
    apply (av j hj).frame (bf.trans tf)
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro h;rcases h with h|h;omega;exact h.elim
    · intro h;rcases h with h|h;omega;exact h.elim
  · intro j hj
    have hj' : j<height lay := by simpa [preparedPieces] using hj
    have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
    apply (aa j hj).frame (bf.trans tf)
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro h;rcases h with h|h;omega;exact h.elim
    · intro h;rcases h with h|h;omega;exact h.elim
  · exact ((ar.trans br).trans tr).mono (by simp)
  · exact ((af.trans bf).trans tf).mono (by
      intro A hA h;rcases h with (h|h)|h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def LowerWrites (lay : Layer) (A : Nat) : Prop :=
  (ENC≤A ∧ A<ENC+40) ∨ (ENC+48≤A ∧ A<ENC+64) ∨
  (EOUT≤A ∧ A<EOUT+32) ∨ (DIGITS≤A ∧ A<DIGITS+64) ∨
  (0x66000≤A ∧ A<0x66020 ∨ A=0x667F8) ∨ (SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688)

theorem lowerWrites_subset (lay : Layer) (hl : lay≠0) {A : Nat} (h : LowerWrites lay A) : WorkWrites A := by
  have hh := lay.isLt
  have hz : lay.val≠0 := fun h=>hl (Fin.ext h)
  rcases h with h|h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lay.val,by omega,by omega,h⟩)))))

theorem lowerWrites_saved (lay : Layer) (i : Nat) (hi : i<7) : ¬LowerWrites lay (0x66100+8*i) := by
  intro h
  rcases h with h|h|h|h|h|h
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at h;split_ifs at h <;> omega

theorem csWrites_subset {A : Nat} (h : Canonical.CsW A) : WorkWrites A := by
  unfold Canonical.CsW DigW CanonicalHooks.CreditW at h
  unfold WorkWrites
  simp only [Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG,ENC,EOUT,DIGITS] at *
  omega

theorem csWrites_lower (lay : Layer) {A : Nat} (h : Canonical.CsW A) : LowerWrites lay A := by
  unfold Canonical.CsW DigW CanonicalHooks.CreditW at h
  unfold LowerWrites
  simp only [Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG,ENC,EOUT,DIGITS] at *
  omega

theorem topSetupWrites_subset {A : Nat} (h : A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) : WorkWrites A := by
  unfold WorkWrites;omega

theorem lowerSetupWrites_subset (lay : Layer) {A : Nat}
    (h : A=0x66000 ∨ A=0x66010 ∨ A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) : LowerWrites lay A := by
  unfold LowerWrites;omega

def SavedTop (ds : List Nat) (t : MachineState) : Prop :=
  ∃ s : MachineState,
    (∀ j,j<54 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)) ∧
    (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i)))

theorem SavedTop.frame {ds : List Nat} {s t : MachineState} {W : Nat→Prop}
    (h : SavedTop ds s) (hf : Frame s t W) (hw : ∀ i,i<7 → ¬W (0x66100+8*i)) : SavedTop ds t := by
  obtain ⟨u,hu,hmem⟩ := h
  exact ⟨u,hu,fun i hi=>(hf.get (by omega) (hw i hi)).trans (hmem i hi)⟩

theorem SavedTop.restore {ds : List Nat} {s t : MachineState} (h : SavedTop ds s)
    (hw : ∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) :
    ∀ j,j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0) := by
  obtain ⟨u,hu,hmem⟩ := h
  intro j hj
  exact (words_bytes DIGITS DIGITS 7 (by unfold DIGITS;decide) (by unfold DIGITS;decide)
    (by unfold DIGITS;decide) (by unfold DIGITS;decide) (fun i hi=>(hw i hi).trans (hmem i hi)) j (by omega)).trans (hu j hj)

theorem lower_decode_digits (lay : Layer) (hl : lay≠0) {ds : List Nat}
    (hd : ∃ v,CanonicalPolicy.decode lay v=some ds) : ∀ j,j<43 → ds.getD j 0<8 := by
  obtain ⟨v,hv⟩ := hd
  have he : CanonicalPolicy.normalLayer lay=1 := by simp [CanonicalPolicy.normalLayer,hl]
  change T3.decode (CanonicalPolicy.normalLayer lay) v=some ds at hv
  rw [he] at hv
  intro j hj
  have hb := T3.decode_digit_max hv j (by simpa [T3.chainCount] using hj)
  simpa [T3.maxDigit] using Nat.lt_succ_of_le hb

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure FinishSteps (im : Image) : Prop where
  restore : ∀ s : MachineState,s.pc=pcOf 22460 →
    ∃ t,Steps im s 18 18 t ∧ t.pc=pcOf 22478 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56)
  produce : ∀ s : MachineState,s.pc=pcOf 22478 → ∀ index : Nat,index<2^31 →
    s.getMem (0x20550#64)=BitVec.ofNat 64 index →
    ∃ t,Steps im s 12 12 t ∧ SharedControlTail.TopPost index s t

structure Finished (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (ds : List Nat)
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
  digits : ∀ j,j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56)

theorem finish_steps {im : Image} (hc : FinishSteps im) (index : Nat) (hi : index<2^31)
    (p : PreparedRoots) (forest : Digest×Digest) (ds : List Nat) (s : MachineState)
    (hp : s.pc=pcOf 22460) (hstable : Stable index p forest s) (hsaved : SavedTop ds s)
    (hsum : (s.getReg .x25).toNat≤201) :
    ∃ t,Steps im s 30 30 t ∧ Finished index p forest ds s t := by
  obtain ⟨a,sa,ap,acopy,ar,af⟩ := hc.restore s hp
  have haf : Frame s a WorkWrites := af.mono (by intro A hA h;unfold WorkWrites;omega)
  have hsta : Stable index p forest a := hstable.frame haf ar (by decide)
  obtain ⟨t,at',ht⟩ := hc.produce a ap index hi hsta.indexMem
  have hstt : Stable index p forest t := hsta.frame (ht.frame.mono (by simp)) ht.regs (by decide)
  refine ⟨t,sa.trans at',ht.pc,ht.layer,ht.tree,ht.height,ht.chains,ht.n4,ht.target,ht.leaf,ht.selected,hstt,?_,?_,?_⟩
  · intro j hj
    rw [ht.frame.getByte (by unfold DIGITS;omega) (by simp)]
    exact hsaved.restore acopy j hj
  · rw [ht.regs.get (by decide),ar.get (by decide)];exact hsum
  · exact (af.trans ht.frame).mono (by tauto)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure SearchCalls (im : Image) (sk : BitVec 256) : Prop where
  call : ∀ (A : Canonical.CsArgs) (s : MachineState), Canonical.CsPre 543 A s →
    TBSim im sk s (Canonical.csCost A.lay)
      (CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (searchLimit A.lay))
      (Canonical.CsPost im 543 A s)

structure TopSetupSteps (im : Image) : Prop where
  setup : ∀ s : MachineState, s.pc=pcOf 22182 → ∀ index : Nat,index<2^31 →
    s.getMem 0x20550=BitVec.ofNat 64 index → ∀ left right : Digest,
    DigAt s 0x66040 left → DigAt s 0x66050 right →
    ∃ t,Steps im s 26 26 t ∧ SharedTopSetup.Post index left right s t

structure TopReady (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (low : Bool) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual 74 0 low ds)
  small : CanonicalPolicy.nextResidual 74 0 low ds<56
  hints : t.getMem (0x66000#64)=0
  c32 : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some ds
  length : ds.length=54
  saved : SavedTop ds t
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t WorkWrites

def SearchError (im : Image) (t : MachineState) : Prop :=
  t.pc=pcOf 545 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)

def TopStagePost (im : Image) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option (BitVec 32×List Nat×Bool)→MachineState→Prop
  | none,t => SearchError im t
  | some (_,ds,low),t => TopReady index p forest low ds s t

theorem top_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : TopSetupSteps im) (htailSteps : TopTailSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost 0+57)
      (CanonicalPolicy.layerCounterSearchAt 0 19 (route index 0).2 (route index 0).1
        (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im index p forest s) := by
  obtain ⟨a,sa,ha⟩ := ht.setup s hp index hi hstable.indexMem _ _ hstable.one.left hstable.one.right
  have haf : Frame s a WorkWrites := ha.frame.mono (fun _ _=>topSetupWrites_subset)
  have hsta : Stable index p forest a := hstable.frame haf ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold ENC;omega) (by unfold ENC;omega)).trans hcv⟩
  have H := hs.call (topArgs index (topPair 1 p.one.levels)) a (top_pre index hi _ s a ha hsta.tables hac)
  have Htail : TBSim im sk a (Canonical.csCost 0+31)
      (CanonicalPolicy.layerCounterSearchAt 0 19 (route index 0).2 (route index 0).1
        (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im index p forest s) := by
    have hb := TBSim.bind H (f:=fun r=>pure r) (W₂:=31) (Q₂:=TopStagePost im index p forest s) (by
      intro r u hu
      cases r with
      | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=TopStagePost im index p forest s) hu).mono (by omega) (fun _ _ h=>h)
      | some pair =>
        obtain ⟨c,ds,low⟩ := pair
        rcases hu with ⟨up,hc,uc19,uc32,hdec,hlen,hdigs,ur,uf,usum,ucredit,hfloor⟩
        have huf : Frame a u WorkWrites := uf.mono (fun _ _=>csWrites_subset)
        have hstu : Stable index p forest u := hsta.frame huf ur (by decide)
        obtain ⟨t,k,ut,hk,htail⟩ := top_tail htailSteps u up low ds ucredit
        have htf : Frame u t WorkWrites := htail.frame.mono (fun _ _=>topTail_subset)
        have hstt : Stable index p forest t := hstu.frame htf htail.regs (by decide)
        refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
        refine ⟨htail.pc,htail.layer,htail.residual,top_residual_small hfloor,?_,?_,hstt,hdec,hlen,⟨u,hdigs,htail.saved⟩,?_,?_⟩
        · exact (htail.frame.get (by decide) (by unfold TopTailWrites;omega)).trans
            ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans
              ((ha.frame.get (by decide) (by unfold ENC;omega)).trans hh))
        · exact ⟨c.toNat,by omega,
            (htail.frame.get (by unfold ENC;omega) (by unfold TopTailWrites ENC;omega)).trans uc32⟩
        · rw [htail.regs.get (by decide)]
          change (u.getReg .x25).toNat≤201
          change (u.getReg .x25).toNat≤146 at usum
          omega
        · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
    simpa only [bind_pure,topArgs,lowerArgs] using hb
  exact (TBSim.steps sa Htail).mono (by omega) (fun _ _ h=>h)

end SigGolfCandidate.T3M.Sign.SharedSearches
